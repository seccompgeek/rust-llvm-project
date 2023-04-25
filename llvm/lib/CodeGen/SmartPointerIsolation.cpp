#include "/root/rust/src/llvm-project/llvm/lib/CodeGen/SafeStackLayout.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/Local.h"
#include <cassert>
#include <string>
#include <vector>

#define DEBUG_TYPE "rust-meta"
#define GET_EXTERN_STACK_PTR "__get_extern_stack_ptr"

using namespace llvm;

namespace
{
	class ExternStack
	{
		Function &F;
		const DataLayout &DL;

		Type *StackPtrTy; //void pointer type
		Type *IntPtrTy; //integer type which has same bit size to ptr type (i.e. i64) 
		Type *Int32Ty;
		Type *Int8Ty;

		Value *ExternStackPtr = nullptr; // extern stack pointer wrapper

		enum
		{
			StackAlignment = 16
		};
		
		uint64_t getStaticAllocaAllocationSize(AllocaInst *AI);

	public:

		ExternStack(Function &F, const DataLayout &DL)
			: F(F), DL(DL),
			  StackPtrTy(Type::getInt8PtrTy(F.getContext())),
			  IntPtrTy(DL.getIntPtrType(F.getContext())),
			  Int32Ty(Type::getInt32Ty(F.getContext())),
			  Int8Ty(Type::getInt8Ty(F.getContext())) {}

		Value *moveStaticAllocasToExternStack(IRBuilder<> &IRB, Function &F,
											  ArrayRef<AllocaInst *> StaticAllocas,
											  Instruction *BasePtr);
		
		void moveDynamicAllocasToExternStack(Function &F, Value *ExternStackPtr,
											 AllocaInst *DynamicTop,
											 ArrayRef<AllocaInst *> DynamicAllocas);
		AllocaInst *
		createStackRestorePoints(IRBuilder<> &IRB, Function &F,
								 ArrayRef<Instruction *> StackRestorePoints,
								 Value *StaticTop, bool NeedDynamicTop);

		void run(ArrayRef<AllocaInst *> StaticAllocas, ArrayRef<ReturnInst *> Returns);
		/*void run(ArrayRef<AllocaInst *> StaticAllocas,
				 ArrayRef<AllocaInst *> DynamicAllocas,
				 ArrayRef<Instruction *> StackRestorePoints, ArrayRef<ReturnInst *>);*/
	};
} // namespace

// byte of type * number of element (if it is not array like, the number of element is 1.)
uint64_t ExternStack::getStaticAllocaAllocationSize(AllocaInst *AI)
{
	uint64_t Size = DL.getTypeAllocSize(AI->getAllocatedType());
	auto C = dyn_cast<ConstantInt>(AI->getArraySize());
	//if (!C) return 0;
	Size *= C->getZExtValue();
	return Size;
}

void ExternStack::moveDynamicAllocasToExternStack(
	Function &F, Value *ExternStackPtr, AllocaInst *DynamicTop,
	ArrayRef<AllocaInst *> DynamicAllocas)
{
	errs() << "Moving dynamic allocas\n";
	DIBuilder DIB(*F.getParent());
	for (AllocaInst *AI : DynamicAllocas)
	{
		errs() << *AI << "\n";
		IRBuilder<> IRB(AI);
		Value *ArraySize = AI->getArraySize();
		if (ArraySize->getType() != IntPtrTy)
			ArraySize = IRB.CreateIntCast(ArraySize, IntPtrTy, false);

		Type *Ty = AI->getAllocatedType();
		u_int64_t TySize = DL.getTypeAllocSize(Ty);
		Value *Size = IRB.CreateMul(ArraySize, ConstantInt::get(IntPtrTy, TySize));
		Value *SP = IRB.CreatePtrToInt(IRB.CreateLoad(StackPtrTy, ExternStackPtr),
									   IntPtrTy);
		SP = IRB.CreateSub(SP, Size);

		unsigned Align = std::max(
			std::max((unsigned)DL.getPrefTypeAlignment(Ty), (unsigned)AI->getAlign().value()),
			(unsigned)StackAlignment);

		assert(isPowerOf2_32(Align));
		Value *NewTop = IRB.CreateIntToPtr(
			IRB.CreateAnd(SP, ConstantInt::get(IntPtrTy, ~u_int64_t(Align - 1))),
			StackPtrTy);
		IRB.CreateStore(NewTop, ExternStackPtr);
		if (DynamicTop)
			IRB.CreateStore(NewTop, DynamicTop);

		Value *NewAI = IRB.CreatePointerCast(NewTop, AI->getType());
		if (AI->hasName() && isa<Instruction>(NewAI))
			NewAI->takeName(AI);

		replaceDbgDeclare(AI, NewAI, DIB, DIExpression::ApplyOffset, 0);
		AI->replaceAllUsesWith(NewAI);
		AI->eraseFromParent();
	}

	if (!DynamicAllocas.empty())
	{
		for (inst_iterator It = inst_begin(&F), Ie = inst_end(&F); It != Ie;)
		{
			Instruction *I = &*(It++);
			auto II = dyn_cast<IntrinsicInst>(I);
			if (!II)
				continue;

			if (II->getIntrinsicID() == Intrinsic::stacksave)
			{
				IRBuilder<> IRB(II);
				Instruction *LI = IRB.CreateLoad(StackPtrTy, ExternStackPtr);
				LI->takeName(II);
				II->replaceAllUsesWith(LI);
				II->eraseFromParent();
			}
			else if (II->getIntrinsicID() == Intrinsic::stackrestore)
			{
				IRBuilder<> IRB(II);
				Instruction *SI = IRB.CreateStore(II->getArgOperand(0), ExternStackPtr);
				SI->takeName(II);
				assert(II->use_empty());
				II->eraseFromParent();
			}
		}
	}

	errs() << "Moved dynamic allocas\n";
}

AllocaInst *ExternStack::createStackRestorePoints(
	IRBuilder<> &IRB, Function &F, ArrayRef<Instruction *> StackRestorePoints,
	Value *StaticTop, bool NeedDynamicTop)
{
	assert(StaticTop && "The stack top isn't set.");

	if (StackRestorePoints.empty())
		return nullptr;

	// We need the current value of the shadow stack pointer to restore
	// after longjmp or exception catching.

	// FIXME: On some platforms this could be handled by the longjmp/exception
	// runtime itself.

	AllocaInst *DynamicTop = nullptr;
	if (NeedDynamicTop)
	{
		// If we also have dynamic alloca's, the stack pointer value changes
		// throughout the function. For now we store it in an alloca.
		DynamicTop = IRB.CreateAlloca(StackPtrTy, /*ArraySize=*/nullptr,
									  "unsafe_stack_dynamic_ptr");
		IRB.CreateStore(StaticTop, DynamicTop);
	}

	// Restore current stack pointer after longjmp/exception catch.
	for (Instruction *I : StackRestorePoints)
	{

		IRB.SetInsertPoint(I->getNextNode());
		Value *CurrentTop =
			DynamicTop ? IRB.CreateLoad(StackPtrTy, DynamicTop) : StaticTop;
		IRB.CreateStore(CurrentTop, ExternStackPtr);
	}

	return DynamicTop;
}


Value *ExternStack::moveStaticAllocasToExternStack(
	IRBuilder<> &IRB, Function &F, ArrayRef<AllocaInst *> StaticAllocas,
	Instruction *BasePtr)
{
	if (StaticAllocas.empty())
		return BasePtr;

	errs() << "Moving static allocas\n";
	DIBuilder DIB(*F.getParent());

	// I don't think this part is need
	StackLifetime SSC(F, StaticAllocas, StackLifetime::LivenessType::May);
	for (auto *I : SSC.getMarkers())
	{
		auto *Op = dyn_cast<Instruction>(I->getOperand(1));
		const_cast<IntrinsicInst *>(I)->eraseFromParent();
		if (Op && Op->use_empty())
			Op->eraseFromParent();
	}
	///

	static const StackLifetime::LiveRange NoColoringRange(1, true);

	Align stackAlignment(StackAlignment); // Integer to Align instance
	safestack::StackLayout SSL(stackAlignment);
	for (AllocaInst *AI : StaticAllocas)
	{
		Type *Ty = AI->getAllocatedType();
		u_int64_t Size = getStaticAllocaAllocationSize(AI);
		assert(Size !=0 && "Size should be bigger than 0");
		//if (Size == 0) Size = 1;


		unsigned intAlign =
			std::max((unsigned)DL.getPrefTypeAlignment(Ty), (unsigned)AI->getAlign().value());
		Align alignment(intAlign);
		SSL.addObject(AI, Size, alignment, NoColoringRange);
	}

	SSL.computeLayout();
	unsigned FrameAlignment = SSL.getFrameAlignment().value();

	if (FrameAlignment > StackAlignment)
	{
		assert(isPowerOf2_32(FrameAlignment));
		IRB.SetInsertPoint(BasePtr->getNextNode());

		// WARNNING : I think this realign alignment for extern stack pointer when alignment changed. but i don't know.
		BasePtr = cast<Instruction>(IRB.CreateIntToPtr(
			IRB.CreateAnd(
				IRB.CreatePtrToInt(BasePtr, IntPtrTy),
				ConstantInt::get(IntPtrTy, ~u_int64_t(FrameAlignment - 1))),
			StackPtrTy));
	}

	//IRB.SetInsertPoint(BasePtr->getNextNode());

	for (AllocaInst *AI : StaticAllocas)
	{
		errs() << *AI << "\n";
		IRB.SetInsertPoint(AI);
		unsigned Offset = SSL.getObjectOffset(AI);

		// dbg
		outs() << "move static alloca -- offset : " << Offset << "\n";
		//dgb

		replaceDbgDeclare(AI, BasePtr, DIB, DIExpression::ApplyOffset, -Offset);
		replaceDbgValueForAlloca(AI, BasePtr, DIB, -Offset);

		int i = 0;
		
		std::string Name = std::string(AI->getName()) + ".rsp_extern";
		while (!AI->use_empty())
		{
			i++;

			Use &U = *AI->use_begin();
			Instruction *User = cast<Instruction>(U.getUser());
			outs() << i << ". user : " << *User << "\n"; //dbg
			
			Instruction *InsertBefore;
			if (auto *PHI = dyn_cast<PHINode>(User)){
				outs() << "find Phi node\n"; //dbg
				InsertBefore = PHI->getIncomingBlock(U)->getTerminator();
				}
			else
				InsertBefore = User;

			// WARNNING : need to one more see!!!
			// this part means that before every user, insert gep instruction to get the extern SP, 
			// but I think this may generate overhead
			IRBuilder<> IRBUser(InsertBefore);
			Value *Off = IRBUser.CreateGEP(Int8Ty, BasePtr,
										   ConstantInt::get(Int32Ty, -Offset));
			Value *Replacement = IRBUser.CreateBitCast(Off, AI->getType(), Name);
			outs() << "   Replacement : " << *Replacement << "\n"; //dbg

			// TODO : need one more see!!!!
			// a little confused
			if (auto *PHI = dyn_cast<PHINode>(User))
				PHI->setIncomingValueForBlock(PHI->getIncomingBlock(U), Replacement);
			else
				U.set(Replacement); 
			
			Instruction *user2 = cast<Instruction>(U.getUser()); //dbg
			outs() << "   user : " << *user2 << "\n\n";  //dbg
		}
		AI->eraseFromParent();
	}

	unsigned FrameSize = alignTo(SSL.getFrameSize(), StackAlignment);
	IRB.SetInsertPoint(BasePtr->getNextNode());

	Value *StaticTop =
		IRB.CreateGEP(Int8Ty, BasePtr, ConstantInt::get(Int32Ty, -FrameSize),
					  "extern_stack_top");
	IRB.CreateStore(StaticTop, ExternStackPtr); // This part doesn't need when using static alloca isolation only.
	errs() << "Moved static allocas\n";
	return StaticTop;
}


void ExternStack::run(ArrayRef<AllocaInst *> StaticAllocas, ArrayRef<ReturnInst *> Returns)
{
	IRBuilder<> IRB(&F.front(), F.begin()->getFirstInsertionPt());
	/*
	if (DISubprogram *SP = F.getSubprogram())
		IRB.SetCurrentDebugLocation(DebugLoc::get(SP->getScopeLine(), 0, SP));
	*/
	std::vector<Type *> arg_type;
	std::vector<Value *> args;
	LLVMContext &C = F.getContext();
	Type* voidType = Type::getInt8PtrTy(F.getContext());


	FunctionCallee Fn = F.getParent()->getOrInsertFunction(GET_EXTERN_STACK_PTR, StackPtrTy);
	Value* ExternStakcPointer= IRB.CreateCall(Fn);
	Type *int8Ptr = Type::getInt8PtrTy(C);
	this->ExternStackPtr = IRB.CreateAlloca(int8Ptr);
	IRB.CreateStore(ExternStakcPointer, ExternStackPtr);
	
	/*MDNode *N = MDNode::get(C, {MDString::get(C, "r15")});
	arg_type.push_back(Type::getInt64Ty(C));
	Function *readRegisterFunc = Intrinsic::getDeclaration(
		F.getParent(), Intrinsic::read_register, arg_type);
	args.push_back(MetadataAsValue::get(C, N));
	Value *savedStackPtr = IRB.CreateCall(readRegisterFunc, args);

	Type *int8Ptr = Type::getInt8PtrTy(C);
	Value *intToPtr = IRB.CreateIntToPtr(savedStackPtr, int8Ptr);
	this->ExternStackPtr = IRB.CreateAlloca(int8Ptr);
	IRB.CreateStore(intToPtr, ExternStackPtr);*/

	/// BasePtr : external stack pointer
	/// ExternStackPtr : BasePtr wrapper
	Instruction *BasePtr =
		IRB.CreateLoad(StackPtrTy, ExternStackPtr, false, "extern_stack_ptr");


	/*
	Type *int64Ptr = Type::getInt64PtrTy(C);
	Value *intToPtr = IRB.CreateIntToPtr(savedStackPtr, int64Ptr);
	intToPtr = IRB.CreateBitCast(intToPtr, int64Ptr->getPointerTo(0));
	this->ExternStackPtr =
		IRB.CreateBitCast(intToPtr, StackPtrTy->getPointerTo(0));
	Instruction *BasePtr =
		IRB.CreateLoad(StackPtrTy, ExternStackPtr, false, "extern_stack_ptr");
	assert(BasePtr->getType() == StackPtrTy);
	*/

	Value *StaticTop =
		moveStaticAllocasToExternStack(IRB, F, StaticAllocas, BasePtr);
	
	IRB.SetInsertPoint(cast<Instruction>(StaticTop)->getNextNode());
	FunctionCallee Fn_StackTop = F.getParent()->getOrInsertFunction("register_2_memory", StackPtrTy, voidType);
	args.push_back(StaticTop);
	IRB.CreateCall(Fn_StackTop, args);
	
	/*
	AllocaInst *DynamicTop = createStackRestorePoints(
		IRB, F, StackRestorePoints, StaticTop, !DynamicAllocas.empty());

	moveDynamicAllocasToExternStack(F, ExternStackPtr, DynamicTop,
									DynamicAllocas);
	*/


		

	/*
	IRB.SetInsertPoint(cast<Instruction>(StaticTop)->getNextNode());
	args.clear();
	Function *writeRegisterFunc = Intrinsic::getDeclaration(
		F.getParent(), Intrinsic::write_register, arg_type);

	Value *ptrToIntInst = IRB.CreatePtrToInt(StaticTop, Type::getInt64Ty(C));

	args.push_back(MetadataAsValue::get(C, N));
	args.push_back(ptrToIntInst);
	IRB.CreateCall(writeRegisterFunc, args);
	*/

	
	
	for (ReturnInst *RI : Returns)
	{
		IRB.SetInsertPoint(RI);
		IRB.CreateStore(BasePtr, ExternStackPtr);
		FunctionCallee Fn_Restore = F.getParent()->getOrInsertFunction("register_2_memory", StackPtrTy, voidType);
		args.clear();
		args.push_back(BasePtr);
		IRB.CreateCall(Fn_Restore, args);
	}
	
}



//--------------------------------pass definition--------------------------------//

class RustSmartPointerIsolationPass : public FunctionPass
{
public:
	static char ID;
	RustSmartPointerIsolationPass() : FunctionPass(ID)
	{
		//initializeRutsMetaIsolationPass(*PassRegistry::getPassRegistry());
		//domain = nullptr;
	}

	void getAnalysisUsage(AnalysisUsage &AU) const override
	{
		AU.setPreservesAll();
	}

	bool runOnFunction(Function &) override;

private:
	Function *createFunction(std::string, FunctionType *, Module *);
	//MpkDomain *domain;
	ExternStack *externStack;
};

Function *RustSmartPointerIsolationPass::createFunction(std::string name,
												FunctionType *type, Module *M)
{
	FunctionCallee callee = M->getOrInsertFunction(name, type);
	return dyn_cast<Function>(callee.getCallee());
}

bool RustSmartPointerIsolationPass::runOnFunction(Function &F)
{
	//if (!llvm::shouldHookWithMpkIsolation() || F.isDeclaration())
	//	return false;
	if(F.isDeclaration()){
		outs() << "this function is declaration\n";
		return false;
	}

	auto *DL = &F.getParent()->getDataLayout();
	if (!DL) report_fatal_error("Data Layout is required");
	externStack = new ExternStack(F, *DL);


	// --------------------domain----------------------//
	/*
	if (!domain)
	{
		// initialize domain
		domain = new MpkDomain();
		FunctionType *voidType =
			FunctionType::get(Type::getVoidTy(currContext), {}, false);
		FunctionType *ptrRetVoidArgType =
			FunctionType::get(Type::getInt64PtrTy(currContext), {}, false);
		FunctionType *void2IntArgType = FunctionType::get(
			Type::getVoidTy(currContext),
			{Type::getInt8Ty(currContext), Type::getInt8Ty(currContext)}, false);
		domain->setSFIExceptionFunc(
			createFunction(SFI_EXCEPTION_FUNC_NAME, voidType, currModule));
		domain->setCountAllocasFunc(
			createFunction(COUNT_ALLOCA_FUNC_NAME, void2IntArgType, currModule));
	}
	*/
	//-------------------------------------------------//

	SmallVector<AllocaInst *, 4> StaticArrayAllocas;
	SmallVector<AllocaInst *, 4> DynamicArrayAllocas;
	SmallVector<Instruction *, 8> StackRestorePoints;
	SmallVector<ReturnInst *, 4> Returns;
	
	bool foundMovable = false;
	if (F.getName() == "main")
	{
		auto II = F.begin()->begin();
		Instruction *inst = &(*II);
		IRBuilder<> IRB(inst);
		Type *StackPtrTy = Type::getInt8PtrTy(F.getContext());

		/*FunctionCallee Fn = F.getParent()->getOrInsertFunction(
			GET_DOMAIN_FUNC_NAME, StackPtrTy->getPointerTo(0));*/
		FunctionCallee Fn = F.getParent()->getOrInsertFunction(
			GET_EXTERN_STACK_PTR, StackPtrTy);
		Value *ExternStackPtr = IRB.CreateCall(Fn);

		std::vector<Type *> arg_type;
		std::vector<Value *> args;
		LLVMContext &C = F.getContext();
		MDNode *N = MDNode::get(C, {MDString::get(C, "r15")});
		arg_type.push_back(Type::getInt64Ty(C));
		Function *writeRegisterFunc = Intrinsic::getDeclaration(
			F.getParent(), Intrinsic::write_register, arg_type);

		Value *ptrToIntInst = IRB.CreatePtrToInt(ExternStackPtr, Type::getInt64Ty(C));

		args.push_back(MetadataAsValue::get(C, N));
		args.push_back(ptrToIntInst);

		IRB.CreateCall(writeRegisterFunc, args);
		return true;
	}

	//size_t totalAllocas = 0;
	//size_t totalUnsafeAllocas = 0;
	for (BasicBlock &BB : F)
	{
		for (Instruction &I : BB)
		{
			if (auto CI = dyn_cast<CallInst>(&I))
			{
				if (CI->getCalledFunction() && CI->canReturnTwice())
				{
					StackRestorePoints.push_back(CI);
				}
			}

			else if (auto LPI = dyn_cast<LandingPadInst>(&I))
			{
				StackRestorePoints.push_back(LPI);
			}

			else if (auto AI = dyn_cast<AllocaInst>(&I))
			{
				if (AI->hasMetadata("RustMeta-Smart-Pointer"))
				{
					if (AI->isStaticAlloca())
					{
						// WARNNING : I think find() function isn't need.
						if (std::find(StaticArrayAllocas.begin(), StaticArrayAllocas.end(),
									  AI) == StaticArrayAllocas.end())
						{
							StaticArrayAllocas.push_back(AI);
							foundMovable = true;
						}
					}
					else
					{
						assert(AI->isStaticAlloca() && "Dynamic Alloca inst is not yet implemented");
						/*
						if (std::find(DynamicArrayAllocas.begin(),
									  DynamicArrayAllocas.end(),
									  AI) == DynamicArrayAllocas.end())
						{
							DynamicArrayAllocas.push_back(AI);
							foundMovable = true;
						}
						*/
					}
					//totalUnsafeAllocas++;
				}
				//totalAllocas++;
			}


			// WARNNING : is this need?
			else if (auto RI = dyn_cast<ReturnInst>(&I))
			{
				Returns.push_back(RI);
			}
			/*
			// WARNNING : I think this is not need to rustmeta
			else if (isa<StoreInst>(&I) || isa<LoadInst>(&I))
			{

				if (I.getMetadata("MPK-Unsafe") != nullptr)
				{
					if (auto SI = llvm::dyn_cast<StoreInst>(&I))
					{
						applySFICast(SI);
					}
					// applyFalsePositiveCheck(&I);
				}
				else
				{
					// applyFalseNegativeCheck(&I);
				}
			}
			//
			*/
		}
	}

	if (foundMovable)
	{
		externStack->run(StaticArrayAllocas, Returns);
	}
	return foundMovable;
}

char RustSmartPointerIsolationPass::ID = 0;
static RegisterPass<RustSmartPointerIsolationPass> X("rust-smart-pointer-isolation", "Rust Smart Pointer Isolation Pass");


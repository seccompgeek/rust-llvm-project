#include "SafeStackLayout.h"
#include "llvm/CodeGen/SmartPointerIsolation.h"
#include "llvm/InitializePasses.h"
#include "llvm/CodeGen/Passes.h"
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
#include "llvm/PassRegistry.h"
#include "llvm/PassRegistry.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/InlineAsm.h"

#include <cassert>
#include <string>
#include <vector>

#define DEBUG_TYPE "rust-meta"


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
			StackAlignment = 8
		};
		
		uint64_t getStaticAllocaAllocationSize(AllocaInst *AI);

	public:

		ExternStack(Function &F, const DataLayout &DL)
			: F(F), DL(DL),
			  StackPtrTy(Type::getInt8PtrTy(F.getContext())),
			  IntPtrTy(DL.getIntPtrType(F.getContext())),
			  Int32Ty(Type::getInt32Ty(F.getContext())),
			  Int8Ty(Type::getInt8Ty(F.getContext())) {}

		Value *moveHousedSmartPtrsToExternStack(IRBuilder<> &IRB, Function &F, 
												ArrayRef<AllocaInst *> HousedSmartPointers,
												Instruction *BasePtr);	

		Value *moveStaticAllocasToExternStack(IRBuilder<> &IRB, Function &F,
											  ArrayRef<AllocaInst *> StaticAllocas,
											  Instruction *BasePtr);

		void run(ArrayRef<AllocaInst *> StaticAllocas, 
				 ArrayRef<AllocaInst *> HousedSmaartPointers,
				 ArrayRef<ReturnInst *> Returns);
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


Value *ExternStack::moveStaticAllocasToExternStack(
	IRBuilder<> &IRB, Function &F, ArrayRef<AllocaInst *> StaticAllocas,
	Instruction *BasePtr)
{
	if (StaticAllocas.empty())
		return BasePtr;

	// errs() << "Moving static allocas\n";
	DIBuilder DIB(*F.getParent());

	StackLifetime SSC(F, StaticAllocas, StackLifetime::LivenessType::May);
	for (auto *I : SSC.getMarkers())
	{
		auto *Op = dyn_cast<Instruction>(I->getOperand(1));
		const_cast<IntrinsicInst *>(I)->eraseFromParent();
		if (Op && Op->use_empty())
			Op->eraseFromParent();
	}

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

		BasePtr = cast<Instruction>(IRB.CreateIntToPtr(
			IRB.CreateAnd(
				IRB.CreatePtrToInt(BasePtr, IntPtrTy),
				ConstantInt::get(IntPtrTy, ~u_int64_t(FrameAlignment - 1))),
			StackPtrTy));
	}

	//IRB.SetInsertPoint(BasePtr->getNextNode());

	for (AllocaInst *AI : StaticAllocas)
	{
		//errs() << *AI << "\n";
		IRB.SetInsertPoint(AI);
		unsigned Offset = SSL.getObjectOffset(AI);

		// dbg
		// outs() << "move static alloca -- offset : " << Offset << "\n";
		//dgb

		replaceDbgDeclare(AI, BasePtr, DIB, DIExpression::ApplyOffset, -Offset);
		replaceDbgValueForAlloca(AI, BasePtr, DIB, -Offset);

		// int i = 0;
		
		std::string Name = std::string(AI->getName()) + ".rsp_extern";
		while (!AI->use_empty())
		{
			// i++;

			Use &U = *AI->use_begin();
			Instruction *User = cast<Instruction>(U.getUser());
			// outs() << i << ". user : " << *User << "\n"; //dbg
			
			Instruction *InsertBefore;
			if (auto *PHI = dyn_cast<PHINode>(User)){
				// outs() << "find Phi node\n"; //dbg
				InsertBefore = PHI->getIncomingBlock(U)->getTerminator();
				}
			else
				InsertBefore = User;

			IRBuilder<> IRBUser(InsertBefore);
			Value *Off = IRBUser.CreateGEP(Int8Ty, BasePtr,
										   ConstantInt::get(Int32Ty, -Offset));
			Value *Replacement = IRBUser.CreateBitCast(Off, AI->getType(), Name);
			// outs() << "   Replacement : " << *Replacement << "\n"; //dbg

			if (auto *PHI = dyn_cast<PHINode>(User))
				PHI->setIncomingValueForBlock(PHI->getIncomingBlock(U), Replacement);
			else
				U.set(Replacement); 
			
			// Instruction *user2 = cast<Instruction>(U.getUser()); //dbg
			// outs() << "   user : " << *user2 << "\n\n";  //dbg
		}
		AI->eraseFromParent();
	}

	unsigned FrameSize = alignTo(SSL.getFrameSize(), StackAlignment);
	IRB.SetInsertPoint(BasePtr->getNextNode());

	Value *StaticTop =
		IRB.CreateGEP(Int8Ty, BasePtr, ConstantInt::get(Int32Ty, -FrameSize),
					  "extern_stack_pure_top");
	// IRB.CreateStore(StaticTop, ExternStackPtr);
	// errs() << "Moved static allocas\n";
	return StaticTop;
}

Value *ExternStack::moveHousedSmartPtrsToExternStack(
	IRBuilder<> &IRB, Function &F, ArrayRef<AllocaInst *> HousedSmartPointers,
	Instruction *BasePtr)
{
	if (HousedSmartPointers.empty())
		return BasePtr;

	//errs() << "Moving housed allocas\n";
	DIBuilder DIB(*F.getParent());

	StackLifetime SSC(F, HousedSmartPointers, StackLifetime::LivenessType::May);
	for (auto *I : SSC.getMarkers())
	{
		auto *Op = dyn_cast<Instruction>(I->getOperand(1));
		const_cast<IntrinsicInst *>(I)->eraseFromParent();
		if (Op && Op->use_empty())
			Op->eraseFromParent();
	}

	static const StackLifetime::LiveRange NoColoringRange(1, true);

	Align stackAlignment(StackAlignment); // Integer to Align instance
	safestack::StackLayout SSL(stackAlignment);
	for (AllocaInst *AI : HousedSmartPointers)
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

	for (AllocaInst *AI : HousedSmartPointers)
	{
		//errs() << *AI << "\n";
		IRB.SetInsertPoint(AI);
		unsigned Offset = SSL.getObjectOffset(AI);

		// dbg
		// outs() << "move housed smart pointer -- offset : " << Offset << "\n";
		// dgb

		replaceDbgDeclare(AI, BasePtr, DIB, DIExpression::ApplyOffset, -Offset);
		replaceDbgValueForAlloca(AI, BasePtr, DIB, -Offset);

		//int i = 0;
		
		std::string Name = std::string(AI->getName()) + ".rsp_extern";
		while (!AI->use_empty())
		{
			//i++;

			Use &U = *AI->use_begin();
			Instruction *User = cast<Instruction>(U.getUser());
			// outs() << i << ". user : " << *User << "\n"; //dbg
			
			Instruction *InsertBefore;
			if (auto *PHI = dyn_cast<PHINode>(User)){
				// outs() << "find Phi node\n"; //dbg
				InsertBefore = PHI->getIncomingBlock(U)->getTerminator();
				}
			else
				InsertBefore = User;

			// WARNNING : need to one more see!!!
			// this part means that before every user, insert gep instruction to get the extern SP
			IRBuilder<> IRBUser(InsertBefore);
			Value *Off = IRBUser.CreateGEP(Int8Ty, BasePtr,
										   ConstantInt::get(Int32Ty, -Offset));
			Value *Replacement = IRBUser.CreateBitCast(Off, AI->getType(), Name);
			// outs() << "   Replacement : " << *Replacement << "\n"; //dbg

			// TODO : need one more see!!!!
			// a little confused
			if (auto *PHI = dyn_cast<PHINode>(User))
				PHI->setIncomingValueForBlock(PHI->getIncomingBlock(U), Replacement);
			else
				U.set(Replacement); 
			
			//Instruction *user2 = cast<Instruction>(U.getUser()); //dbg
			//outs() << "   user : " << *user2 << "\n\n";  //dbg
		}
		AI->eraseFromParent();
	}

	unsigned FrameSize = alignTo(SSL.getFrameSize(), StackAlignment);
	IRB.SetInsertPoint(BasePtr->getNextNode());

	Value *StaticTop =
		IRB.CreateGEP(Int8Ty, BasePtr, ConstantInt::get(Int32Ty, -FrameSize),
					  "extern_stack_housed_top");
	// IRB.CreateStore(StaticTop, ExternStackPtr);
	// errs() << "Moved static allocas\n";
	return StaticTop;
}

void ExternStack::run(ArrayRef<AllocaInst *> StaticAllocas, ArrayRef<AllocaInst *> HousedSmartPointers, ArrayRef<ReturnInst *> Returns)
{
	IRBuilder<> IRB(&F.front(), F.begin()->getFirstInsertionPt());
	IRBuilder<> IRB2(&F.front(), F.begin()->getFirstInsertionPt());
	/*
	if (DISubprogram *SP = F.getSubprogram())
		IRB.SetCurrentDebugLocation(DebugLoc::get(SP->getScopeLine(), 0, SP));
	*/
	if(StaticAllocas.empty() && HousedSmartPointers.empty()){
		return;
	}
	
	LLVMContext &C = F.getContext();

///
	std::vector<Value *> args;

	StringRef asmCode = "movq %fs:${1:c}, $0";
	StringRef constraints = "=r,i,~{dirflag},~{fpsr},~{flags}";

	InlineAsm* inlineAsm = InlineAsm::get(
       	FunctionType::get(Type::getInt64Ty(C), {Type::getInt32Ty(C)}, false),
       	asmCode, constraints, false, false, InlineAsm::AD_ATT);

	//args.push_back(ptrToIntInst);
	args.push_back(ConstantInt::get(Type::getInt32Ty(C), 56));
		
	CallInst *FS2MEM = IRB.CreateCall(inlineAsm, args);
	FS2MEM->addAttributeAtIndex(AttributeList::FunctionIndex, Attribute::NoUnwind);
	
	// WARNNING 
	FS2MEM->addAttributeAtIndex(AttributeList::FunctionIndex, Attribute::ReadNone);
	// WARNNING 

	Value *ExternStackPointer = IRB.CreateIntToPtr(FS2MEM, Type::getInt64PtrTy(C));
	//FunctionCallee Fn = F.getParent()->getOrInsertFunction("FS2MEM", StackPtrTy);
	//Value* ExternStackPointer= IRB.CreateCall(Fn);
///

	Type *int64Ptr = Type::getInt64PtrTy(C);
	ExternStackPointer = IRB.CreateBitCast(ExternStackPointer, int64Ptr->getPointerTo(0));
	this->ExternStackPtr =
    	IRB.CreateBitCast(ExternStackPointer, StackPtrTy->getPointerTo(0));
	
	Instruction *BasePtr;
	Value *PureTop;

	if(!StaticAllocas.empty()){
		BasePtr = IRB.CreateLoad(StackPtrTy, ExternStackPtr, false, "extern_stack_ptr_pure");

		PureTop = moveStaticAllocasToExternStack(IRB, F, StaticAllocas, BasePtr);
	
		IRB.SetInsertPoint(cast<Instruction>(PureTop)->getNextNode());
		IRB.CreateStore(PureTop, ExternStackPtr);
	}

	Instruction *temp;
	Instruction *HousedBasePtr;
	Value *HousedTop;	

	if(!HousedSmartPointers.empty()){	
		temp = cast<Instruction>(IRB2.CreateGEP(Type::getInt8Ty(C), ExternStackPtr, ConstantInt::get(Int32Ty, 8)));
		HousedBasePtr = IRB2.CreateLoad(StackPtrTy, temp, false, "extern_stack_ptr_housed"); 

		HousedTop = moveHousedSmartPtrsToExternStack(IRB2, F, HousedSmartPointers, HousedBasePtr);

		IRB2.SetInsertPoint(cast<Instruction>(HousedTop)->getNextNode());
		IRB2.CreateStore(HousedTop, temp);
	}	

	for (ReturnInst *RI : Returns)
	{
		IRB.SetInsertPoint(RI);
		if(!StaticAllocas.empty()){
			IRB.CreateStore(BasePtr, ExternStackPtr);
		}
		if(!HousedSmartPointers.empty()){
			IRB.CreateStore(HousedBasePtr, temp);
		}
		//FunctionCallee Fn_Restore = F.getParent()->getOrInsertFunction("register_2_memory", StackPtrTy, voidPtrType);
		/*FunctionCallee Fn_Restore =	F.getParent()->getOrInsertFunction("MEM2GS", Type::getVoidTy(F.getContext()), StackPtrTy);
		args.clear();
		args.push_back(BasePtr);
		IRB.CreateCall(Fn_Restore, args);*/
	}
	
}



//--------------------------------pass definition--------------------------------//

class RustSmartPointerIsolationPass : public FunctionPass
{
public:
	static char ID;
	RustSmartPointerIsolationPass() : FunctionPass(ID)
	{
		initializeRustSmartPointerIsolationPassPass(*PassRegistry::getPassRegistry());
	}

	void getAnalysisUsage(AnalysisUsage &AU) const override
	{
		AU.setPreservesAll();
	}

	bool runOnFunction(Function &) override;

private:
	ExternStack *externStack;
};

bool RustSmartPointerIsolationPass::runOnFunction(Function &F)
{
	if(F.isDeclaration()){
		// outs() << "this function is declaration\n";
		return false;
	}

	LLVMContext &C = F.getContext();

	auto *DL = &F.getParent()->getDataLayout();
	if (!DL) report_fatal_error("Data Layout is required");
	externStack = new ExternStack(F, *DL);

	SmallVector<AllocaInst *, 4> StaticArrayAllocas;
	SmallVector<AllocaInst *, 4> HousedSmartPoninters;	
	SmallVector<ReturnInst *, 4> Returns;
	
	bool foundMovable = false;
	if (F.getName() == "main")
	{
		auto II = F.begin()->begin();
		Instruction *inst = &(*II);
		IRBuilder<> IRB(inst);
		Type *StackPtrTy = Type::getInt8PtrTy(C);
		Type *int64Ty = Type::getInt64Ty(C);
		Type *int32Ty = Type::getInt32Ty(C);

		FunctionCallee Fn = F.getParent()->getOrInsertFunction(
			"__get_wrapper", StackPtrTy);
		Value *ExternStackPtr = IRB.CreateCall(Fn);

		/*std::vector<Type *> arg_type;
		std::vector<Value *> args;
		LLVMContext &C = F.getContext();
		MDNode *N = MDNode::get(C, {MDString::get(C, "r15")});
		arg_type.push_back(Type::getInt64Ty(C));
		Function *writeRegisterFunc = Intrinsic::getDeclaration(
			F.getParent(), Intrinsic::write_register, arg_type);

		Value *ptrToIntInst = IRB.CreatePtrToInt(ExternStackPtr, Type::getInt64Ty(C));

		args.push_back(MetadataAsValue::get(C, N));
		args.push_back(ptrToIntInst);

		IRB.CreateCall(writeRegisterFunc, args);*/
		
		std::vector<Value *> args;

		StringRef asmCode = "movq $0, %fs:${1:c}";
		StringRef constraints = "r,i,~{dirflag},~{fpsr},~{flags}";

		InlineAsm* inlineAsm = InlineAsm::get(
        	FunctionType::get(Type::getVoidTy(C), {Type::getInt64Ty(C), Type::getInt32Ty(C)}, false),
        	asmCode, constraints, true, false, InlineAsm::AD_ATT);

		Value *ptrToIntInst = IRB.CreatePtrToInt(ExternStackPtr, int64Ty);
		args.push_back(ptrToIntInst);
		args.push_back(ConstantInt::get(int32Ty, 56));
		

		CallInst *MEM2FS = IRB.CreateCall(inlineAsm, args);
		MEM2FS->addAttributeAtIndex(AttributeList::FunctionIndex, Attribute::NoUnwind);


		/*FunctionCallee MEM2GS = F.getParent()->getOrInsertFunction(
			"MEM2FS", Type::getVoidTy(F.getContext()), StackPtrTy);
		std::vector<Value *> args;
		args.push_back(ExternStackPtr);
		IRB.CreateCall(MEM2GS, args);	
		*/
		return true;
	}

	for (BasicBlock &BB : F)
	{
		for (Instruction &I : BB)
		{
			if (auto CI = dyn_cast<CallInst>(&I))
			{
				if (CI->getCalledFunction() && CI->canReturnTwice())
				{
					//StackRestorePoints.push_back(CI);
				}
			}

			else if (auto LPI = dyn_cast<LandingPadInst>(&I))
			{
				//StackRestorePoints.push_back(LPI);
			}

			else if (auto AI = dyn_cast<AllocaInst>(&I))
			{
				if (AI->hasMetadata("RustMeta-Smart-Pointer"))
				{
					if (AI->isStaticAlloca())
					{
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

				}
				else 
				{
					if (AI->isStaticAlloca())
					{
						// WARNNING : I think find() function isn't need.
						if (std::find(HousedSmartPoninters.begin(), HousedSmartPoninters.end(),
									  AI) == HousedSmartPoninters.end())
						{
							HousedSmartPoninters.push_back(AI);
							foundMovable = true;
						}
					}
					else{
						assert(AI->isStaticAlloca() && "Dynamic Alloca inst is not yet implemented");	
					}
				}
			}

			else if (auto RI = dyn_cast<ReturnInst>(&I))
			{
				Returns.push_back(RI);
			}
		}
	}

	if (foundMovable)
	{
		std::reverse(StaticArrayAllocas.begin(), StaticArrayAllocas.end());
		std::reverse(HousedSmartPoninters.begin(), HousedSmartPoninters.end());
		std::reverse(Returns.begin(), Returns.end());
		externStack->run(StaticArrayAllocas, HousedSmartPoninters, Returns);
	}
	return foundMovable;
}

char RustSmartPointerIsolationPass::ID = 0;

INITIALIZE_PASS(RustSmartPointerIsolationPass, "rust-smart-pointer-isolation", "Rust Smart Pointer Isolation Pass", false, false)

FunctionPass *llvm::createRustSmartPointerIsolationPass() {
	return new RustSmartPointerIsolationPass();
}

/*static llvm::cl::opt<bool>
RustSmartPtrPassOpt("rust-smart-pointer-isolation",
          cl::desc("Rust Smart Pointer Isolation Pass"),
          cl::init(false));*/


PreservedAnalyses RSPIPass::run(Function &F, FunctionAnalysisManager &AM) {
	createRustSmartPointerIsolationPass()->runOnFunction(F);
	return PreservedAnalyses::all();
}

//static RegisterPass<RustSmartPointerIsolationPass> X("rust-smart-pointer-isolation", "Rust Smart Pointer Isolation Pass");

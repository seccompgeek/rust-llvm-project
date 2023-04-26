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

		void run(ArrayRef<AllocaInst *> StaticAllocas, ArrayRef<ReturnInst *> Returns);
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

	errs() << "Moving static allocas\n";
	DIBuilder DIB(*F.getParent());

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

			IRBuilder<> IRBUser(InsertBefore);
			Value *Off = IRBUser.CreateGEP(Int8Ty, BasePtr,
										   ConstantInt::get(Int32Ty, -Offset));
			Value *Replacement = IRBUser.CreateBitCast(Off, AI->getType(), Name);
			outs() << "   Replacement : " << *Replacement << "\n"; //dbg

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
	IRB.CreateStore(StaticTop, ExternStackPtr);
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
	
	Instruction *BasePtr =
		IRB.CreateLoad(StackPtrTy, ExternStackPtr, false, "extern_stack_ptr");

	Value *StaticTop =
		moveStaticAllocasToExternStack(IRB, F, StaticAllocas, BasePtr);
	
	IRB.SetInsertPoint(cast<Instruction>(StaticTop)->getNextNode());
	FunctionCallee Fn_StackTop = F.getParent()->getOrInsertFunction("register_2_memory", StackPtrTy, voidType);
	args.push_back(StaticTop);
	IRB.CreateCall(Fn_StackTop, args);
	
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
		outs() << "this function is declaration\n";
		return false;
	}

	auto *DL = &F.getParent()->getDataLayout();
	if (!DL) report_fatal_error("Data Layout is required");
	externStack = new ExternStack(F, *DL);

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
			}

			else if (auto RI = dyn_cast<ReturnInst>(&I))
			{
				Returns.push_back(RI);
			}
		}
	}

	if (foundMovable)
	{
		externStack->run(StaticArrayAllocas, Returns);
	}
	return foundMovable;
}

char RustSmartPointerIsolationPass::ID = 0;
INITIALIZE_PASS(RustSmartPointerIsolationPass, "rust-smart-pointer-isolation", "Rust Smart Pointer Isolation Pass", false, false)

FunctionPass *llvm::createRustSmartPointerIsolationPass() {
  return new RustSmartPointerIsolationPass();
}

PreservedAnalyses RSPIPass::run(Function &F, FunctionAnalysisManager &AM) {
  return PreservedAnalyses::all();
}

//static RegisterPass<RustSmartPointerIsolationPass> X("rust-smart-pointer-isolation", "Rust Smart Pointer Isolation Pass");


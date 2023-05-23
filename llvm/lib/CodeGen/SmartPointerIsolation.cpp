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

		Value *PureExternStackPtr = nullptr;
		Value *HousedExternStackPtr = nullptr;

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

		
		Value *moveStaticAllocasToExternStack(IRBuilder<> &IRB, Function &F,
											  ArrayRef<AllocaInst *> StaticAllocas,
											  Instruction *BasePtr, Value *ExternStackPtr,
											  bool isPure);
		
		void moveDynamicAllocasToExternStack(Function &F, Value *ExternStackPtr,
											 AllocaInst *DynamicTop,
											 ArrayRef<AllocaInst *> DynamicAllocas);
		AllocaInst *
		createStackRestorePoints(IRBuilder<> &IRB, Function &F,
								 ArrayRef<Instruction *> StackRestorePoints,
								 Value *StaticTop, Value *ExternStackPtr, bool NeedDynamicTop,
								 bool isPure);

		void run(ArrayRef<AllocaInst *> StaticAllocas,
				 ArrayRef<AllocaInst *> DynamicAllocas,
				 ArrayRef<Instruction *> StackRestorePoints, 
				 ArrayRef<ReturnInst *> Returns,
				 bool isPure);
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
	//errs() << "Moving dynamic allocas\n";
	DIBuilder DIB(*F.getParent());

	for (AllocaInst *AI : DynamicAllocas)
	{
		//errs() << *AI << "\n";
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

		unsigned intAlign = std::max(
			std::max((unsigned)DL.getPrefTypeAlignment(Ty), (unsigned)AI->getAlign().value()),
			(unsigned)StackAlignment);

		assert(isPowerOf2_32(intAlign));
		Value *NewTop = IRB.CreateIntToPtr(
			IRB.CreateAnd(SP, ConstantInt::get(IntPtrTy, ~u_int64_t(intAlign - 1))),
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
	//errs() << "Moved dynamic allocas\n";
}


AllocaInst *ExternStack::createStackRestorePoints(
	IRBuilder<> &IRB, Function &F, ArrayRef<Instruction *> StackRestorePoints,
	Value *StaticTop, Value *ExternStackPtr, bool NeedDynamicTop, bool isPure)
{
	assert(StaticTop && "The stack top isn't set.");

	if (StackRestorePoints.empty())
		return nullptr;
	
	const char *name;
	if(isPure){
		name= "dynamic_pure_ptr";
	}
	else{
		name = "dynamic_housed_ptr";
	}

	AllocaInst *DynamicTop = nullptr;
	if (NeedDynamicTop)
	{
		DynamicTop = IRB.CreateAlloca(StackPtrTy, /*ArraySize=*/nullptr,
									  name);
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
	Instruction *BasePtr, Value *ExternStackPtr, bool isPure)
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
		//assert(Size !=0 && "Size should be bigger than 0");
		if (Size == 0) Size = 1;

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
		IRB.SetInsertPoint(AI);
		unsigned Offset = SSL.getObjectOffset(AI);

		replaceDbgDeclare(AI, BasePtr, DIB, DIExpression::ApplyOffset, -Offset);
		replaceDbgValueForAlloca(AI, BasePtr, DIB, -Offset);

		std::string Name = std::string(AI->getName()) + ".rsp_extern";
		while (!AI->use_empty())
		{

			Use &U = *AI->use_begin();
			Instruction *User = cast<Instruction>(U.getUser());

			Instruction *InsertBefore;
			if (auto *PHI = dyn_cast<PHINode>(User))
				InsertBefore = PHI->getIncomingBlock(U)->getTerminator();
			else
				InsertBefore = User;

			IRBuilder<> IRBUser(InsertBefore);
			Value *Off = IRBUser.CreateGEP(Int8Ty, BasePtr,
										   ConstantInt::get(Int32Ty, -Offset));
			Value *Replacement = IRBUser.CreateBitCast(Off, AI->getType(), Name);

			if (auto *PHI = dyn_cast<PHINode>(User))
				PHI->setIncomingValueForBlock(PHI->getIncomingBlock(U), Replacement);
			else
				U.set(Replacement); 
		}
		AI->eraseFromParent();
	}
	unsigned FrameSize = alignTo(SSL.getFrameSize(), StackAlignment);
	
	const char *name;
	if(isPure){
		name= "extern_stack_pure_top";
	}
	else{
		name = "extern_stack_housed_top";	
	}

	IRB.SetInsertPoint(BasePtr->getNextNode());
	Value *StaticTop =
		IRB.CreateGEP(Int8Ty, BasePtr, ConstantInt::get(Int32Ty, -FrameSize),
					  name);
	IRB.CreateStore(StaticTop, ExternStackPtr);
	// errs() << "Moved static allocas\n";
	return StaticTop;
}

void ExternStack::run(ArrayRef<AllocaInst *> StaticAllocas,
						 ArrayRef<AllocaInst *> DynamicAllocas,
						 ArrayRef<Instruction *> StackRestorePoints,
						 ArrayRef<ReturnInst *> Returns,
						 bool isPure)
{
	IRBuilder<> IRB(&F.front(), F.begin()->getFirstInsertionPt());
	/*
	if (DISubprogram *SP = F.getSubprogram())
		IRB.SetCurrentDebugLocation(DebugLoc::get(SP->getScopeLine(), 0, SP));
	*/
	if(StaticAllocas.empty()){
		return;
	}
	Value **ExternStackPtr;
	const char *name;
	
	if(isPure){
		ExternStackPtr = &(this->PureExternStackPtr);
		name= "extern_stack_pure_ptr";
	}
	else{
		ExternStackPtr = &(this->HousedExternStackPtr);
		name = "extern_stack_housed_ptr";	
	}
	
	LLVMContext &C = F.getContext();
	std::vector<Value *> args;

	StringRef asmCode = "movq %fs:${1:c}, $0";
	StringRef constraints = "=r,i,~{dirflag},~{fpsr},~{flags}";
	InlineAsm* inlineAsm = InlineAsm::get(
       	FunctionType::get(Type::getInt64Ty(C), {Type::getInt32Ty(C)}, false),
       	asmCode, constraints, false, false, InlineAsm::AD_ATT);

	args.push_back(ConstantInt::get(Type::getInt32Ty(C), 56));		
	CallInst *FS2MEM = IRB.CreateCall(inlineAsm, args);
	FS2MEM->addAttributeAtIndex(AttributeList::FunctionIndex, Attribute::NoUnwind);	
	// WARNNING 
	FS2MEM->addAttributeAtIndex(AttributeList::FunctionIndex, Attribute::ReadNone);
	// WARNNING 

	Value *ExternStackPointer = IRB.CreateIntToPtr(FS2MEM, Type::getInt64PtrTy(C));

	Type *int64Ptr = Type::getInt64PtrTy(C);
	ExternStackPointer = IRB.CreateIntToPtr(ExternStackPointer, int64Ptr);
	ExternStackPointer = IRB.CreateBitCast(ExternStackPointer, int64Ptr->getPointerTo(0));

	*ExternStackPtr =
		IRB.CreateBitCast(ExternStackPointer, StackPtrTy->getPointerTo(0));
	if(!isPure){
		*ExternStackPtr = cast<Instruction>(IRB.CreateGEP(Type::getInt8Ty(C), *ExternStackPtr, ConstantInt::get(Int32Ty, 8)));		
	}
	
	Instruction *BasePtr = IRB.CreateLoad(StackPtrTy, *ExternStackPtr, false, name);
	Value *StaticTop = moveStaticAllocasToExternStack(IRB, F, StaticAllocas, BasePtr, *ExternStackPtr, isPure);
	//IRB.SetInsertPoint(cast<Instruction>(PureTop)->getNextNode());
	//IRB.CreateStore(StaticTop, PureExternStackPtr);
	AllocaInst *DynamicTop = createStackRestorePoints(
		IRB, F, StackRestorePoints, StaticTop, *ExternStackPtr,!DynamicAllocas.empty(), isPure);

	moveDynamicAllocasToExternStack(F, *ExternStackPtr, DynamicTop,
									DynamicAllocas);

	for (ReturnInst *RI : Returns)
	{
		IRB.SetInsertPoint(RI);
		IRB.CreateStore(BasePtr, *ExternStackPtr);
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
	SmallVector<AllocaInst *, 4> DynamicArrayAllocas;
	SmallVector<AllocaInst *, 4> StaticHousedAllocas;
	SmallVector<AllocaInst *, 4> DynamicHousedAllocas;
	SmallVector<Instruction *, 8> StackRestorePoints;
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
				if (AI->hasMetadata("RustMeta-Smart-Pointer") || AI->hasMetadata("RustMeta-Smart-Pointer-House"))
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
						if (std::find(DynamicArrayAllocas.begin(),
									  DynamicArrayAllocas.end(),
									  AI) == DynamicArrayAllocas.end())
						{
							DynamicArrayAllocas.push_back(AI);
							foundMovable = true;
						}
					}
				}
				/*else if (AI->hasMetadata("RustMeta-Smart-Pointer"))
				{
					if (AI->isStaticAlloca())
					{
						if (std::find(StaticHousedAllocas.begin(), StaticHousedAllocas.end(),
									  AI) == StaticHousedAllocas.end())
						{
							StaticHousedAllocas.push_back(AI);
							foundMovable = true;
						}
					}
					else
					{
						if (std::find(DynamicHousedAllocas.begin(),
									  DynamicHousedAllocas.end(),
									  AI) == DynamicHousedAllocas.end())
						{
							DynamicHousedAllocas.push_back(AI);
							foundMovable = true;
						}
					}	
				}*/
			}

			else if (auto RI = dyn_cast<ReturnInst>(&I))
			{
				Returns.push_back(RI);
			}
		}
	}

	if (foundMovable)
	{
		externStack->run(StaticArrayAllocas, DynamicArrayAllocas,
						 StackRestorePoints, Returns, true);
		externStack->run(StaticHousedAllocas, DynamicHousedAllocas,
						 StackRestorePoints, Returns, false);
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

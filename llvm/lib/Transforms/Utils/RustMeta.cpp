#include "llvm/Transforms/RustMeta.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Dominators.h"
#include <map>
#include <vector>

using namespace llvm;

std::string MetaUpdateSMAPIPass::typeToString(Type* type){
  std::string str;
  llvm::raw_string_ostream rso(str);
  type->print(rso);
  return rso.str();
}

PreservedAnalyses MetaUpdateSMAPIPass::run(Function& Func,
                                               FunctionAnalysisManager &AM) {

  /*Find special types housed in normal structs and insert new structs to replace them
  auto structTypes = M.getIdentifiedStructTypes();
  auto specialTypeMetadata = M.getNamedMetadata("SpecialTypes");
  std::map<StructType*, StructType*> specialTypeHousedStructsMap;
  std::map<StructType*, std::map<int, int>> specialTypeFieldRemap;
  std::set<StructType*> specialTypes;
  for(auto MDIt: specialTypeMetadata->operands()){
    auto MDValue = cast<MDString>(MDIt)->getString();
    for(auto type: structTypes){
      if (type->getStructName().equals(MDValue)){
        specialTypes.insert(type);
      }
    }
  }

  for(auto type: structTypes){
    if (specialTypes.find(type) == specialTypes.end()){
      auto totalFields = type->getStructNumElements();
      SmallVector<Type*> specialFields;
      SmallVector<int> FieldIndices;
      for(int i=0; i<totalFields; i++){
        auto fieldType = type->getStructElementType(i);
        if(auto structFieldType = dyn_cast<StructType>(fieldType)){
          if(specialTypes.find(structFieldType) != specialTypes.end()){
            specialFields.push_back(fieldType);
            FieldIndices.push_back(i);
          }
        }
      }

      if(specialFields.size() != 0){//TODO: if all fields are special, make this a special type as well as an optimization
        StructType* newType = StructType::create(specialFields);
        newType->setName(type->getStructName().str()+".safe");
        specialTypeHousedStructsMap.insert(std::make_pair(type, newType));
        specialTypeFieldRemap.insert(std::make_pair(type, std::map<int, int>()));
        int counter = 0;
        for(auto i: FieldIndices){
          specialTypeFieldRemap[type].insert(std::make_pair(i, counter++));
        }
      }
    }
  }

  auto checkIsZeroIdxGep = [&specialTypeFieldRemap](Type* type) {
    if(auto structType = dyn_cast<StructType>(type)){
      return specialTypeFieldRemap.find(structType) != specialTypeFieldRemap.end() && specialTypeFieldRemap[structType].find(0) != specialTypeFieldRemap[structType].end();
    }else {
      return false;
    }
  };

  for (auto &Func: M){
    if (Func.isDeclaration()) continue;
    std::map<Instruction*, Instruction*> housingPtrToSafePtrMap;
    for(auto &Inst: Func) {
      if(auto memInst = dyn_cast<MemTransferInst>(&Inst)){
        auto source = memInst->getSource();
        auto dest = memInst->getDest();
        auto len = memInst->getLength();
      }
    }
  }*/

  if(Func.isDeclaration()) return PreservedAnalyses::all();

    std::map<Instruction*, size_t> candidateCallSites;
    std::set<Instruction*> externFuncCalls;
    std::set<Instruction*> unnecessaryStores;
    std::map<uint64_t, uint64_t> optimizedIndices;

    std::map<Value*, std::set<Instruction*>> SmartPtr2ShadowMap;
    std::set<Instruction*> SmartPtrProjections;

    bool TDIAnalysis = !Func.getMetadata("SmartPointerAPIFunc");

    Instruction* getTDISlotInsertPoint = nullptr;
    bool Allocas = true;
    for(auto &BB: Func){
      for (auto &Inst: BB){
        if(Allocas && !isa<AllocaInst>(&Inst)){
          Allocas = false;
          getTDISlotInsertPoint = &Inst;
        }

        if(TDIAnalysis){
          if(auto call = dyn_cast<CallBase>(&Inst)){
            if(auto SMMD = call->getMetadata("ExchangeMallocCall")){
              auto TypeID = cast<MDString>(SMMD->getOperand(0))->getString();
              if(TypeID.equals("0")){
                candidateCallSites.insert(std::make_pair(&Inst, 1));
              }else{
                auto it = TypeMetadataToTDIIndexMap.find(TypeID);
                size_t TDIIndex = -1;
                if(it == TypeMetadataToTDIIndexMap.end()){
                  TDIIndex = TypeMetadataToTDIIndexMap.size() + 2; //0 is for FFIs, 1 is for smart pointers
                  TypeMetadataToTDIIndexMap.insert(std::make_pair(TypeID, TDIIndex));
                }else{
                  TDIIndex = it->second;
                }
                candidateCallSites.insert(std::make_pair(&Inst, TDIIndex));
              }
            }else if(auto F = call->getCalledFunction()){
              if(F->getMetadata("ExternFunc")){
                externFuncCalls.insert(call);
              }
            }
          }
        }
        
        if (auto store = dyn_cast<StoreInst>(&Inst)){
            auto dest = store->getPointerOperand();
            if(auto TDIIndex = dyn_cast<GlobalVariable>(dest)){
              if(TDIIndex->getName().equals("_mi_tdi_index")){
                if(store->hasMetadata("noalias")){
                  unnecessaryStores.insert(store);
                  continue;
                }
              }
            }
        } else if(auto Int2Ptr = dyn_cast<IntToPtrInst>(&Inst)){
          if(Int2Ptr->hasMetadata("FieldProjection")){
            auto AndInst = cast<Instruction>(Int2Ptr->getOperand(0));
            auto Ptr2Int = cast<Instruction>(AndInst->getOperand(0));
            auto OrigAddr = Ptr2Int->getOperand(0);
            if(SmartPtr2ShadowMap.find(OrigAddr) != SmartPtr2ShadowMap.end()){
              SmartPtr2ShadowMap[OrigAddr].insert(Int2Ptr);
            }else{
              std::set<Instruction*> set;
              set.insert(Int2Ptr);
              SmartPtr2ShadowMap.insert(std::make_pair(OrigAddr, set));
            }
          }
        }
      }
    }

    if(SmartPtr2ShadowMap.size() > 0){
      //DominatorTreeAnalysis::Result& DT = AM.getResult<DominatorTreeAnalysis>(Func);
      for(auto it: SmartPtr2ShadowMap){
        auto OrigAddr = it.first;
        for(auto inst: it.second){

        assert(dominator != nullptr && "Can't have a null dominator!");
        auto Int2Ptr = inst;
        auto AndInst = cast<Instruction>(Int2Ptr->getOperand(0));
        auto Ptr2Int = cast<Instruction>(AndInst->getOperand(0));
        auto originalBlock = Int2Ptr->getParent();
        auto currentFunction = &Func;
        auto& context = Func.getContext();

        uint64_t stackMask = ~((uint64_t)0x7FFFFF);
        uint64_t segmentMask = (uint64_t)0xFFFFFFFFFE000000;
        uint64_t lowerAddrOffsetMask = ~((uint64_t) segmentMask);

        std::vector<Type *> arg_type;
        std::vector<Value *> args;
        MDNode *N = MDNode::get(context, {MDString::get(context, "rsp")});
        arg_type.push_back(Type::getInt64Ty(context));
        Function *readRSPFunc = Intrinsic::getDeclaration(
            currentFunction->getParent(), Intrinsic::read_register, arg_type);
        args.push_back(MetadataAsValue::get(context, N));

        Value* StackMaskValue = ConstantInt::get(Type::getInt64Ty(context), stackMask);
        Value* SegmentMaskValue = ConstantInt::get(Type::getInt64Ty(context), segmentMask);
        Value* Zero = ConstantInt::get(Type::getInt64Ty(context), 0);

        IRBuilder<> IRB(Int2Ptr);
        Value *StackPtr = IRB.CreateCall(readRSPFunc, args);     
        Value *MaskedStackAddr = IRB.CreateAnd(std::vector<Value*>({StackPtr, StackMaskValue}));
        Value *MaskedOrigAddr = IRB.CreateAnd(std::vector<Value*>({StackMaskValue, Ptr2Int}));
        Value *XORed = IRB.CreateXor(MaskedStackAddr, MaskedOrigAddr);
        Value *ICmp = IRB.CreateICmpEQ(Zero, XORed);

        errs()<<"splitting blocks\n";
        BasicBlock* ShadowBlock = originalBlock->splitBasicBlock(++(cast<Instruction>(ICmp)->getIterator()), "shadow_block");
        BasicBlock* ThenBlock = BasicBlock::Create(context, "shadow.maybe_stack", currentFunction, ShadowBlock);
        BasicBlock* ElseBlock = BasicBlock::Create(context, "shadow.maybe_heap", currentFunction, ShadowBlock);

        //currentFunction->getBasicBlockList().insertBefore(ShadowBlock, ThenBlock);
        //currentFunction->getBasicBlockList().insertBefore(ShadowBlock, ElseBlock);
        errs()<<"inserted new blocks\n";
        Instruction* insertedBranch =&*(++(cast<Instruction>(ICmp)->getIterator()));
        errs()<<"Inserted branch: "<<*insertedBranch<<"\n";
        IRB.SetInsertPoint(insertedBranch);
        IRB.CreateCondBr(ICmp, ThenBlock, ElseBlock);
        insertedBranch->eraseFromParent();

        IRB.SetInsertPoint(ThenBlock);
        Value* StackShadowAddr = IRB.CreateIntToPtr(AndInst, Type::getInt8PtrTy(context));
        IRB.CreateBr(ShadowBlock);


        IRB.SetInsertPoint(ElseBlock);
        Value* segmentPtrInt = IRB.CreateAnd(std::vector<Value*>({SegmentMaskValue, Ptr2Int}));
        Value* segmentPtr = IRB.CreateIntToPtr(segmentPtrInt, Type::getInt8PtrTy(context)->getPointerTo(0));
        //Value* ShadowAddr = IRB.CreateLoad(Type::getInt8PtrTy(context), segmentPtr);
        //IRB.CreateStore(ConstantInt::get(Type::getInt8Ty(context), 1), ShadowAddr);//TODO: get the offset with OR
        Value* HeapShadowAddr = IRB.CreateIntToPtr(AndInst, Type::getInt8PtrTy(context));
        IRB.CreateBr(ShadowBlock);

        IRB.SetInsertPoint(ShadowBlock, ShadowBlock->begin());
        PHINode* phiNode = IRB.CreatePHI(Type::getInt8PtrTy(context), 2, "shadow_address");
        errs()<<"Inserted phi: "<<*phiNode<<"\n";
        phiNode->addIncoming(StackShadowAddr, ThenBlock);
        phiNode->addIncoming(HeapShadowAddr, ElseBlock);
        inst->replaceAllUsesWith(phiNode);
        //inst->eraseFromParent(); //remove the int2Ptr;
        }
      }
    }

    if(candidateCallSites.size() > 0){ // no need to continue if we don't have any calls to focus on
      auto &Context = Func.getContext();
      //Constant* TDISlot_ = M.getOrInsertGlobal("_mi_tdi_index",Type::getInt64Ty(Context));
      //GlobalVariable* TDISlot = cast<GlobalVariable>(TDISlot_);
      //TDISlot->setThreadLocal(true);
      //auto TDISlot = new GlobalVariable(M, Type::getInt64Ty(Context), false, GlobalVariable::ExternalLinkage,
      //           nullptr, "_mi_tdi_index",nullptr,GlobalVariable::ThreadLocalMode::GeneralDynamicTLSModel,0U,true);
      Module& M = *Func.getParent();
      auto getTDISlotCallee = M.getOrInsertFunction("mi_get_tdi_index_slot", FunctionType::get(Type::getVoidTy(Context)->getPointerTo(0), false));
      IRBuilder<> Builder(getTDISlotInsertPoint);
      auto TDISlotCall = Builder.CreateCall(getTDISlotCallee);
      auto TDISlot = Builder.CreateBitCast(TDISlotCall, Type::getInt64PtrTy(Context), "tdi_slot");
      auto ResetValue = ConstantInt::get(IntegerType::getInt64Ty(Context), 0, false);

      for(auto it: candidateCallSites){
        Builder.SetInsertPoint(it.first);
        auto Index = ConstantInt::get(IntegerType::getInt64Ty(Context), it.second, false);
        auto store = Builder.CreateStore(Index, TDISlot, true);
        MDNode* N = MDNode::get(Context, MDString::get(Context, "added by metaupdate pass"));
        store->setMetadata("TDIIndexStore", N);
        /*if(auto callInst = dyn_cast<CallInst>(it.first)){
          Builder.SetInsertPoint(it.first->getNextNode());
          Builder.CreateStore(ResetValue, TDISlot, false);
        }else{
          assert(isa<InvokeInst>(it.first) && "Expecting anything other than call or invoke?");
          auto invokeInst = dyn_cast<InvokeInst>(it.first);
          Builder.SetInsertPoint(&*invokeInst->getNormalDest()->begin());
          Builder.CreateStore(ResetValue, TDISlot, false);
          auto nextInsertPoint = &*invokeInst->getUnwindDest()->begin();
          if (isa<LandingPadInst>(nextInsertPoint)){
            nextInsertPoint = nextInsertPoint->getNextNode();
          }
          Builder.SetInsertPoint(nextInsertPoint);
          Builder.CreateStore(ResetValue, TDISlot, false);
        }*/
      }

      for(auto it: externFuncCalls){
        Builder.SetInsertPoint(it);
        auto Index = ConstantInt::get(IntegerType::getInt64Ty(Context), 0, false);
        auto store = Builder.CreateStore(Index, TDISlot, true);
        MDNode* N = MDNode::get(Context, MDString::get(Context, "added by metaupdate pass"));
        store->setMetadata("TDIIndexStore", N);
      }

      for(auto unstore: unnecessaryStores){
        unstore->eraseFromParent();
      }
    }
  
    for(auto store: unnecessaryStores){
      store->eraseFromParent();
    }
  return PreservedAnalyses::none();
}

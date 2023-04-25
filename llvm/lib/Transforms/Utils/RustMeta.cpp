#include "llvm/Transforms/RustMeta.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/IntrinsicInst.h"
#include <map>
#include <vector>

using namespace llvm;

std::string MetaUpdateSMAPIPass::typeToString(Type* type){
  std::string str;
  llvm::raw_string_ostream rso(str);
  type->print(rso);
  return rso.str();
}

PreservedAnalyses MetaUpdateSMAPIPass::run(Module &M,
                                               ModuleAnalysisManager &AM) {
  for (auto &Func: M){
    if(Func.isDeclaration() || Func.getMetadata("SmartPointerAPIFunc")) continue; //no need to analyze smart pointer APIs for this part

    std::map<Instruction*, size_t> candidateCallSites;
    std::set<Instruction*> externFuncCalls;
    Instruction* getTDISlotInsertPoint = nullptr;
    bool Allocas = true;
    for(auto &BB: Func){
      for (auto &Inst: BB){
        if(Allocas && !isa<AllocaInst>(&Inst)){
          Allocas = false;
          getTDISlotInsertPoint = &Inst;
        }
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
    }

    if(candidateCallSites.size() > 0){ // no need to continue if we don't have any calls to focus on
      auto &Context = M.getContext();
      auto getTDISlotCallee = M.getOrInsertFunction("mi_get_tdi_index_slot", FunctionType::get(Type::getVoidTy(Context)->getPointerTo(0), false));

      IRBuilder<> Builder(getTDISlotInsertPoint);
      auto TDISlotCall = Builder.CreateCall(getTDISlotCallee);
      auto TDISlot = Builder.CreateBitCast(TDISlotCall, Type::getInt64PtrTy(Context), "tdi_slot");
      auto ResetValue = ConstantInt::get(IntegerType::getInt64Ty(Context), 0, false);

      for(auto it: candidateCallSites){
        Builder.SetInsertPoint(it.first);
        auto Index = ConstantInt::get(IntegerType::getInt64Ty(Context), it.second, false);
        Builder.CreateStore(Index, TDISlot, true);
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
        Builder.CreateStore(Index, TDISlot, true);
      }
    }
  }
  return PreservedAnalyses::all();
}

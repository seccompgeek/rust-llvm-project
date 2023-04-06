#include "llvm/Transforms/RustMeta.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include <map>
#include <vector>

using namespace llvm;

PreservedAnalyses MetaUpdateSMAPIFuncPass::run(Function &F,
                                               FunctionAnalysisManager &AM) {
  if (!F.isDeclaration()) {
    std::map<Instruction *, unsigned long long> candidate_map;
    auto currentFuncSMMD = F.getMetadata("SmartPointerAPIFunc");
    Instruction *tdi_call_before = nullptr;
    bool still_alloca = true;
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (!isa<AllocaInst>(&I) && still_alloca) {
          still_alloca = false;
          tdi_call_before = &I;
        }
        if (auto callbase = dyn_cast<CallBase>(&I)) {
          if (auto callee = callbase->getCalledFunction()) {
            if (auto SMMD = callee->getMetadata("SmartPointerAPIFunc")) {
              auto value_type = cast<MetadataAsValue>(SMMD->getOperand(0))->getType();
              if (currentFuncSMMD != nullptr &&
                  currentFuncSMMD->getOperand(0) == SMMD->getOperand(0)) {
                continue;
              }

              bool index_set = false;
              if(auto smartpointers = F.getParent()->getNamedMetadata("SmartPointers")){
                for(auto op: smartpointers->operands()){
                  auto val = cast<Value>(op);
                  if(auto mdv = dyn_cast<MetadataAsValue>(val)){
                    Metadata* md = mdv->getMetadata();
                    if(ConstantAsMetadata* cam = dyn_cast<ConstantAsMetadata>(md)){
                      if(cam->getValue()->getType() == value_type){
                        candidate_map.insert(std::make_pair(&I, 1));
                        index_set = true;
                        break;
                      }
                    }
                  }
                }
              }

              if(!index_set){
                if (TypeMetadataToTDIIndexMap.find(value_type) !=
                         TypeMetadataToTDIIndexMap.end()) {

                  candidate_map.insert(
                      std::make_pair(&I, TypeMetadataToTDIIndexMap[value_type]));
                } else {
                  auto next_index = TypeMetadataToTDIIndexMap.size() +
                                    2; // 0 is default, 1 is for smart pointers
                  TypeMetadataToTDIIndexMap.insert(
                      std::make_pair(value_type, next_index));
                  candidate_map.insert(std::make_pair(&I, next_index));
                }
              }
            }else if(callee->getMetadata("ExchangeMallocFunc")){
              //TODO: track uses of this call untill you reach a store.
            }
          }
        }
      }
    }

    if (!candidate_map.empty()) {
      FunctionType *tdi_slot_type = FunctionType::get(
          Type::getVoidTy(F.getContext())->getPointerTo(0), false);
      auto CB = F.getParent()->getOrInsertFunction("mi_get_tdi_index_slot",
                                                   tdi_slot_type);
      IRBuilder<> IRB(tdi_call_before);
      auto index_slot = IRB.CreateCall(CB, None, "tdi_index_slot", nullptr);
      for (auto it : candidate_map) {
        auto tdi_index = ConstantInt::get(
            IntegerType::getInt64Ty(F.getContext()), it.second);
        new StoreInst(tdi_index, index_slot, it.first);
      }
    }
  }
  return PreservedAnalyses::all();
}

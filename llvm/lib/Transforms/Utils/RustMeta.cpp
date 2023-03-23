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
              auto value = cast<MDString>(SMMD->getOperand(0))->getString();
              if (currentFuncSMMD != nullptr &&
                  currentFuncSMMD->getOperand(0) == SMMD->getOperand(0)) {
                continue;
              }

              if (value.startswith("000")) {
                candidate_map.insert(std::make_pair(&I, 1));
              } else if (TypeMetadataToTDIIndexMap.find(value) !=
                         TypeMetadataToTDIIndexMap.end()) {

                candidate_map.insert(
                    std::make_pair(&I, TypeMetadataToTDIIndexMap[value]));
              } else {
                auto next_index = TypeMetadataToTDIIndexMap.size() +
                                  2; // 0 is default, 1 is for smart pointers
                TypeMetadataToTDIIndexMap.insert(
                    std::make_pair(value, next_index));
                candidate_map.insert(std::make_pair(&I, next_index));
              }
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

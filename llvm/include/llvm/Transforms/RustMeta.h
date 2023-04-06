#ifndef LLVM_TRANSFORMS_RUSTMETA_H
#define LLVM_TRANSFORMS_RUSTMETA_H

#include "llvm/IR/PassManager.h"
#include <map>
#include <set>

namespace llvm {
class MetaUpdateSMAPIFuncPass : public PassInfoMixin<MetaUpdateSMAPIFuncPass> {
  std::map<std::string, unsigned long long> TypeMetadataToTDIIndexMap;
  std::set<std::string> SmartPointerTypes;

public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif

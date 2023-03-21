#ifndef LLVM_TRANSFORMS_RUSTMETA_H
#define LLVM_TRANSFORMS_RUSTMETA_H

#include "llvm/IR/PassManager.h"
#include <map>

namespace llvm {
class MetaUpdateSMAPIFuncPass : public PassInfoMixin<MetaUpdateSMAPIFuncPass> {
  std::map<llvm::StringRef, unsigned long long> TypeMetadataToTDIIndexMap;

public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif

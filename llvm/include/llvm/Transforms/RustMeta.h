#ifndef LLVM_TRANSFORMS_RUSTMETA_H
#define LLVM_TRANSFORMS_RUSTMETA_H

#include "llvm/IR/PassManager.h"
#include <map>
#include <set>

namespace llvm {
class MetaUpdateSMAPIPass : public PassInfoMixin<MetaUpdateSMAPIPass> {
  std::map<StringRef, unsigned long long> TypeMetadataToTDIIndexMap;
  std::set<StringRef> SmartPointerTypes;
  std::string typeToString(Type* type);

public:
  PreservedAnalyses run(Function &Func, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif

#ifndef LLVM_TRANSFORMS_RUSTMETA_H
#define LLVM_TRANSFORMS_RUSTMETA_H

#include "llvm/IR/PassManager.h"
#include <map>
#include <set>

namespace llvm {
class MetaUpdateSMAPIPass : public PassInfoMixin<MetaUpdateSMAPIPass> {
  std::map<std::string, unsigned long long> TypeMetadataToTDIIndexMap;
  std::set<std::string> SmartPointerTypes;
  std::string typeToString(Type* type);

public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

} // namespace llvm

#endif

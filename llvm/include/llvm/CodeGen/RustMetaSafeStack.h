#ifndef LLVM_CODEGEN_RUSTMETA_SAFESTACK_H
#define LLVM_CODEGEN_RUSTMETA_SAFESTACK_H

#include "llvm/IR/PassManager.h"
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <string>
#include <utility>

namespace llvm {
    class MetaSafeStackPass : public PassInforMixin<MetaSafeStackPass> {
        const TargetMachine* TM = nullptr;
        public:
        PreservedAnalyses run(Module &M, FunctionAnalysisManager &FAM);
    };
}

#endif
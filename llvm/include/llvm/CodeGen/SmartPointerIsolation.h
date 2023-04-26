#ifndef SMART_POINTER_ISOLATION_H
#define SMART_POINTER_ISOLATION_H

#include "llvm/IR/PassManager.h"

namespace llvm {

	class Function;

	class RSPIPass : public PassInfoMixin<RSPIPass> {
		public:
 			PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
	};
}

#endif 
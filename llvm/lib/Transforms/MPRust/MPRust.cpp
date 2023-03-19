#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Pass.h"
#include "llvm/IR/IRBuilder.h"
#include <map>
#include <vector>

#define DEBUG_TYPE "MPRust"

using namespace llvm;

namespace {
    struct RustMetaUpdate: public ModulePass {
        static char ID;
        std::map<std::string, unsigned long long> tdi_index_map;
        RustMetaUpdate(): ModulePass(ID) {}

        bool runOnModule(Module &M) override;
    };

    

    bool RustMetaUpdate::runOnModule(Module &M){
        bool changed = false;
        for(auto &F: M){
            std::map<Instruction*, unsigned long long> candidate_map;
            for(auto &BB: F){
                for(auto &I: BB){
                    if(auto call = dyn_cast<CallBase>(&I)){
                        if(auto callee = call->getCalledFunction()){
                            if(auto SMMD = callee->getMetadata("SmartPointerAPIFunc")){
                                auto value = cast<MDString>(SMMD->getOperand(0))->getString();
                                if(value.startswith("000")){
                                    candidate_map.insert(std::make_pair(&I, 1));
                                }
                            }
                        }
                    }
                }
            }

            if(!candidate_map.empty()){
                FunctionType* tdi_slot_type = FunctionType::get(Type::getVoidTy(M.getContext())->getPointerTo(0), false);
                auto CB = M.getOrInsertFunction("mi_get_tdi_index_slot", tdi_slot_type);
                auto insertInst = &*(F.begin()->begin());
                IRBuilder<> IRB(insertInst);
                auto index_slot = IRB.CreateCall(CB, None, "tdi_index_slot", nullptr);
                for(auto it: candidate_map){
                    auto tdi_index = ConstantInt::get(IntegerType::getInt64Ty(F.getContext()), it.second);
                    new StoreInst(tdi_index, index_slot, it.first);
                }
                changed = true;
            }
        }

        return false;
    }
}

char RustMetaUpdate::ID = 0;
static RegisterPass<RustMetaUpdate> MPRPass("metaupdate", "Set and reset TDI indices");
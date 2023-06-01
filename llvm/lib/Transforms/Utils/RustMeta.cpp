#include "llvm/Transforms/RustMeta.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Dominators.h"
#include <map>
#include <vector>

using namespace llvm;

std::string MetaUpdateSMAPIPass::typeToString(Type* type){
  std::string str;
  llvm::raw_string_ostream rso(str);
  type->print(rso);
  return rso.str();
}

PreservedAnalyses MetaUpdateSMAPIPass::run(Function& Func,
                                               FunctionAnalysisManager &AM) {

  if(Func.isDeclaration()) return PreservedAnalyses::all();

    std::map<Instruction*, size_t> candidateCallSites;
    std::set<Instruction*> externFuncCalls;
    std::set<Instruction*> unnecessaryStores;
    std::map<uint64_t, uint64_t> optimizedIndices;

    std::map<Value*, std::set<Instruction*>> SmartPtr2ShadowMap;
    std::set<Instruction*> SmartPtrProjections;

    bool TDIAnalysis = !Func.getMetadata("SmartPointerAPIFunc");
    bool foundTDIIndexSet = false;

    Instruction* getTDISlotInsertPoint = nullptr;
    bool Allocas = true;
    for(auto &BB: Func){
      for (auto &Inst: BB){
        if(Allocas && !isa<AllocaInst>(&Inst)){
          Allocas = false;
          getTDISlotInsertPoint = &Inst;
        }

        if(TDIAnalysis){
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

            if(auto calledFunc = call->getCalledFunction()){
              auto funcName = calledFunc->getName();
              if(funcName.equals("__rust_alloc") || funcName.equals("__rust_alloc_zeroed") || funcName.equals("__rust_realloc")) {
                Module* M = Func.getParent();
                auto& context = M->getContext();
                FunctionCallee callee = M->getOrInsertFunction("_tdi_set_ptr_valid", FunctionType::get(Type::getVoidTy(context), std::vector<Type*>({Type::getInt8PtrTy(context)}),false));

                IRBuilder<> IRB(&*(++call->getIterator()));
                IRB.CreateCall(callee, std::vector<Value*>({call}));
              }else if(funcName.equals("__rust_dealloc")){
                Module* M = Func.getParent();
                auto& context = M->getContext();
                FunctionCallee callee = M->getOrInsertFunction("_tdi_set_ptr_invalid", FunctionType::get(Type::getVoidTy(context), std::vector<Type*>({Type::getInt8PtrTy(context)}), false));
                IRBuilder<> IRB(call);
                IRB.CreateCall(callee, std::vector<Value*>({call->getArgOperand(0)}));
                // no need to validate before this, the set-invalid function will validate first!
              }
            }
          }
        }
        
        if (auto store = dyn_cast<StoreInst>(&Inst)){
            auto dest = store->getPointerOperand();
            if(auto TDIIndex = dyn_cast<GlobalVariable>(dest)){
              if(TDIIndex->getName().equals("_mi_tdi_index")){
                foundTDIIndexSet = true;
                if(store->hasMetadata("noalias")){
                  unnecessaryStores.insert(store);
                  continue;
                }
              }
            }
        } else if(auto Int2Ptr = dyn_cast<IntToPtrInst>(&Inst)){
          if(Int2Ptr->hasMetadata("FieldProjection")){
            IRBuilder<> IRB(&*(++Int2Ptr->getIterator()));
            IRB.CreateLoad(Type::getInt8PtrTy(Int2Ptr->getContext()), Int2Ptr, true); //insert volatile load to maintain performance overhead.
          }
        }
      }
    }

    if(!foundTDIIndexSet && candidateCallSites.size() > 0){ // no need to continue if we don't have any calls to focus on
      auto &Context = Func.getContext();
      Module& M = *Func.getParent();
      Constant* TDISlot_ = M.getOrInsertGlobal("_mi_tdi_index",Type::getInt64Ty(Context));
      GlobalVariable* TDISlot = cast<GlobalVariable>(TDISlot_);
      TDISlot->setThreadLocal(true);
      //auto getTDISlotCallee = M.getOrInsertFunction("mi_get_tdi_index_slot", FunctionType::get(Type::getVoidTy(Context)->getPointerTo(0), false));
      IRBuilder<> Builder(getTDISlotInsertPoint);
      /*auto TDISlotCall = Builder.CreateCall(getTDISlotCallee);
      auto TDISlot = Builder.CreateBitCast(TDISlotCall, Type::getInt64PtrTy(Context), "tdi_slot");
      auto ResetValue = ConstantInt::get(IntegerType::getInt64Ty(Context), 0, false);*/
      FunctionCallee enableMPK = M.getOrInsertFunction("_mi_mpk_enable_writes", FunctionType::getVoidTy(Context));
      std::set<BasicBlock*> mpkEnabledBlocks;
      for(auto it: candidateCallSites){
        Builder.SetInsertPoint(it.first);
        if(it.first->getMetadata("SetMPKEnable")){
            if(mpkEnabledBlocks.find(it.first->getParent()) == mpkEnabledBlocks.end()){
              Builder.CreateCall(enableMPK, std::vector<Value*>({}));
              mpkEnabledBlocks.insert(it.first->getParent());
            }
        }
        auto Index = ConstantInt::get(IntegerType::getInt64Ty(Context), it.second, false);
        auto store = Builder.CreateStore(Index, TDISlot, true);
        MDNode* N = MDNode::get(Context, MDString::get(Context, "added by metaupdate pass"));
        store->setMetadata("TDIIndexStore", N);
      }

      FunctionCallee disableMPK = M.getOrInsertFunction("_mi_mpk_disable_writes", FunctionType::getVoidTy(Context));
      for(auto block: mpkEnabledBlocks){
        auto lastInst = block->back();
        IRBuilder<> IRB(&lastInst);
        if(auto invokeInst = dyn_cast<InvokeInst>(&lastInst)){
          if(auto lp = invokeInst->getLandingPadInst()){
            IRB.SetInsertPoint(lp->getNextNode());

          }
        }
      }

      for(auto it: externFuncCalls){
        Builder.SetInsertPoint(it);
        auto Index = ConstantInt::get(IntegerType::getInt64Ty(Context), 0, false);
        auto store = Builder.CreateStore(Index, TDISlot, true);
        MDNode* N = MDNode::get(Context, MDString::get(Context, "added by metaupdate pass"));
        store->setMetadata("TDIIndexStore", N);
      }

      for(auto unstore: unnecessaryStores){
        unstore->eraseFromParent();
      }
    }
  return PreservedAnalyses::none();
}

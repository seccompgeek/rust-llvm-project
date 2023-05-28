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

  /*Find special types housed in normal structs and insert new structs to replace them
  auto structTypes = M.getIdentifiedStructTypes();
  auto specialTypeMetadata = M.getNamedMetadata("SpecialTypes");
  std::map<StructType*, StructType*> specialTypeHousedStructsMap;
  std::map<StructType*, std::map<int, int>> specialTypeFieldRemap;
  std::set<StructType*> specialTypes;
  for(auto MDIt: specialTypeMetadata->operands()){
    auto MDValue = cast<MDString>(MDIt)->getString();
    for(auto type: structTypes){
      if (type->getStructName().equals(MDValue)){
        specialTypes.insert(type);
      }
    }
  }

  for(auto type: structTypes){
    if (specialTypes.find(type) == specialTypes.end()){
      auto totalFields = type->getStructNumElements();
      SmallVector<Type*> specialFields;
      SmallVector<int> FieldIndices;
      for(int i=0; i<totalFields; i++){
        auto fieldType = type->getStructElementType(i);
        if(auto structFieldType = dyn_cast<StructType>(fieldType)){
          if(specialTypes.find(structFieldType) != specialTypes.end()){
            specialFields.push_back(fieldType);
            FieldIndices.push_back(i);
          }
        }
      }

      if(specialFields.size() != 0){//TODO: if all fields are special, make this a special type as well as an optimization
        StructType* newType = StructType::create(specialFields);
        newType->setName(type->getStructName().str()+".safe");
        specialTypeHousedStructsMap.insert(std::make_pair(type, newType));
        specialTypeFieldRemap.insert(std::make_pair(type, std::map<int, int>()));
        int counter = 0;
        for(auto i: FieldIndices){
          specialTypeFieldRemap[type].insert(std::make_pair(i, counter++));
        }
      }
    }
  }

  auto checkIsZeroIdxGep = [&specialTypeFieldRemap](Type* type) {
    if(auto structType = dyn_cast<StructType>(type)){
      return specialTypeFieldRemap.find(structType) != specialTypeFieldRemap.end() && specialTypeFieldRemap[structType].find(0) != specialTypeFieldRemap[structType].end();
    }else {
      return false;
    }
  };

  for (auto &Func: M){
    if (Func.isDeclaration()) continue;
    std::map<Instruction*, Instruction*> housingPtrToSafePtrMap;
    for(auto &Inst: Func) {
      if(auto memInst = dyn_cast<MemTransferInst>(&Inst)){
        auto source = memInst->getSource();
        auto dest = memInst->getDest();
        auto len = memInst->getLength();
      }
    }
  }*/

  if(Func.isDeclaration()) return PreservedAnalyses::all();

    std::map<Instruction*, size_t> candidateCallSites;
    std::set<Instruction*> externFuncCalls;
    std::set<Instruction*> unnecessaryStores;
    std::map<uint64_t, uint64_t> optimizedIndices;

    std::map<Value*, std::set<Instruction*>> SmartPtr2ShadowMap;
    std::set<Instruction*> SmartPtrProjections;

    bool TDIAnalysis = !Func.getMetadata("SmartPointerAPIFunc");

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
          }
        }
        
        if (auto store = dyn_cast<StoreInst>(&Inst)){
            auto dest = store->getPointerOperand();
            if(auto TDIIndex = dyn_cast<GlobalVariable>(dest)){
              if(TDIIndex->getName().equals("_mi_tdi_index")){
                if(store->hasMetadata("noalias")){
                  unnecessaryStores.insert(store);
                  continue;
                }
              }
            }
        } else if(auto Int2Ptr = dyn_cast<IntToPtrInst>(&Inst)){
          if(Int2Ptr->hasMetadata("FieldProjection")){
            IRBuilder<> IRB(++Int2Ptr->getIterator());
            IRB.CreateLoad(Type::getInt8PtrTy(Int2Ptr->getContext()), Int2Ptr, true); //insert volatile load to maintain performance overhead.
          }
        }
      }
    }

    if(candidateCallSites.size() > 0){ // no need to continue if we don't have any calls to focus on
      auto &Context = Func.getContext();
      //Constant* TDISlot_ = M.getOrInsertGlobal("_mi_tdi_index",Type::getInt64Ty(Context));
      //GlobalVariable* TDISlot = cast<GlobalVariable>(TDISlot_);
      //TDISlot->setThreadLocal(true);
      //auto TDISlot = new GlobalVariable(M, Type::getInt64Ty(Context), false, GlobalVariable::ExternalLinkage,
      //           nullptr, "_mi_tdi_index",nullptr,GlobalVariable::ThreadLocalMode::GeneralDynamicTLSModel,0U,true);
      Module& M = *Func.getParent();
      auto getTDISlotCallee = M.getOrInsertFunction("mi_get_tdi_index_slot", FunctionType::get(Type::getVoidTy(Context)->getPointerTo(0), false));
      IRBuilder<> Builder(getTDISlotInsertPoint);
      auto TDISlotCall = Builder.CreateCall(getTDISlotCallee);
      auto TDISlot = Builder.CreateBitCast(TDISlotCall, Type::getInt64PtrTy(Context), "tdi_slot");
      auto ResetValue = ConstantInt::get(IntegerType::getInt64Ty(Context), 0, false);

      for(auto it: candidateCallSites){
        Builder.SetInsertPoint(it.first);
        auto Index = ConstantInt::get(IntegerType::getInt64Ty(Context), it.second, false);
        auto store = Builder.CreateStore(Index, TDISlot, true);
        MDNode* N = MDNode::get(Context, MDString::get(Context, "added by metaupdate pass"));
        store->setMetadata("TDIIndexStore", N);
        /*if(auto callInst = dyn_cast<CallInst>(it.first)){
          Builder.SetInsertPoint(it.first->getNextNode());
          Builder.CreateStore(ResetValue, TDISlot, false);
        }else{
          assert(isa<InvokeInst>(it.first) && "Expecting anything other than call or invoke?");
          auto invokeInst = dyn_cast<InvokeInst>(it.first);
          Builder.SetInsertPoint(&*invokeInst->getNormalDest()->begin());
          Builder.CreateStore(ResetValue, TDISlot, false);
          auto nextInsertPoint = &*invokeInst->getUnwindDest()->begin();
          if (isa<LandingPadInst>(nextInsertPoint)){
            nextInsertPoint = nextInsertPoint->getNextNode();
          }
          Builder.SetInsertPoint(nextInsertPoint);
          Builder.CreateStore(ResetValue, TDISlot, false);
        }*/
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

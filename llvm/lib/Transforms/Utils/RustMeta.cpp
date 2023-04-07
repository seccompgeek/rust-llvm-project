#include "llvm/Transforms/RustMeta.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/IntrinsicInst.h"
#include <map>
#include <vector>

using namespace llvm;

std::string MetaUpdateSMAPIPass::typeToString(Type* type){
  std::string str;
  llvm::raw_string_ostream rso(str);
  type->print(rso);
  return rso.str();
}

PreservedAnalyses MetaUpdateSMAPIPass::run(Module &M,
                                               ModuleAnalysisManager &AM) {
  //collect smart pointer types
  for(auto &F: M){
    if(auto SMMD = F.getMetadata("SmartPointerAPIFunc")){
      auto value = cast<MDString>(SMMD->getOperand(0))->getString();
      if(value.startswith("000")){
        value = value.substr(3);
        SmartPointerTypes.insert(value);
      }
    }
    for(auto &I: F){
      if(auto alloca = dyn_cast<AllocaInst>(&I)){
        if(alloca->hasMetadata("RustMeta-Smart-Pointer")){
          auto value = typeToString(alloca->getAllocatedType());
          SmartPointerTypes.insert(value);
        }
      }
    }
  }

  //insert TDI index before SP-API calls
  for(auto &F: M){
    if(!F.isDeclaration() && !F.getMetadata("SmartPointerAPIFunc")){
      std::map<Instruction*, unsigned long long> candidate_map;
      Instruction *tdi_call_before = nullptr;
      bool still_alloca = true;

      for (auto &BB: F){
        for(auto &II: BB){
          if(!isa<AllocaInst>(&II) && still_alloca){
            still_alloca = false;
            tdi_call_before = &II;
          }

          if(auto callbase = dyn_cast<CallBase>(&II)){
            if(auto callee = callbase->getCalledFunction()){
              if(auto SMMD = callee->getMetadata("SmartPointerAPIFunc")){
                auto value = cast<MDString>(SMMD->getOperand(0))->getString();
                if(value.startswith("000")){
                  value = value.substr(3);
                }
                if(SmartPointerTypes.find(value) != SmartPointerTypes.end()){
                  candidate_map.insert(std::make_pair(&II, 1));
                }else{
                  unsigned long long tdi_index = 0;
                  if(TypeMetadataToTDIIndexMap.find(value) == TypeMetadataToTDIIndexMap.end()){
                    tdi_index = TypeMetadataToTDIIndexMap.size() + 2;
                    TypeMetadataToTDIIndexMap.insert(std::make_pair(value, tdi_index));
                  }else{
                    tdi_index = TypeMetadataToTDIIndexMap[value];
                  }
                  candidate_map.insert(std::make_pair(&II, tdi_index));
                }
              }else{
                //handle exchange_malloc
                if(callee->getMetadata("ExchangeMallocFunc")){
                  for(auto users: II.users()){

                  }
                }
              }
            }
          }
        }
      }
    }
  }
  
  return PreservedAnalyses::all();
}

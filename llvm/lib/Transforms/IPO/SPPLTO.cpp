///////////////////////////////////////////
///                                     ///
///           /IPO/SPPLTO.cpp           ///
///           (clangllvm.12.0)          ///
///                                     ///
///////////////////////////////////////////


#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Transforms/IPO/SPPLTO.h"
#include "llvm/Transforms/IPO.h"

#include "llvm/Analysis/ValueTracking.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "../lib/IR/ConstantsContext.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include <utility>
#include <queue>
#include <unordered_set>
#include <cxxabi.h>

#include<climits>
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ValueTracking.h"
#include <algorithm>
#include "llvm/ADT/Statistic.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "../lib/IR/ConstantsContext.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include <utility>
#include <queue>
#include <unordered_set>
#include <cxxabi.h>
#include "llvm/Transforms/Miu/MiuUtils.h"

#define DEBUG_TYPE "spplto"

//#define SPPDEBUG // Uncomment for debugging
#ifdef SPPDEBUG
#  define dbg(x) x
#else
#  define dbg(x)
#endif


#define SPPFUNC(F)  (F->getName().startswith("__spp"))

using namespace llvm;
using namespace std; // Jin: this is NOT recommended..

namespace {

struct SPPLTO : public ModulePass {
  static char ID;

  SPPLTO() : ModulePass(ID) {
    initializeSPPLTOPass(*PassRegistry::getPassRegistry());
  }

  virtual bool runOnFunction (Function * F, Module &M);
  virtual bool runOnModule(Module &M);
  bool doCallBase (CallBase * ins);

  void getAnalysisUsage(AnalysisUsage &AU) const override{

    //AU.addRequired<DominatorTreeWrapperPass>();
    //AU.addRequired<AAResultsWrapperPass>();
    //AU.addRequired<CallGraphWrapperPass>();
    //AU.addRequired<TargetLibraryInfoWrapperPass>();
  }

  protected:

};

} // end anonymous namespace

char SPPLTO::ID = 0;

INITIALIZE_PASS(SPPLTO, "spplto", "SPPLTO", false, false)

ModulePass *llvm::createSPPLTOPass() {
  return new SPPLTO;
}

PreservedAnalyses
SPPLTOPass::run(Module &M, ModuleAnalysisManager &MAM) {
  return PreservedAnalyses::all();
}

static string 
demanglename (StringRef str)
{
    string result= "";
    int unmangledStatus;
    
    char *unmangledName = abi::__cxa_demangle(
        str.data(), nullptr, nullptr, &unmangledStatus);
    if (unmangledStatus == 0) {
        string unmangledNameStr(unmangledName);
        result= unmangledNameStr;
    }
    return result;    
}

static bool
doCallFunc_LLVMDbg (CallBase * CB)
{
    dbg(errs()<<" llvm.dbg.CB \n";)

    MetadataAsValue* Arg= dyn_cast<MetadataAsValue>(CB->getOperand(0));
    assert(Arg);
    
    ValueAsMetadata * ArgMD= dyn_cast<ValueAsMetadata>(Arg->getMetadata());   
    assert(ArgMD);
    
    Value * ArgVal= ArgMD->getValue();   
    assert(ArgVal);
    
    dbg(errs()<<"  -Arg(0): "<<*ArgVal<<"\n";)
    
    if (!ArgVal->getType()->isPointerTy() || isa<Constant>(ArgVal)) {
        dbg(errs()<<"   :: skip. Not Pointerty\n";)
        return false;
    }

    IRBuilder<> B(CB);
    vector <Value*> arglist;
    
    Module * mod= CB->getModule();
    Type* vpty= Type::getInt8PtrTy(mod->getContext());
    FunctionType * fty= FunctionType::get(vpty, vpty, false);
    FunctionCallee hook = 
        mod->getOrInsertFunction("__spp_cleantag_external", fty); 

    Value* TmpPtr = B.CreateBitCast(ArgVal, 
                hook.getFunctionType()->getParamType(0));
    arglist.push_back(TmpPtr);
    CallInst* Masked = B.CreateCall(hook, arglist);
    Value* Unmasked = B.CreateBitCast(Masked, ArgVal->getType()); 
    MetadataAsValue * MDAsVal= 
            MetadataAsValue::get(CB->getModule()->getContext(), 
                                 ValueAsMetadata::get(Unmasked));
    dbg(errs()<<"  -newArg: "<<*MDAsVal->stripPointerCasts()<<"\n";)
    
    CB->setArgOperand(0, MDAsVal);
    dbg(errs()<<"  NewCB: "<< *CB <<"\n";)
    
    return true;
}

static bool
doCallExternal(CallBase * CB)
{
    // Skip tag cleaning for certain transaction functions
    if (CB->getCalledFunction() != NULL && 
        CB->getCalledFunction()->getName().contains("pmemobj_tx_add_range_direct")) {
            return false;
        }
    bool Changed= false;

    Module * mod= CB->getModule();
    Type* vpty= Type::getInt8PtrTy(mod->getContext());
    FunctionType * fty= FunctionType::get(vpty, vpty, false);
    
    FunctionCallee hook = 
        mod->getOrInsertFunction("__spp_cleantag_external", fty); 

    for (auto Arg = CB->arg_begin(); Arg != CB->arg_end(); ++Arg) {

        dbg(errs()<<" -Arg: "<<**Arg<<"\n";)
        
        Value * ArgVal= dyn_cast<Value>(Arg);
        if (!ArgVal) {
            dbg(errs()<<"   :: Skip. Not_value\n";)
            continue;
        }
        
        /// Now we got a Value arg. 
        if (!ArgVal->getType()->isPointerTy()) {
            dbg(errs()<<"\t:: Skip. Not pointerType\n";)
            continue;
        }
        //if (!ArgVal->getType()->isAggregateType()) {
        //    dbg(errs()<<"\t:: Skip. Not AggreType\n";)
        //    continue;
        //}
        if (isa<Constant>(ArgVal)) {
            dbg(errs()<<"\t:: Skip. is Constant\n";)
            continue; 
        } 
        
        // TODO: move to opt pass later.
        //if (isSafePtr(From->stripPointerCasts())) {
        //    continue; 
        //}
        //if (ArgVal->getType()->isPointerTy()) {
        
        IRBuilder<> B(CB);
        vector <Value*> arglist;
/* In progress
        if (CB->getCalledFunction() != NULL && 
            CB->getCalledFunction()->getName().contains("pmemobj_tx_add_range")) {

            // Update the ptr tag for precaution check for snapshotting
            FunctionCallee hookUpdate = 
            mod->getOrInsertFunction("__spp_updatetag", fty);

            vector <Value*> addarglist;
            Value* TmpPtr = B.CreateBitCast(ArgVal, 
                        hookUpdate.getFunctionType()->getParamType(0));
            addarglist.push_back(TmpPtr);

            Value Size = dyn_cast<Value>(Arg->getNext());
            Value* TmpSize = B.CreateBitCast(ArgVal, 
                        hookUpdate.getFunctionType()->getParamType(1));
            addarglist.push_back(TmpSize);
            CallInst* UpdatedTag = B.CreateCall(hookUpdate, addarglist);

            // Perform the bounds checking on updated tag
            vector <Value*> checkarglist;
            FunctionCallee hookCheck = 
            mod->getOrInsertFunction("__spp_checkbound", fty);
            Value* TmpUnmasked = B.CreateBitCast(UpdatedTag, 
                        hookCheck.getFunctionType()->getParamType(0));
            checkarglist.push_back(TmpUnmasked);
            CallInst* TmpMasked = B.CreateCall(hookCheck, checkarglist);
            Value* Unmasked = B.CreateBitCast(TmpMasked, ArgVal->getType()); 
            CB->setArgOperand(Arg - CB->arg_begin(), Unmasked);

            //dbg(errs()<<" --> new_CB: "<< *CB<<"\n";)

            return true;
        }*/

        Value* TmpPtr = B.CreateBitCast(ArgVal, 
                        hook.getFunctionType()->getParamType(0));
        arglist.push_back(TmpPtr);
        CallInst* Masked = B.CreateCall(hook, arglist);
        Value* Unmasked = B.CreateBitCast(Masked, ArgVal->getType()); 

        CB->setArgOperand(Arg - CB->arg_begin(), Unmasked);

        dbg(errs()<<" --> new_CB: "<< *CB<<"\n";)

        Changed = true;
    }
    return Changed;
}

static bool
doCallNonFunc (CallBase * cb)
{
    return  doCallExternal(cb);
}

static bool
doCallFunction (CallBase * cb, Function * cfn)
{
    assert(cfn);
   
    // just checking..
    if (cfn->getName().startswith("llvm.dbg.")) {
        return doCallFunc_LLVMDbg (cb); 
    }
    if (cfn->isDeclaration() ||
        StringRef(demanglename(cfn->getName())).equals("pmemobj_direct_inline") ||
        cfn->getName().contains("pmemobj_direct_inline") ||
        cfn->getName().contains("ZL21pmemobj_direct_inline7pmemoid") 
        ) {
         
        dbg(errs()<<"  ---> external function call ...\n";)
        return  doCallExternal(cb);
    }
    
    assert(!cfn->getName().contains("pmemobj_direct_"));    

    dbg(errs()<<"  :: skip. Internal func\n";)
    return false; 
}


bool
SPPLTO::doCallBase (CallBase * cb)
{
    bool changed= false;
    dbg(errs()<<"CallBase:  "<<*cb<<"\n\n";)

    Function * cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());

    if (cfn) {
        
        StringRef fname= cfn->getName();
        dbg(errs()<<"CalledFn: "<< fname <<" / " << demanglename(fname) <<"\n";)
        if (SPPFUNC(cfn)) {
            dbg(errs()<<"  :: skip. Hook Func\n";)
            return false; 
        }
        // to be interposed at link time
        
        if (fname.equals("free") || isStringFuncName(fname)) {
            dbg(errs()<<"  :: skip. free or string func.\n";)
            return false;
        }
    //    if (fname.equals("pmemobj_tx_alloc") || fname.equals("pmemobj_tx_add_range_direct")) {
    //        dbg(errs()<<"  :: skip. pmemobj_* func\n";)
    //        return false;
    //    }
        changed= doCallFunction (cb, cfn);
    }
    else {
        changed= doCallNonFunc (cb);
    }
    
    return changed;
}

    bool
SPPLTO::runOnFunction (Function * FN, Module & M)
{
    bool changed= false;

    for (auto BB= FN->begin(); BB != FN->end(); ++BB) {
        for (auto ins= BB->begin(); ins != BB->end(); ++ins ) { 
            dbg(errs()<<"\n----------------------------\n";)
            if (auto cb = dyn_cast<CallBase>(ins)) {
                changed= doCallBase(&*cb); 
            }
            else {
                dbg(errs()<<"I_LTO: "<<*ins<<"\n";)
            }
        }
    }
  return changed;
}

bool
SPPLTO::runOnModule (Module &M)
{
    //sppltopasscounter++;
    
    dbg(errs()<<"\n>>>>>>> Starting SPPLTO pass .....\n";)
    
    dbg(errs()<<"************************************\n";)
    dbg(errs()<<"**   RunOnModule    ****************\n";)
    dbg(errs()<<"**   Mod Name: "<<M.getModuleIdentifier()<<"\n";)
    
    /////////////////////////////////////////////////
    ///
    /// DO NOT DELETE the following lines,
    ///   -- returning if 'main' doesnt exist)!!!
    /// Deleting it causes unit test failures, and
    /// LLVM errors - Immutable passes not initialised, since
    /// it just exits without returning to LLVM pass manager.
    /// LLVM just loses track of it, and emits errors.
    ///

    if (!M.getFunction("main")) {
        /////////////////////////////
        errs()<<"!> ALERT: No main\n";
        dbg(errs()<<"Module: "<< M <<"\n";)
        return false; /// DON'T DELETE ME!!
    }
     
    for (auto Fn= M.begin(); Fn!= M.end(); ++Fn) {

        dbg(errs()<<"\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n";) 
        dbg(errs()<<">> FName: "<<Fn->getName()<<"\n";)
        dbg(errs()<<"\t< "<< demanglename(Fn->getName()) << ">\n";)
        if (Fn->isDeclaration()) {
            dbg(errs()<<"\t::decl. skipping..\n";)
            continue;
        } 
        if (SPPFUNC(Fn)) { // hook func names are not mangled.
            dbg(errs()<<"\t::SPP hooks. skipping..\n";)
            continue;
        } 
        runOnFunction(&*Fn, M);

        if (Fn->getName().equals("main")) {
            dbg(errs()<<"----------main ------------\n";)
            dbg(errs()<<*Fn<<"\n";)
        }
    }
    dbg(errs()<<">>>>>>>>>>> Leaving SPPLTO........\n\n";)

    return true;

}

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

#define SPPDEBUG
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

static bool
doCallExternal(CallBase * CB)
{
    bool Changed= false;

    //Function* hook= (CB->getModule())->getFunction("__spp_cleantag");
    //assert(hook);
    Module * mod= CB->getModule();
    Type* vpty= Type::getInt8PtrTy(mod->getContext());
    FunctionType * fty= FunctionType::get(vpty, vpty, false);
    
    FunctionCallee hook = mod->getOrInsertFunction("__spp_cleantag", fty); 

    for (auto Arg = CB->arg_begin(); Arg != CB->arg_end(); ++Arg) {
        Value * ArgVal= cast<Value>(Arg);
        
        if (! (ArgVal->getType()->isPointerTy()
            || ArgVal->getType()->isAggregateType())) {
            dbg(errs()<<"\tNeither Pointer nor aggregated. Skipping..\n";)
            continue;
        }
        
        // TODO: move to opt pass later.
        //if (isSafePtr(From->stripPointerCasts())) {
        //    continue; 
        //}
        //if (ArgVal->getType()->isPointerTy()) {
        
        dbg(errs()<<"\t ptr_arg: "<< *ArgVal<<"\n";)
        IRBuilder<> B(CB);
        vector <Value*> arglist;

        Value* TmpPtr = B.CreateBitCast(ArgVal, hook.getFunctionType()->getParamType(0));
        arglist.push_back(TmpPtr);
        CallInst* Masked = B.CreateCall(hook, arglist);
        Value* Unmasked = B.CreateBitCast(Masked, ArgVal->getType()); 

        CB->setArgOperand(Arg - CB->arg_begin(), Unmasked);
        dbg(errs()<<"\t --> new_CB: "<< *CB<<"\n";)

        Changed = true;
        //}
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

    if (cfn->isDeclaration()) {
        dbg(errs()<<"  ---> external function call ...\n";)
        return  doCallExternal(cb);
    }
    
    dbg(errs()<<"  :: skip. Internal func\n";)
    return false; 
}


bool
SPPLTO::doCallBase (CallBase * cb)
{
    bool changed= false;
    errs()<<"CallBase:  "<<*cb<<"\n";

    Function * cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());

    if (cfn) {
        
        StringRef fname= cfn->getName();
        
        if (SPPFUNC(cfn)) {
            dbg(errs()<<"  :: skip. Hook Func call\n";)
            return false; 
        }
        // to be interposed at link time
        
        if (fname.equals("free") || isStringFuncName(fname)) {
            return false;
        }

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

            if (auto cb = dyn_cast<CallBase>(ins)) {
                changed= doCallBase(&*cb); 
            }
        }
    }
  return changed;
}

bool
SPPLTO::runOnModule (Module &M)
{
    //sppltopasscounter++;
    
    errs()<<"\n>>>>>>> Starting SPPLTO pass .....\n";
    
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
        errs()<<"Module: "<< M <<"\n";
        return false; /// DON'T DELETE ME!!
    }
     
    for (auto Fn= M.begin(); Fn!= M.end(); ++Fn) {

        dbg(errs()<<"\n** Fn: "<<Fn->getName()<<"\n";)

        if (Fn->isDeclaration()) {
            dbg(errs()<<"\t::decl. skipping..\n";)
            continue;
        } 
        if (SPPFUNC(Fn)) {
            dbg(errs()<<"\t::SPP hooks. skipping..\n";)
            continue;
        } 
        runOnFunction(&*Fn, M);

    }

    errs()<<">>>>>>>>>>> Leaving SPPLTO........\n\n";

    return true;

}

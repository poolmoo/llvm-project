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


#define DEBUG_TYPE "spplto"

#define SPPDEBUG
#ifdef SPPDEBUG
#  define dbg(x) x
#else
#  define dbg(x)
#endif

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

bool
SPPLTO::doCallBase (CallBase * cb)
{
  bool changed= false;
  errs()<<"CallBase:  "<<*cb<<"\n";

  Function * cfn= cb->getCalledFunction();
      
  if (cfn) {

    if (cfn->isDeclaration()) {
        errs()<<"  -> External\n";
    }
    else {
        errs()<<"  -> Internal\n";
    }
  
  }
  else {
    errs()<<"InvokeCall:\t"<<*cb<<"\n";
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
        return false; /// DON'T DELETE ME!!
    }

    dbg(errs()<<"************************************\n";)
    dbg(errs()<<"**   RunOnModule    ****************\n";)
    dbg(errs()<<"**   Mod Name: "<<M.getModuleIdentifier()<<"\n";)
     
    for (auto Fn= M.begin(); Fn!= M.end(); ++Fn) {

        dbg(errs()<<"** Fn: "<<Fn->getName()<<"\n";)

        // Jin: SPP hook functions are external functions, i guess (static lib?)

        if (Fn->isDeclaration()) {
            dbg(errs()<<"\t::decl.skipping..\n";)
            continue;
        }

        runOnFunction(&*Fn, M);

    }

    errs()<<">>>>>>>>>>> Leaving SPPLTO........\n\n";

    return true;

}

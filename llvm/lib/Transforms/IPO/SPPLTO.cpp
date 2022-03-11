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

#include <climits>
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
#include "llvm/Transforms/SPP/SPPUtils.h"

// #define DEBUG_TYPE "spplto"

//#define SPPDEBUG // Uncomment for debugging
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

  SPPLTO() : ModulePass(ID) 
  {
    initializeSPPLTOPass(*PassRegistry::getPassRegistry());
  }

  virtual bool runOnFunction (Function * F, Module &M);
  virtual bool runOnModule(Module &M) override;
  bool doCallBase (CallBase * ins);

  void getAnalysisUsage(AnalysisUsage &AU) const override {

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

ModulePass *llvm::createSPPLTOPass() 
{
  return new SPPLTO;
}

PreservedAnalyses
SPPLTOPass::run(Module &M, ModuleAnalysisManager &MAM) 
{
  return PreservedAnalyses::all();
}

static string 
demangleName(StringRef str)
{
    string result= "";
    int unmangledStatus;
    
    char *unmangledName = abi::__cxa_demangle(
        str.data(), nullptr, nullptr, &unmangledStatus);
    if (unmangledStatus == 0) 
    {
        string unmangledNameStr(unmangledName);
        result= unmangledNameStr;
    }
    return result;    
}

static bool
doCallFunc_LLVMDbg(CallBase *CB)
{
    dbg(errs() << ">>llvm.dbg.CB" << *CB << "\n";)

    MetadataAsValue* Arg= dyn_cast<MetadataAsValue>(CB->getOperand(0));
    assert(Arg);
    
    ValueAsMetadata* ArgMD= dyn_cast<ValueAsMetadata>(Arg->getMetadata());   
    assert(ArgMD);
    
    Value* ArgVal= ArgMD->getValue();   
    assert(ArgVal);
        
    if (!ArgVal->getType()->isPointerTy() || isa<Constant>(ArgVal)) {
        dbg(errs()<<">>llvm.dbg.CB: skipping.. Not PointerTy\n";)
        return false;
    }

    IRBuilder<> B(CB);
    vector <Value*> arglist;
    
    Module *mod = CB->getModule();
    Type *vpty = Type::getInt8PtrTy(mod->getContext());
    FunctionType *fty = FunctionType::get(vpty, vpty, false);
    FunctionCallee hook = 
        mod->getOrInsertFunction("__spp_cleantag_external", fty); 

    Value *TmpPtr = B.CreateBitCast(ArgVal, 
                hook.getFunctionType()->getParamType(0));
    arglist.push_back(TmpPtr);
    CallInst *Masked = B.CreateCall(hook, arglist);
    Value *Unmasked = B.CreateBitCast(Masked, ArgVal->getType()); 
    MetadataAsValue *MDAsVal= 
            MetadataAsValue::get(CB->getModule()->getContext(), 
                                 ValueAsMetadata::get(Unmasked));
    
    CB->setArgOperand(0, MDAsVal);
    dbg(errs() << ">>new_CB after masking: " << *CB << "\n";)
    
    return true;
}

static bool
doCallExternal(CallBase *CB)
{
    bool changed = false;

    // Skip tag cleaning for certain transaction functions
    if (CB->getCalledFunction() != NULL && 
        CB->getCalledFunction()->getName().contains("pmemobj_tx_add_range_direct")) 
    {
            return changed;
    }   

    Module *mod = CB->getModule();
    Type *vpty = Type::getInt8PtrTy(mod->getContext());
    FunctionType *fty = FunctionType::get(vpty, vpty, false);
    
    FunctionCallee hook = 
        mod->getOrInsertFunction("__spp_cleantag_external", fty); 

    for (auto Arg = CB->arg_begin(); Arg != CB->arg_end(); ++Arg) 
    {   
        Value *ArgVal = dyn_cast<Value>(Arg);
        if (!ArgVal) 
        {
            dbg(errs() << ">>Argument skipping.. Not a value\n";)
            continue;
        }
        
        /// Now we got a Value arg. 
        if (!ArgVal->getType()->isPointerTy()) 
        {
            dbg(errs()<<">>Argument skipping.. Not pointerType\n";)
            continue;
        }
 
        if (isa<Constant>(ArgVal)) 
        {
            dbg(errs()<<">>Argument skipping.. Constant\n";)
            continue; 
        } 
        
        // TODO: move to opt pass later.
        //if (isSafePtr(From->stripPointerCasts())) {
        //    continue; 
        //}
        
        IRBuilder<> B(CB);
        vector <Value*> arglist;

        Value *TmpPtr = B.CreateBitCast(ArgVal, 
                        hook.getFunctionType()->getParamType(0));
        arglist.push_back(TmpPtr);
        CallInst *Masked = B.CreateCall(hook, arglist);
        Value *Unmasked = B.CreateBitCast(Masked, ArgVal->getType()); 

        CB->setArgOperand(Arg - CB->arg_begin(), Unmasked);

        dbg(errs() << ">>new_CB after masking: " << *CB << "\n";)

        changed = true;
    }
    
    return changed;
}

static bool
doCallNonFunc(CallBase *cb)
{
    return doCallExternal(cb);
}

static bool
doCallFunction(CallBase *cb, Function *cfn)
{
    assert(cfn);
   
    // just checking..
    if (cfn->getName().startswith("llvm.dbg.") && 
        !cfn->getName().startswith("llvm.dbg.label")) 
    {
        return doCallFunc_LLVMDbg(cb); 
    }

    if (cfn->isDeclaration() ||
        StringRef(demangleName(cfn->getName())).equals("pmemobj_direct_inline") ||
        cfn->getName().contains("pmemobj_direct_inline") ||
        cfn->getName().contains("ZL21pmemobj_direct_inline7pmemoid"))
    {         
        dbg(errs() << ">>" << cfn->getName() << " external function call...\n";)
        return doCallExternal(cb);
    }
    
    //simple verification to avoid mistakes
    assert(!cfn->getName().contains("pmemobj_direct_"));    

    dbg(errs() << ">>" << cfn->getName() << " internal function call: skipping..\n";)
    return false; 
}


bool
SPPLTO::doCallBase(CallBase *cb)
{
    bool changed= false;
    dbg(errs() << ">>CallBase: "<<*cb<<"\n";)

    Function *cfn= dyn_cast<Function>(cb->getCalledOperand()->stripPointerCasts());

    if (cfn) 
    {
        StringRef fname = cfn->getName();
        dbg(errs() << ">>CalledFn: " << fname << " / " << demangleName(fname) << "\n";)

        // if it's SPP hook, do not do anything
        if (isSPPFuncName(fname)) 
        {
            dbg(errs() << ">>SPP hook fn call: skipping..\n";)
            return changed; 
        }        
        // if it's memory or string function, do not do anything
        if (isMemFuncName(fname) || isStringFuncName(fname)) 
        {
            dbg(errs() << ">>memory or string fn call: skipping..\n";)
            return changed;
        }
        // if it's memory intrinsic function, do not do anything
        if (dyn_cast<MemIntrinsic>(cb))
        {
            dbg(errs() << ">>LLVM memory intrinsic fn call: skipping..\n";)
            return changed;
        }

        changed = doCallFunction(cb, cfn);
    }
    else 
    {
        changed = doCallNonFunc(cb);
    }
    
    return changed;
}

bool
SPPLTO::runOnFunction(Function *FN, Module &M)
{
    bool changed = false;

    for (auto BB = FN->begin(); BB != FN->end(); ++BB) 
    {
        for (auto ins = BB->begin(); ins != BB->end(); ++ins ) 
        { 
            if (auto cb = dyn_cast<CallBase>(ins)) 
            {
                changed= doCallBase(&*cb); 
            }
        }
    }
  return changed;
}

bool
SPPLTO::runOnModule(Module &M)
{    
    errs() << ">>Starting SPPLTO pass\n";
    errs() << ">>" << __func__ << " : " << M.getModuleIdentifier() << "\n";
    
    /*
    * DO NOT DELETE the following lines,
    *   -- returning if 'main' doesnt exist)!!!
    * Deleting it causes unit test failures, and
    * LLVM errors - Immutable passes not initialised, since
    * it just exits without returning to LLVM pass manager.
    * LLVM just loses track of it, and emits errors.
    */

    if (!M.getFunction("main")) 
    {
        errs() << "!>ALERT: No main found in module\n";
        return false; /// DON'T DELETE ME!!
    }
     
    for (auto Fn = M.begin(); Fn != M.end(); ++Fn) 
    {
        dbg(errs() << ">>FName: " << Fn->getName() << "\n";)

        if (Fn->isDeclaration()) 
        {
            dbg(errs() << ">>declaration: skipping..\n";)
            continue;
        } 
        if (isSPPFuncName(Fn->getName())) // hook func names are not mangled.
        { 
            dbg(errs() << ">>SPP hooks: skipping..\n";)
            continue;
        }
        if (isMemFuncName(Fn->getName())) 
        {
            dbg(errs() << ">>Memory func: skipping..\n";)
            continue;
        } 

        runOnFunction(&*Fn, M);
    }

    errs() << ">>Leaving SPPLTO\n";

    return true;
}

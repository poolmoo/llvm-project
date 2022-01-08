//===----- miu_elimhook.cpp - Bounds Checker in SPP transformation pass -----===//
#define DEBUG_TYPE "miu_elimhook"

#include <llvm/Pass.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/Casting.h>
#include <llvm/IR/Dominators.h>
#include <llvm/ADT/DepthFirstIterator.h>
#include <llvm/ADT/SmallSet.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/IR/MDBuilder.h>
#include <llvm/IR/Metadata.h>
#include <llvm/Analysis/MemoryBuiltins.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Analysis/LoopPass.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Transforms/Utils/Local.h>

#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <tr1/memory>
#include <tr1/tuple>
#include <assert.h>

#include "llvm/Transforms/Miu/MiuUtils.h"

#define SPPFUNC(F)  (F->getName().startswith("__spp"))

using namespace llvm;

class ModInfo {
    Module * M= nullptr;
    TargetLibraryInfo* TLI = nullptr;
    const DataLayout *DL;
    
    StringRef HookPrefix; 

    public:

    SPPPass(Module* M) {
        this->M = M;
    }
    
    void setHookNamePrefix (StringRef str) {
        this->HookPrefix = str;
    }
    
    void setDL(const DataLayout *DL) {
        this->DL = DL;
    }
    void setScalarEvolution(ScalarEvolution* SE) {
        this->SE = SE;
    }
    virtual bool visitFunc (Function * fn);
    virtual bool visitBasicBlock (BasicBlock * bb);
};

namespace {

bool
ModInfo::isHookCallBase (Value * ptrop) 
{
    assert(ptrop);

    if (!isa<CallBase>(ptrop->stripPointerCasts())) {
        return nullptr;
    }

    CallBase * cb= cast<CallBase>(ptrop->stripPointerCasts());

    if (!isa<Function>(cb->getCalledOperand()->stripPointerCasts())) {
        return nullptr;
    }
    Function * hook= cast<Function>(cb->getCalledOperand()->stripPointerCasts()); 
    assert (hook);

    if (!hook->startswith(this->HookPrefix)) {
        return nullptr;
    }
    // Now the pointer operand is call to a hook.
    // if it is a redundant hook, restore its original ptr
    
    return true;
}

// ptrop: pointer operand of store/load, or arg of external func call
static Value * 
collectRedundants (Value * ptrop, std::set & <Value*> myset)
{
    Value * OrigPtr= nullptr;

    CallBase * cb= dyn_cast<CallBase>(ptrop->stripPointerCasts()); 
    assert(cb);

    Function * hook= cb->getCalledFunction()->stripPointerCasts(); 
    assert(hook);

    StringRef name= hook->getName();

    if (name.equals("__spp_cleantag")) {
        assert(hook->getFunctionType()->getNumParams()==1);
        assert(!hook->getFunctionType()->getReturnType()->isVoidTy());
        
        Value * ArgOp= cb->getArgOperand(0);
        Value * Tmp= ArgOp->stripPointerCasts();      
        
        // SPP instruments only heap objects
        if (!isa<Constant>(Tmp) && !isa<AllocaInst>(Tmp)) { 
            return nullptr; 
        }
        
        OrigPtr= Tmp;
            
        myset.insert(cb); 
        
        if (isa<CastInst>(ptrop) && ptrop->getNumUses()==1) {
            myset.insert(ptrop);
        }
        if (isa<CastInst>(ArgOp) && ArgOp->getNumUses()==1) {
            myset.insert(); 
        }
    }
    else {
        ;
    }
    
    return OrigPtr;
}


bool
ModInfo::visitFunc (Function * fn)
{
    bool changed = false;
    
    // Remove redundant tag cleaning
    // i.e. replace hook func calls (tag cleaning) with original ptr.
    
    for (auto &I : instructions(fn)) {                                 
        // NOTE: remove after integrating the LTO pass
        
        std::set<Value*> restoreMe;
        
        if (StoreInst * SI = dyn_cast<StoreInst>(&I) ||
            LoadInst * LI = dyn_cast<LoadInst>(&I)) {
        
            Value * ptrop= SI?  SI->getPointerOperand(): 
                                LI->getPointerOperand();

            if (!(isHookCallBase(ptrop))) continue;
            
            Value * origOp= collectRedundants(ptrop, restoreMe);

            if (SI) {
                SI->setOperand(0,);
            }
            else {

            }
        }
        else if (auto* CB = dyn_cast<CallBase>(&I)) {
        }
    }
     
    return changed;
}

class MiuElimRedundantHook : public ModulePass {
    public:
        static char ID;
        MiuElimRedundantHook() : ModulePass(ID) { }
        
        virtual bool runOnModule(Module &M); 

};

virtual bool 
MiuElimRedundantHook::runOnModule(Module &M) {
    
    errs() << "\n>>>>>> Running_ElimRemoveHook_Pass >>>>>>>>> \n";
    errs() << "Mod Name: "<< M.getModuleIdentifier() <<"\n\n";
    
    ModInfo mod (&M);
    mod.setHookNamePrefix("__spp_");
    mod.setDL(&M.getDataLayout());

    for (auto F = M.begin(); F! = M.end(); ++F) {
        
        errs()<<"\n-- F: "<<F->getName()<<" -----------\n";

        if (F->isDeclaration() || SPPFUNC(F)) {
            errs()<<"  SKIP: decl or spp hook\n";
            continue;
        }
        errs()<<"  Processing....\n";
        changed = mod.visitFunc(&*F);
    }
    
    errs()<<"\n>>>>>> Exiting Running_ElimRemoveHook_Pass >>>>>>>>\n\n";
    return Changed;

}

    char MiuElimRedundantHook::ID = 0;
    static RegisterPass<MiuElimRedundantHook> X("miu_elimhook", "Eliminate Redundant Hook Pass", false, false);

    static void registerPass(const PassManagerBuilder &,
            legacy::PassManagerBase &PM) {
        PM.add(new MiuElimRedundantHook());
    }
    //apply the module pass at this phase because EarlyAsPossible can cause UB
    static RegisterStandardPasses
        RegisterMyPass(PassManagerBuilder::EP_ModuleOptimizerEarly,
                registerPass);

    //to keep the pass available even in -O0
    static RegisterStandardPasses
        RegisterMyPass_non_opt(PassManagerBuilder::EP_EnabledOnOptLevel0,
                registerPass);

}

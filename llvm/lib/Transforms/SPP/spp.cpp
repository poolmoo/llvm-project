//===----- spp.cpp - Bounds Checker in SPP transformation pass -----===//
// #define DEBUG_TYPE "spp"

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
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>
#include <llvm/Analysis/AssumptionCache.h>
#include <llvm/Analysis/LoopAccessAnalysis.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/LoopIterator.h>
#include <llvm/Analysis/LoopPass.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Transforms/Utils/Local.h>
#include "llvm/Transforms/SPP/SPPUtils.h"

#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <tr1/memory>
#include <tr1/tuple>
#include <assert.h>

//#define SPP_PRINT_DEBUG // Uncomment for debugging
#ifdef SPP_PRINT_DEBUG
#  define dbg(x) x
#else
#  define dbg(x) 
#endif

using namespace llvm;
// using namespace std; // Jin: this is NOT recommended..

namespace {
    
    static int getOpIdx(Instruction* I, Value* Ptr) 
    {
        for (auto Op = I->op_begin(), OpEnd = I->op_end(); Op != OpEnd; ++Op)
        {
            if (Op->get() == Ptr)
                return Op->getOperandNo();
        }
        return -1;
    }

    class SPPPass {

        Module* M = nullptr;
        TargetLibraryInfo* TLI = nullptr;
        ScalarEvolution* SE = nullptr;

        const DataLayout *DL;

        SmallSet<Function*, 32> varargFuncs;
        DenseMap<Constant*, Constant*> globalUses;
        DenseMap<Instruction*, Instruction*> optimizedMemInsts;
        //TODO: Debuglist.

    public:
        
        std::vector<Instruction*> GEP_hooked_CBs;
        std::vector<Instruction*> GEP_skipped_CBs;
    
        SPPPass(Module* M) 
        {
            this->M = M;
        }

        void setScalarEvolution(ScalarEvolution *SE) 
        {
            this->SE = SE;
        }

        void setDL(const DataLayout *DL) 
        {
            this->DL = DL;
        }
        
        void visitGlobals() 
        {
            SmallVector<GlobalVariable*, 16> globals;
            for (auto G = M->global_begin(), Gend = M->global_end(); G != Gend; ++G) 
            {
                globals.push_back(&*G);
            }
        }
        
        bool isTagUpdated(GetElementPtrInst *Gep)
        {
            for (auto user = Gep->user_begin(); user != Gep->user_end(); ++user) 
            {
                CallBase *GepCBUser = dyn_cast<CallBase>(user->stripPointerCasts());
                if (!GepCBUser) 
                { 
                    continue; 
                }

                Function *FN = GepCBUser->getCalledFunction();
                if (!FN) 
                {  
                    continue;
                }

                if (FN->getName().startswith("__spp_update")) 
                {
                    return true;
                }
                
                dbg(errs() << "!>ALERT: missed function callBase!\n";)
            }
            
            return false;
        }

        bool isDefinedLater (Instruction *Op, Instruction *userI)
        {
            Function *F = userI->getFunction();
            bool found = false;

            for (auto & Iter : instructions(F)) 
            {                
                if (&Iter == userI) 
                {
                    //has to be found first
                    found= true;
                }
                else if (&Iter == Op) 
                {
                    //has to be found afterwards
                    assert(found);
                    return true;
                }
            }
            assert(found);
            return found;
        }
        
        bool isMissedGep(GetElementPtrInst *gep, Instruction *userI)
        {
            if (isTagUpdated(gep)) 
            {
                return false;
            }
            if (gep->hasAllZeroIndices()) 
            {
               return false;
            }
           
            if (isDefinedLater(gep, userI)) 
            {
                return false;
            }

            return true;
        }
        bool instrGepOperand(Instruction *userI, GetElementPtrInst *gep) 
        {            
            IRBuilder<> B(gep);
            
            SmallVector <Type*, 2> tlist;
            
            Type *RetArgTy = Type::getInt8PtrTy(M->getContext());
            Type *Arg2Ty = Type::getInt64Ty(M->getContext());
            tlist.push_back(RetArgTy);
            tlist.push_back(Arg2Ty);
            
            FunctionType *hookfty = FunctionType::get(RetArgTy, tlist, false);
            FunctionCallee hook = M->getOrInsertFunction("__spp_update_pointer", hookfty);
            
            SmallVector <Value*, 2> arglist;
            Value *TmpPtr = B.CreateBitCast(gep, hook.getFunctionType()->getParamType(0));
            Value *GepOff = EmitGEPOffset(&B, *DL, gep);
            arglist.push_back(TmpPtr);
            arglist.push_back(GepOff);
            CallInst *Masked = B.CreateCall(hook, arglist);
            Value *NewPtr = B.CreatePointerCast(Masked, gep->getType());

            int OpIdx = getOpIdx(userI, gep);
            userI->setOperand(OpIdx, NewPtr);            
            return true;
        }
        
        bool replaceFoldedGepOp(Instruction *Ins)
        {
            bool changed= false;

            for (auto Op = Ins->op_begin(); Op != Ins->op_end(); ++Op) 
            {
                Instruction *MyOp= dyn_cast<Instruction>(Op);
                if (!MyOp) 
                {
                    dbg(errs() << ">>" << __func__ << "op: not inst\n";) 
                    continue;
                }
                dbg(errs() << ">>" << __func__ << " folded op: " << **Op << "\n";) 
                
                // only one-depth for now.. 
                // otherwise we are screwed.
                if (!isa<GetElementPtrInst>(MyOp->stripPointerCasts())) 
                {
                    continue;
                }

                GetElementPtrInst *GepOp= cast<GetElementPtrInst>(MyOp->stripPointerCasts()); 
                if (isMissedGep(GepOp, Ins)) 
                {
                    dbg(errs() << "!>ALERT: missed GepOp: " << *GepOp << " in " << *Ins \
                                << " of " << Ins->getFunction()->getName() << "\n";)

                    if (GepOp == MyOp) 
                    {
                        changed = instrGepOperand(MyOp, GepOp);
                    }
                    else 
                    {
                        changed = instrGepOperand(Ins, GepOp);
                    }
                } 
            }
            return changed;
        }
        
        
        /*
        * Get the insert point after the specified instruction. For non-terminators
        * this is the next instruction. For `invoke` intructions, create a new
        * fallthrough block that jumps to the default return target, and return the
        * jump instruction.
        */
        Instruction* getInsertPointAfter(Instruction *I) 
        {
            if (InvokeInst *Invoke = dyn_cast<InvokeInst>(I)) 
            {
                BasicBlock *Dst = Invoke->getNormalDest();
                BasicBlock *NewBlock = BasicBlock::Create(I->getContext(),
                        "invoke_insert_point", Dst->getParent(), Dst);
                BranchInst *Br = BranchInst::Create(Dst, NewBlock);
                Invoke->setNormalDest(NewBlock);

                /* Patch references in PN nodes in original successor */
                BasicBlock::iterator It(Dst->begin());
                while (PHINode *PN = dyn_cast<PHINode>(It)) 
                {
                    int i;
                    while ((i = PN->getBasicBlockIndex(Invoke->getParent())) >= 0)
                    {
                        PN->setIncomingBlock(i, NewBlock);
                    }
                    It++;
                }
                return Br;
            }
            if (isa<PHINode>(I))
            {
                return &*I->getParent()->getFirstInsertionPt();
            }
           
            assert(!Instruction::isTerminator(I->getOpcode()));
            return &*std::next(BasicBlock::iterator(I));
        }
        
        bool instrMemIntr(MemIntrinsic *mi)
        {
            bool changed = false;
            
            // create hook prototype
            Type *RetArgTy = Type::getInt8PtrTy(M->getContext());
            Type *Arg2Ty = Type::getInt64Ty(M->getContext());
            SmallVector <Type*, 2> tlist;
            tlist.push_back(RetArgTy);
            tlist.push_back(Arg2Ty);
             
            FunctionType *hookfty = FunctionType::get(RetArgTy, tlist, false);
            FunctionCallee hook = M->getOrInsertFunction("__spp_memintr_check_and_clean", hookfty);

            if (MemCpyInst *MCI = dyn_cast<MemCpyInst>(mi))
            {
                Value *Dest = MCI->getRawDest();
                Value *Src = MCI->getRawSource();
                Value *Length = MCI->getLength();
                
                dbg(errs() << ">>MCI " << *Dest << " | " << *Src << " | " << *Length   << "\n";)

                IRBuilder<> B(MCI);
                std::vector <Value*> arglist;

                Value *DestPtr = B.CreateBitCast(Dest, hook.getFunctionType()->getParamType(0));
                Value *SrcPtr = B.CreateBitCast(Src, hook.getFunctionType()->getParamType(0));
                Value *IntOff = B.CreateSExt(Length, hook.getFunctionType()->getParamType(1));
                
                std::vector<Value*> dest_args;
                dest_args.push_back(DestPtr);
                dest_args.push_back(IntOff);
                CallInst *DestChecked = B.CreateCall(hook, dest_args);          
                Value *DestCleaned = B.CreatePointerCast(DestChecked, Dest->getType());

                std::vector<Value*> src_args;
                src_args.push_back(SrcPtr);
                src_args.push_back(IntOff);
                CallInst *SrcChecked = B.CreateCall(hook, src_args);          
                Value *SrcCleaned = B.CreatePointerCast(SrcChecked, Src->getType());

                MCI->setDest(DestCleaned);
                MCI->setSource(SrcCleaned);          

                changed = true;
            }
            else if (MemMoveInst *MMI = dyn_cast<MemMoveInst>(mi))
            {
                Value *Dest = MMI->getRawDest();
                Value *Src = MMI->getRawSource();
                Value *Length = MMI->getLength();
                dbg(errs() << ">>MMI " << *Dest << " | " << *Src << " | " << *Length   << "\n";)

                IRBuilder<> B(MMI);
                std::vector <Value*> arglist;

                Value *DestPtr = B.CreateBitCast(Dest, hook.getFunctionType()->getParamType(0));
                Value *SrcPtr = B.CreateBitCast(Src, hook.getFunctionType()->getParamType(0));
                Value *IntOff = B.CreateSExt(Length, hook.getFunctionType()->getParamType(1));
                
                std::vector<Value*> dest_args;
                dest_args.push_back(DestPtr);
                dest_args.push_back(IntOff);
                CallInst *DestChecked = B.CreateCall(hook, dest_args);          
                Value *DestCleaned = B.CreatePointerCast(DestChecked, Dest->getType());

                std::vector<Value*> src_args;
                src_args.push_back(SrcPtr);
                src_args.push_back(IntOff);
                CallInst *SrcChecked = B.CreateCall(hook, src_args);          
                Value *SrcCleaned = B.CreatePointerCast(SrcChecked, Src->getType());

                MMI->setDest(DestCleaned);
                MMI->setSource(SrcCleaned);          

                changed = true;
            }
            else if (MemSetInst *MSI = dyn_cast<MemSetInst>(mi))
            {
                Value *Dest = MSI->getRawDest();
                Value *Length = MSI->getLength();
                dbg(errs() << ">>MSI " << *Dest << " | " << *Src << " | " << *Length   << "\n";)

                IRBuilder<> B(MSI);
                std::vector <Value*> arglist;

                Value *DestPtr = B.CreateBitCast(Dest, hook.getFunctionType()->getParamType(0));
                Value *IntOff = B.CreateSExt(Length, hook.getFunctionType()->getParamType(1));
                
                std::vector<Value*> dest_args;
                dest_args.push_back(DestPtr);
                dest_args.push_back(IntOff);
                CallInst *DestChecked = B.CreateCall(hook, dest_args);          
                Value *DestCleaned = B.CreatePointerCast(DestChecked, Dest->getType());

                MSI->setDest(DestCleaned);       

                changed = true;
            }
            return changed;
        }

        bool instrGep(GetElementPtrInst *Gep) 
        {
            IRBuilder<> B(getInsertPointAfter(Gep));
            std::vector<User*> Users(Gep->user_begin(), Gep->user_end());
                        
            /* No effect on ptr means no effect on size. */
            if (Gep->hasAllZeroIndices()) 
            {
                dbg(errs() << ">>GEP: Zero Indices.. skipping...\n";)
                return false;
            }
                    
            /* We want to skip GEPs on vtable stuff, as they shouldn't be able to
            * overflow, and because they don't have metadata normally negative
            * GEPs fail on these. */
            /*
            if (isVtableGep(Gep))
                return false;
            */

            /* TODO: we cannot support GEPs operating on vectors. */
            if (Gep->getType()->isVectorTy()) 
            {
                errs() << ">>GEP:Warning: ignoring GEP on vector: " << *Gep << "\n";
                return false;
            }

            //get the GEP offset
            Value *GepOff = EmitGEPOffset(&B, *DL, Gep);
           
            // create hook prototype
            Type *RetArgTy = Type::getInt8PtrTy(M->getContext());
            Type *Arg2Ty = Type::getInt64Ty(M->getContext());
            SmallVector <Type*, 2> tlist;
            tlist.push_back(RetArgTy);
            tlist.push_back(Arg2Ty);
             
            FunctionType *hookfty = FunctionType::get(RetArgTy, tlist, false);
            FunctionCallee hook = M->getOrInsertFunction("__spp_updatetag", hookfty);

            Value *TmpPtr = B.CreateBitCast(Gep, hook.getFunctionType()->getParamType(0));
            Value *IntOff = B.CreateSExt(GepOff, hook.getFunctionType()->getParamType(1));
            
            std::vector<Value*> args;
            args.push_back(TmpPtr);
            args.push_back(IntOff);
            
            CallInst *Masked = B.CreateCall(hook, args);          
            Value *UpdatedPtr = B.CreatePointerCast(Masked, Gep->getType());

            for (auto User : Users) 
            {
                Instruction *iUser= dyn_cast<Instruction>(User);
                assert(iUser);
                User->setOperand(getOpIdx(iUser, Gep), UpdatedPtr);
                dbg(errs() << ">>GEP updated instruction: " << *iUser << " with " \
                            << *UpdatedPtr->stripPointerCasts() << "\n";)
            }
            
            return true;

        }
        
        bool instrumentLoadOrStore(Instruction *I) 
        {            
            IRBuilder<> B(I);
            bool isStore = isa<StoreInst>(*I);
            Value* Ptr = isStore
                ? cast<StoreInst>(I)->getPointerOperand()
                : cast<LoadInst>(I)->getPointerOperand();
            
            assert(Ptr->getType()->isPointerTy()); 
            
            dbg(errs() << ">>"__func__ << "Ptr: " << *Ptr << " stripped: " \
                        << *Ptr->stripPointerCasts() << "\n";)
            
            if (isa<GetElementPtrInst>(Ptr->stripPointerCasts())) 
            {
                assert(!isMissedGep(cast<GetElementPtrInst>(Ptr->stripPointerCasts()), I));
            } 
             
            Type *RetArgTy = Type::getInt8PtrTy(M->getContext());
            SmallVector <Type*, 1> tlist;
            tlist.push_back(RetArgTy);
            FunctionType *hookfty = FunctionType::get(RetArgTy, RetArgTy, false);
            FunctionCallee hook = M->getOrInsertFunction("__spp_checkbound", hookfty);

            Value *TmpPtr = B.CreateBitCast(Ptr, hook.getFunctionType()->getParamType(0));
            CallInst *Masked = B.CreateCall(hook, TmpPtr);
            Value *NewPtr = B.CreatePointerCast(Masked, Ptr->getType());

            int OpIdx = getOpIdx(I, Ptr);
            I->setOperand(OpIdx, NewPtr);
            dbg(errs() << ">> updated ld/st: " << *I << "\n";)
            
            return true;
        }
        
        bool visitFunc(Function* F) 
        {
            bool changed = false;

            for (auto BI= F->begin(); BI!= F->end(); ++BI) 
            {
                BasicBlock *BB = &*BI; 
                Instruction *sucInst = &*(BB->begin());

                for (auto II = BB->begin(); II != BB->end(); ++II) 
                {    
                    Instruction *Ins= &*II;

                    if (Ins != sucInst) 
                    {
                        dbg(errs() << "<<added_by_instrumentation: " << *Ins << " skipping\n";)
                        continue;
                    }

                    sucInst = getNextInst(Ins);
                     
                    changed = replaceFoldedGepOp(Ins);
                    
                    if (isa<LoadInst>(Ins) || isa<StoreInst>(Ins)) 
                    {
                        changed = instrumentLoadOrStore(Ins);
                    }
                    else if (auto *Gep = dyn_cast<GetElementPtrInst>(Ins)) 
                    {
                        /* GEPs handling --- Apply the arithmetic to the top tag part*/
                        changed = instrGep(Gep);
                    }
                    else if (auto *memIntr = dyn_cast<MemIntrinsic>(Ins))
                    {
                        /* LLVM memory intrinsics handling */
                        /* these are not wrapped and should be checked before cleaned */
                        dbg(errs() << ">>LLVM memory intrinsic fn call:" << memIntr->getName() << " checking..\n";)
                        changed = instrMemIntr(memIntr);
                    }
                }
            } //endof forloop

            return changed;
        }
        
    };
    
    class SPPModule : public ModulePass {
    public:
        static char ID;

        SPPModule() : ModulePass(ID) { }

        virtual bool runOnModule(Module& M) override
        {
            errs() << ">>Running_SPP_Module_Pass start...\n";
            dbg(errs() << ">>" << __func__ << " : " << M.getModuleIdentifier() << "\n";)
            
            SPPPass Spp(&M);
            Spp.setDL(&M.getDataLayout()); //init the data layout

            bool changed = false;
           
            //Visit the functions to clear the appropriate ptr before external calls
            for (auto F = M.begin(), Fend = M.end(); F != Fend; ++F) 
            {
                dbg(errs() << ">>Func : " << F->getName() << "\t";)
                
                if (F->isDeclaration()) 
                {
                    dbg(errs() << "External.. skipping\n";)
                    continue; 
                }
                if (isSPPFuncName(F->getName()))
                {
                    dbg(errs() << "SPP hook func.. skipping\n";)
                    continue; 
                }

                dbg(errs() << "Internal.. processing\n";)
                changed = Spp.visitFunc(&*F);             
            }
            errs() << ">>Running_SPP_Module_Pass exiting...\n";
            return changed;
        }
        
    };

    char SPPModule::ID = 0;
    static RegisterPass<SPPModule> X("spp", "Safe Persistent Pointers Pass", false, false);

    static void registerPass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) 
    {
        PM.add(new SPPModule());
    }
    //apply the module pass at this phase because EarlyAsPossible can cause UB
    static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_ModuleOptimizerEarly,
                   registerPass);

    //to keep the pass available even in -O0
    static RegisterStandardPasses
    RegisterMyPass_non_opt(PassManagerBuilder::EP_EnabledOnOptLevel0,
                   registerPass);

} // endof namespace

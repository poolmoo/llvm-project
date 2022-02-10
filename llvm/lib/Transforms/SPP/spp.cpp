//===----- spp.cpp - Bounds Checker in SPP transformation pass -----===//
#define DEBUG_TYPE "spp"

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
#include "llvm/Transforms/Miu/MiuUtils.h"

#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <tr1/memory>
#include <tr1/tuple>
#include <assert.h>

#define SPPFUNC(F)  (F->getName().startswith("__spp"))

//#define SPP_PRINT_DEBUG // Uncomment for debugging
#ifdef SPP_PRINT_DEBUG
#  define dbg(x) x
#else
#  define dbg(x) 
#endif

using namespace llvm;

namespace {
    
    static int getOpIdx(Instruction* I, Value* Ptr) {
        for (auto Op = I->op_begin(), OpEnd = I->op_end(); Op != OpEnd; ++Op) {
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
        SmallSet<Function*, 32> externalFuncs;
        SmallSet<Value*, 32> pmemPtrs;
        //TODO: Debuglist.

    public:
        
        std::vector<Instruction*> GEP_hooked_CBs;
        std::vector<Instruction*> GEP_skipped_CBs;
    
        SPPPass(Module* M) {
            this->M = M;
        }

        void setScalarEvolution(ScalarEvolution* SE) {
            this->SE = SE;
        }

        void setDL(const DataLayout *DL) {
            this->DL = DL;
        }
        
        void visitGlobals() {
            SmallVector<GlobalVariable*, 16> globals;
            for (auto G = M->global_begin(), Gend = M->global_end(); G != Gend; ++G) {
                globals.push_back(&*G);
            }
        }
        
        bool isTagUpdated (GetElementPtrInst * Gep)
        {
            bool isUpdated= false;

            for (auto user= Gep->user_begin(); user!=Gep->user_end(); ++user) {
                dbg(errs()<<"  User: "<<**user<<"\n";)
                CallBase * GepCBUser= dyn_cast<CallBase>(user->stripPointerCasts());
                if (!GepCBUser) { continue; }

                Function * FN= GepCBUser->getCalledFunction();
                if (!FN) {  continue;   }

                dbg(errs()<<"  --> fun_callBase!n";)

                if (FN->getName().startswith("__spp_update")) {
                    dbg(errs()<<"  --> HOOK_callBase! skip..\n";)
                    return true;
                }
                dbg(errs()<<"  --> normal_callBase! skip..\n";)
            }
            
            return isUpdated;
        }

        bool isDefinedLater (Instruction * Op, Instruction * userI)
        {
            Function * F= userI->getFunction();
            bool idxUserI= false;;

            dbg(errs()<<"isdefined_GepOp: "<<*Op<<"\n";)
            dbg(errs()<<"isdefined_userI: "<<*userI<<"\n";)

            for (auto & Iter : instructions(F)) {
                dbg(errs()<<"  Iter_: "<<Iter<<"\n";)
                
                if (&Iter==userI) {
                    dbg(errs()<<"  ---> found userI: "<<*userI<<"\n";)
                    idxUserI= true;
                }
                else if (&Iter==Op) {
                    assert(idxUserI); 
                    dbg(errs()<<"  ---> found GepOp: "<<*Op<<"\n";)
                    dbg(errs()<<"  ---> ! GepOp_is_defined_later.";)
                    return true;
                }
            }
            assert(idxUserI);
            
            return idxUserI;
        }
        
        bool isMissedGep (GetElementPtrInst * gep, Instruction * userI)
        {
            if (isTagUpdated(gep)) {
                return false;
            }
            if (gep->hasAllZeroIndices()) {
               return false;; 
            }
           
            if (isDefinedLater(gep, userI)) {
                return false;
            }
            dbg(errs()<<"error:missedGep "<<*gep<<"\n";)
            return true;
        }
        bool instrGepOperand(Instruction * userI, GetElementPtrInst * gep) {
            
            IRBuilder<> B(gep);
            
            SmallVector <Type*, 2> tlist;
            
            Type* RetArgTy= Type::getInt8PtrTy(M->getContext());
            Type* Arg2Ty= Type::getInt64Ty(M->getContext());
            tlist.push_back(RetArgTy);
            tlist.push_back(Arg2Ty);
            
            FunctionType * hookfty= FunctionType::get(RetArgTy, tlist, false);
            dbg(errs()<<"temp_FTy: "<<*hookfty<<"\n";)
            FunctionCallee hook= M->getOrInsertFunction("__spp_update_pointer", hookfty);
            
            SmallVector <Value*, 2> arglist;
            Value* TmpPtr = B.CreateBitCast(gep, hook.getFunctionType()->getParamType(0));
            Value *GepOff = EmitGEPOffset(&B, *DL, gep);
            arglist.push_back(TmpPtr);
            arglist.push_back(GepOff);
            CallInst* Masked = B.CreateCall(hook, arglist);
            Value* NewPtr = B.CreatePointerCast(Masked, gep->getType());

            int OpIdx = getOpIdx(userI, gep);
            userI->setOperand(OpIdx, NewPtr);
            dbg(errs()<<"new_User: "<<*userI<<"\n";)
            dbg(errs()<<"new_opCB: "<<*Masked<<"\n";)
            
            return true;
        }
        
        bool replaceFoldedGepOp(Instruction * Ins)
        {
            bool changed= false;
            dbg(errs()<<"numOp: "<<Ins->getNumOperands()<<"\n";)

            for (auto Op = Ins->op_begin(); Op != Ins->op_end(); ++Op) {
                Instruction * MyOp= dyn_cast<Instruction>(Op);
                if (!MyOp) {
                    dbg(errs()<<"op: not inst\n";) 
                    continue;
                }
                dbg(errs()<<"op: "<< **Op <<"\n";) 
                
                // only one-depth.. otherwise we are screwed.
                //
                
                if (!isa<GetElementPtrInst>(MyOp->stripPointerCasts())) {
                    continue;
                }
                GetElementPtrInst * GepOp= cast<GetElementPtrInst>(MyOp->stripPointerCasts()); 
                if (isMissedGep(GepOp, Ins)) {
                    dbg(errs()<<"error: isMissedGep!!..........\n";)
                    dbg(errs()<<"--> GepOp: "<<*GepOp<<"\n";)
                    dbg(errs()<<"--> userI: "<<*Ins<<"\n";)
                    dbg(errs()<<"func: "<<Ins->getFunction()->getName()<<"\n";)
                    dbg(errs()<<*Ins->getFunction()<<"\n";)

                    if (GepOp == MyOp) {
                        changed= instrGepOperand(MyOp, GepOp);
                    }
                    else {
                        changed= instrGepOperand(Ins, GepOp);
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
        Instruction *getInsertPointAfter(Instruction *I) {
            if (InvokeInst *Invoke = dyn_cast<InvokeInst>(I)) {
                BasicBlock *Dst = Invoke->getNormalDest();
                BasicBlock *NewBlock = BasicBlock::Create(I->getContext(),
                        "invoke_insert_point", Dst->getParent(), Dst);
                BranchInst *Br = BranchInst::Create(Dst, NewBlock);
                Invoke->setNormalDest(NewBlock);

                /* Patch references in PN nodes in original successor */
                BasicBlock::iterator It(Dst->begin());
                while (PHINode *PN = dyn_cast<PHINode>(It)) {
                    int i;
                    while ((i = PN->getBasicBlockIndex(Invoke->getParent())) >= 0)
                        PN->setIncomingBlock(i, NewBlock);
                    It++;
                }
                return Br;
            }
            if (isa<PHINode>(I))
                return &*I->getParent()->getFirstInsertionPt();
           
            assert(!Instruction::isTerminator(I->getOpcode()));
            return &*std::next(BasicBlock::iterator(I));
        }
        

        bool instrGep(GetElementPtrInst* Gep) {
            IRBuilder<> B(getInsertPointAfter(Gep));
            std::vector<User*> Users(Gep->user_begin(), Gep->user_end());
            
            dbg(errs()<<"-> GEP\n";)
            
            /* No effect on ptr means no effect on size. */
            if (Gep->hasAllZeroIndices()) {
                dbg(errs()<<"--> allZeroIndices. Skip...\n";)
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
            if (Gep->getType()->isVectorTy()) {
                errs() << "Warning: ignoring GEP on vector: " << *Gep << "\n";
                return false;
            }

            dbg(errs()<<"NumUses: "<<Gep->getNumUses() <<"\n";)

            //get the GEP offset

            Value *GepOff = EmitGEPOffset(&B, *DL, Gep);
           
            // create hook prototype
            
            Type* RetArgTy= Type::getInt8PtrTy(M->getContext());
            Type* Arg2Ty= Type::getInt64Ty(M->getContext());
            SmallVector <Type*, 2> tlist;
            tlist.push_back(RetArgTy);
            tlist.push_back(Arg2Ty);
            //tlist.push_back(RetArgTy); // SPP_DEBUG ///////
             
            FunctionType * hookfty= FunctionType::get(RetArgTy, tlist, false);
             
            //FunctionCallee hook= M->getOrInsertFunction("__spp_updatetag_DEBUG", hookfty);
            FunctionCallee hook= M->getOrInsertFunction("__spp_updatetag", hookfty);

            Value* TmpPtr = B.CreateBitCast(Gep, hook.getFunctionType()->getParamType(0));
            Value* IntOff = B.CreateSExt(GepOff, hook.getFunctionType()->getParamType(1));
            //Value* TmpPtrOp = B.CreateBitCast(Gep->getPointerOperand(), hook.getFunctionType()->getParamType(2)); // DEBUG 
            
            std::vector<Value*> args;
            args.push_back(TmpPtr);
            args.push_back(IntOff);
            //args.push_back(TmpPtrOp); // SPP_DEBUG //////////
            
            CallInst* Masked = B.CreateCall(hook, args);
            dbg(errs() << "CallInst =" << *Masked << "\n";)
            dbg(errs() << "    Arg0 : " << *TmpPtr << "\n";)
            dbg(errs() << "    Arg0': " << *TmpPtr->stripPointerCasts() << "\n";)
            dbg(errs() << "    Arg1 :" << *IntOff << "\n";)
            dbg(errs() << "    Arg2 :" << *TmpPtrOp->stripPointerCasts() << "\n";) // SPP_DEBUG /// 
            
            Value* UpdatedPtr = B.CreatePointerCast(Masked, Gep->getType());
            //errs() << "CreatePtrCast =" << *UpdatedPtr << "\n";

            for (auto User : Users) {
                Instruction * iUser= dyn_cast<Instruction>(User);
                assert(iUser);
                dbg(errs()<<"\noldGepUser_: "<<*iUser<<"\n";)
                User->setOperand(getOpIdx(iUser, Gep), UpdatedPtr);
                dbg(errs()<<"newGepUser_: "<<*iUser<<"\n";)
                dbg(errs()<<"  newGepOp_: "<<*UpdatedPtr->stripPointerCasts()<<"\n";)
            }
            
            return true;

        }
        
        bool instrumentLoadOrStore(Instruction * I) {
            
            dbg(errs()<<"-> SL\n";)
            
            IRBuilder<> B(I);
            bool isStore = isa<StoreInst>(*I);
            Value* Ptr = isStore
                ? cast<StoreInst>(I)->getPointerOperand()
                : cast<LoadInst>(I)->getPointerOperand();
            
            //if (isa<Constant>(Ptr->stripPointerCasts())) {
            //    dbg(errs()<<"--> constant. Skip..\n";)
            //    return false;
            //}
            assert(Ptr->getType()->isPointerTy()); 
            
            dbg(errs()<<"Ptr:\t\t"<<*Ptr<<"\n";)
            dbg(errs()<<"stripped:\t"<<*Ptr->stripPointerCasts()<<"\n";)
            
            if (isa<GetElementPtrInst>(Ptr->stripPointerCasts())) {
                assert(!isMissedGep(cast<GetElementPtrInst>(Ptr->stripPointerCasts()), I));
            } 
             
            Type* RetArgTy= Type::getInt8PtrTy(M->getContext());
            SmallVector <Type*, 1> tlist;
            tlist.push_back(RetArgTy);
            FunctionType * hookfty= FunctionType::get(RetArgTy, RetArgTy, false);
            //errs()<<"temp_FTy: "<<*hookfty<<"\n";
            //FunctionCallee hook= M->getOrInsertFunction("__spp_cleantag", hookfty);
            FunctionCallee hook= M->getOrInsertFunction("__spp_checkbound", hookfty);

            Value* TmpPtr = B.CreateBitCast(Ptr, hook.getFunctionType()->getParamType(0));
            CallInst* Masked = B.CreateCall(hook, TmpPtr);
            Value* NewPtr = B.CreatePointerCast(Masked, Ptr->getType());

            int OpIdx = getOpIdx(I, Ptr);
            I->setOperand(OpIdx, NewPtr);
            dbg(errs()<<"new_SL: "<<*I<<"\n";)
            dbg(errs()<<"new_opCB: "<<*Masked<<"\n";)
            
            return true;
        }
        
        bool visitFunc(Function* F) {
            //if (F->getName().equals("TreeAlloc")) {
                //errs()<<"... TreeAlloc ........................\n";
                //errs()<<*F<<"\n";
                //errs()<<"...........................\n";
            //}
            dbg(errs() << "Running_visitFunc...\n";)
            bool Changed = false;

            //for (auto &I : instructions(F)) {
            for (auto BI= F->begin(); BI!= F->end(); ++BI) {
                BasicBlock * BB= &*BI; 
                Instruction * sucInst = &*(BB->begin());

                for (auto II= BB->begin(); II!=BB->end(); ++II) {
                    
                    Instruction * Ins= &*II;

                    dbg(errs()<<"\n-------------------------------\n";)
                    dbg(errs()<<"I_:  "<<*Ins<<"\n";)

                    if (Ins != sucInst) {
                        dbg(errs()<<"\tadded_by_instrumentation? skipping..\n";)
                            continue;
                    }
                    sucInst = getNextInst(Ins);

                    if (sucInst) {
                        dbg(errs()<<"nextI: "<<*sucInst<<"\n";)
                    }
                    //////////// 
                    Changed= replaceFoldedGepOp(Ins);
                    
                    if (isa<LoadInst>(Ins) || isa<StoreInst>(Ins)) {
                        Changed= instrumentLoadOrStore(Ins);
                    }
                    /* GEPs handling --- Apply the arithmetic to the top tag part*/
                    else if (auto *Gep = dyn_cast<GetElementPtrInst>(Ins)) {
                        Changed = instrGep(Gep);
                    }
                    else {
                        //errs()<<" -> ElseIns\n";
                    }
                }
            } //endof forloop

            return Changed;
        }

        void addExternalFunc(Function* F) {
            externalFuncs.insert(F);
        }

        void trackPmemPtrs(Function* F) {
            for (auto &I : instructions(F)) {
                if (auto *CB = dyn_cast<CallBase>(&I)) {
                    Function * callee= CB->getCalledFunction();
                    if (!callee) continue;
                    if (callee->getName()=="pmemobj_direct_inline") {
                        Value *Pmem_ptr = cast<Value>(&I);
                        pmemPtrs.insert(Pmem_ptr);                       
                    }
                }
            }
        }
        
    };
    
    class SPPModule : public ModulePass {
    public:
        static char ID;

        SPPModule() : ModulePass(ID) { }


        virtual bool runOnModule(Module& M) {
            
            errs() << "\n------>>>>>-----------------------------\n";
            errs() << "Running_SPP_Module_Pass start...\n";
            errs() << "ModName: "<< M.getModuleIdentifier()<<"\n";
            
            SPPPass Spp(&M);

            Spp.setDL(&M.getDataLayout()); //init the data layout

            bool Changed = false;
            //Track the external functions first &
            //Track the pointers derived from pmemobj_direct_inline
           
            for (auto F = M.begin(), Fend = M.end(); F != Fend; ++F) {
                
                dbg(errs()<<"__F: "<<F->getName()<<"\t";)
                if (F->isDeclaration()) {
                    dbg(errs()<<"Ext\n";)
                    Spp.addExternalFunc(&*F);
                }
                else {
                    dbg(errs()<<"Int\n";)
                    
                    if (SPPFUNC(F)) continue; 
                    
                    Spp.trackPmemPtrs(&*F);
                }
                dbg(errs()<<"...\n";)
            }

            //Visit the functions to clear the appropriate ptr before external calls
            for (auto F = M.begin(), Fend = M.end(); F != Fend; ++F) {
                dbg(errs()<<"\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n";)
                dbg(errs() << "Func: "<<F->getName()<<"\n";)
                dbg(errs()<<">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n";)
                
                if (F->isDeclaration() || SPPFUNC(F)) {
                    dbg(errs() << " -> External. Skip\n";)
                    continue; 
                }
                
                /*if (F->getName().equals("AdvanceNumber")) {
                    errs()<<"AdvanceNumberBody\n";
                    errs()<<*F<<"\n";
                }*/
                Changed= Spp.visitFunc(&*F);             
            }

            /*
            errs()<<"\n>>> GEP_hooked_CBs >>>>>>>>>>>>>>>>>\n";
            for (unsigned i=0; i< Spp.GEP_hooked_CBs.size(); i++) {
                Instruction * ins= Spp.GEP_hooked_CBs.at(i);
                errs()<<"Hooked: "<< ins->getFunction()->getName()<<"\n";
                errs()<<"     I: "<< *ins <<"\n";
            }
            errs()<<"\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n";
            
            errs()<<"\n>>> GEP_skipped_CBs >>>>>>>>>>>>>>>>>\n";
            for (unsigned i=0; i< Spp.GEP_skipped_CBs.size(); i++) {
                Instruction * ins= Spp.GEP_skipped_CBs.at(i);
                errs()<<"Skipped: "<< ins->getFunction()->getName()<<"\n";
                errs()<<"      I: "<< *ins <<"\n";
            }
            errs()<<"\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n";
            */

            errs() << "Running_SPP_Module_Pass exiting...\n";
            
            return Changed;
        }
        
    };

    char SPPModule::ID = 0;
    static RegisterPass<SPPModule> X("spp", "Safe Persistent Pointers Pass", false, false);

    static void registerPass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
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

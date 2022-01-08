#include "llvm/IR/Function.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

static cl::opt<bool> RemoveHook("wave-miu_remove_hook", cl::init(false),
                          cl::desc("miu remove hook"));

namespace {

bool runMiuRemoveHook(Function &F) {
  if (RemoveHook) {
    errs() << "MiuRemoveHook: ";
    errs().write_escaped(F.getName()) << '\n';
  }
  return false;
}

struct LegacyMiuRemoveHook : public FunctionPass {
  static char ID;
  LegacyMiuRemoveHook() : FunctionPass(ID) {}
  bool runOnFunction(Function &F) override { return runMiuRemoveHook(F); }
};

struct MiuRemoveHook : PassInfoMixin<MiuRemoveHook> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
    if (!runMiuRemoveHook(F))
      return PreservedAnalyses::all();
    return PreservedAnalyses::none();
  }
};

} // namespace

char LegacyMiuRemoveHook::ID = 0;

static RegisterPass<LegacyMiuRemoveHook> X("miu_remove_hook", "Good MiuRemoveHook Pass",
                                 false /* Only looks at CFG */,
                                 false /* Analysis Pass */);

/* Legacy PM Registration */
static llvm::RegisterStandardPasses RegisterMiuRemoveHook(
    llvm::PassManagerBuilder::EP_VectorizerStart,
    [](const llvm::PassManagerBuilder &Builder,
       llvm::legacy::PassManagerBase &PM) { PM.add(new LegacyMiuRemoveHook()); });

/* New PM Registration */
llvm::PassPluginLibraryInfo getMiuRemoveHookPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "MiuRemoveHook", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerVectorizerStartEPCallback(
                [](llvm::FunctionPassManager &PM,
                   llvm::PassBuilder::OptimizationLevel Level) {
                  PM.addPass(MiuRemoveHook());
                });
            PB.registerPipelineParsingCallback(
                [](StringRef Name, llvm::FunctionPassManager &PM,
                   ArrayRef<llvm::PassBuilder::PipelineElement>) {
                  if (Name == "miu_remove_hook") {
                    PM.addPass(MiuRemoveHook());
                    return true;
                  }
                  return false;
                });
          }};
}

#ifndef LLVM_BYE_LINK_INTO_TOOLS
extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getMiuRemoveHookPluginInfo();
}
#endif

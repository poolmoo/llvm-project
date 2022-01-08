add_llvm_library( MiuElimRedundantHook MODULE #BUILDTREE_ONLY
    MiuElimRedundantHook.cpp

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )

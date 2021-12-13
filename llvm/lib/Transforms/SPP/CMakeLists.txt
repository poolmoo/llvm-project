add_llvm_library( LLVMSPP MODULE #BUILDTREE_ONLY
  spp.cpp

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )

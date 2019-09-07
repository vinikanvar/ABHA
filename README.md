# ABHA
ABHA (Access Based Heap Analyzer)

Makefile builds the following source code:

analysis_plugin.cpp: Plugging in the analyses to GCC
dfa: Data Flow Analysis files 
      Allocation sites based analysis
      Liveness analysis
      Simplistic liveness analysis
      Access based points-to analysis
dfv: Data Flow Value files
      Variables
      Points-to graph
      Deterministic graph
      Non-deterministic graph
      Access-based graph
      Access-paths graph
      Access-paths based points-to graph
      Unlabeled edge graph
 ipa: Inter-Procedural Analysis 
      (Templates based classes to plug in any intra-procedural dfa)
      Value contexts
      Interprocedural analysis
      Forward interprocedural analysis
      Backward interprocedural analysis
 misc: Miscellaneous files
      Debugging messages
      Control flow graph block information
      Profiling information
      TVLA
 
 
 The implementation is based on the following publications
 1) 
      

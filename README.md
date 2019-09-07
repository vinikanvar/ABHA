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

      1) ”What’s in a Name?” Going Beyond Allocation Site Names in Heap Analysis. Vini Kanvar, Uday Khedker.
            International Symposium on Memory Management (ISMM), Jun’17, Barcelona.

      2) Heap Abstractions for Static Analysis. Vini Kanvar, Uday Khedker.
            ACM Computing Surveys, Vol 49, Issue 2, Jun’16.
       
       3) Generalizing the Liveness Based Points-to Analysis. Uday Khedker, Vini Kanvar.
            Points-to analysis restricted to live data to improve efficiency and scalability, while preserving precision.
      
       4) Which Part of the Heap is Useful? Improving Heap Liveness Analysis. Vini Kanvar, Uday Khedker.
            Using static liveness analysis to understand the actual use of heap memory in a program.

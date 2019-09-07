#include <cstdlib>		// If this is not the first header file, we get POISONED error on using -std=c++0x
//#include <algorithm>		// Should be used before gcc-plugin.h
#include "gcc-plugin.h"		// Dynamic plugin
#include "config.h"
#include <stdio.h>
//#include "stdlib.h"
#include "system.h"
#include "cgraph.h"
#include "coretypes.h"
#include "tm.h"
#include "diagnostic.h"
#include "gimple-pretty-print.h"
#include "tree.h"
#include "tree-flow.h"
#include "tree-pass.h"
#include "toplev.h"
#include "gimple.h"
#include "cfgloop.h"

#include "vec.h"
#include "ggc.h"
#include "alloc-pool.h"
#include "params.h"
#include "string.h"
#include <string>
#include <sstream>
#include <iostream>
#include <ctime>
#include <sys/sysinfo.h>    // sysinfo
#include <unistd.h>     // sysconf
#include <map>
#include <set>
#include <stack>
#include <list>
#include <vector>
//#include <tr1/unordered_map>
//#include <boost/bimap.hpp>
#include <typeinfo>

#include "misc/profile.hh"

using namespace std;
//using namespace std::tr1;
//using namespace boost;

#define GC 1

// For access based abstraction, we should connect V and V.FIELD nodes with an
// edge labeled FIELD.
#define FIELD_CONNECT_BASED_ON_PROGRAM 0
#define FIELD_CONNECT_BASED_ON_TYPE 1

// For safe handling of pointer arithmetic, we use UNIVERSAL node.
#define POINTER_ARITHMETIC 0

// Without UNDEF node, we achieve weak-must-points-to analysis. With UNDEF
// node, we achieve must-points-to analysis.
#define UNDEF_LOCATION 0
#define NULL_LOCATION 0
#define READONLY_LOCATION 0

// If STRONG_UPDATES is true and UNDEF is true, then strong updates are
// performed based on must-points-to information. If STRONG_UPDATES is true and
// UNDEF is false, then strong updates are performed based on
// weak-must-points-to information.
#define STRONG_UPDATES 0

#define PARALLEL 0

// Field label to denote dereference of a variable through asterisk (*)
// There is no problem in defining ASTERISK as 0---it will not clash
// with any field dereference value, since any field dereference happens
// after ROOT.ASTERISK.
// ASTERISK is like 0 offset from structure.
//const HOST_WIDE_INT ASTERISK = 0;
#define ASTERISK (HOST_WIDE_INT) stack_deref 

// True if liveness and points-to alternate
#define BIDIRECTIONAL_ANALYSIS 0

// To enable collection of only those access paths that start from a stack
// variable.
#define ONLY_STACK_APS 1

// Switch between access based and allocation site based analyses.
// #define ACCESS_BASED 1

// For summarization of access paths 
// (a) based on repeating defining statement ids (in deterministic AP -- STMT
//     closure is taken), set SUMM_STMT_CLOSURE 1
#define SUMM_STMT_CLOSURE 0

// TYPES: For stack APs, we need to summarize (explicit cycles in data
// structure) using types. For heap APs, we need to summarize using allocation
// site of pointee heap (or static name of heap or heap type).
// (b) based on repeating non-zero field ids (types) (in deterministic AP --
//     TYPE closure is taken), set SUMM_TYPE_CLOSURE 1
// (c) based on repeating non-zero field_ids (types) (in non-deterministic AP
//     -- TYPE closure is not taken), set SUMM_TYPE_K 1. To allow K repetitions
//     of the same type along an access path, set SUMM_TYPE_K K .
// TYPES of different allocation sites is considered different if parser
// creates different heap variables for the different calls to malloc().
#define SUMM_TYPE_CLOSURE 0

// This should be 1 for dfa/points_to_analysis_fi
#define SUMM_TYPE_K ACCESS_BASED

// K LIMITED
// (d) based on k-limiting, i.e. APs of k length are stored, rest are filtered
//     out (stored as ap_unbounded predicate), set SUMM_K_FILTER K
// (e) based on k-limiting, i.e. APs' prefix upto k length are stored, set
//     SUMM_K_PREFIX K
// (f) based on k-limiting, i.e. each subgraph of gPT at any program point has
//     max k long sequence of edges, set SUMM_K_CONSISTENT K
#define K 0
#define SUMM_K_FILTER K
#define SUMM_K_PREFIX K
#define SUMM_K_CONSISTENT K
// K_FIELDS=0 counts only ASTERISK. K_FIELDS=1 counts both ASTERISK and FIELDS
#define K_FIELDS 1

// SRW96
// (g) pointed-to-by-x predicate 
//	SUMM_FIELD_POINTED_TO_BY=0: includes aliased with x.*, x.*.f, x.*.f.g, etc. Excludes x.*.f.*, etc.
//	SUMM_FIELD_POINTED_TO_BY=1: includes aliased with x.*. Excludes x.*.f, x.*.f.g, x.*.f.*, etc.
//	SUMM_REACHABLE_BY: Should be enabled when SUMM_FIELD_POINTED_TO_BY is disabled.
#define SUMM_POINTED_TO_BY 		0
#define SUMM_FIELD_POINTED_TO_BY	(0 && SUMM_POINTED_TO_BY)
#define SUMM_REACHABLE_BY		(0 && SUMM_POINTED_TO_BY)

//////////////////////////////////////////////////////////////////////////////////////
// Approximations in alias set recomputation algorithm: 
//////////////////////////////////////////////////////////////////////////////////////

// Set this if Access Name includes gAP nodes that represent unbounded APs
// i.e., if gAP represents unbounded APs, i.e. gAP has cycles.
// Currently this has been defined only for SUMM_TYPE_K == 1.
#define gAP_CYCLIC_CMD 1
#define gAP_CYCLIC (gAP_CYCLIC_CMD && SUMM_TYPE_K)
#define OVER_APPROX_CYCLIC_EDGES (0 && gAP_CYCLIC)

// Record acyclic paths (gAP_CYCLIC=1) but not cyclic edges
#define gAP_CYCLIC_EDGES (1 && gAP_CYCLIC)

// do not reset alias set of clone, rather only accumulate. Too approximate on spec.
	#define RESET_ACCESS_NAMES		1
// filter out new edges that already exist
	#define FILTER_EXISTING_EDGES		1
// summarize repeating fields rather than just repeating ASTERISK
	#define SUMM_FIELD_POINTERS		(0 && SUMM_TYPE_K)
// pull rather than push
	#define PULL_ACCESS_NAMES		1
// push from root (over all valid nodes) rather than pushing randomly over only affected nodes
	#define PUSH_FROM_ROOT			(!PULL_ACCESS_NAMES && 1)
// pull from internal boundary nodes in breadth first order rather than pulling in reverse post order
	#define PULL_BOUNDARY			(PULL_ACCESS_NAMES && 1)
	#if PULL_BOUNDARY == 0 && PULL_ACCESS_NAMES
	#define PULL_REV_PO			700
	#endif
// pull alias set from boundary nodes only once
	#define PULL_BNDRY_ONCE			(PULL_BOUNDARY && 0)
// subsume alias sets (deeper monotonicity)
	// Remove redundant access names using partial order
	#define ACCESS_PARTIAL_ORDER 		(0 && SUMM_TYPE_K)
	// #define PARTIAL_ORDER_STATISTICS	(0 && SUMM_TYPE_K)
	// #define ACCESS_PARTIAL_ORDER 	SUMM_TYPE_K

///////////////////////////////////////////////////////////////////////////////////////

// Enable this to produce heap variables of the form heap.T1,heap.T2,... to
// denote heap of types T1,T2,...
// Disable this to produce allocation site based heap variables of the form
// heap.1,heap.2,... to denote heap allocated at statements 1,2,...
#if ACCESS_BASED
#define HEAP_TYPE_BASED_NAME 0
#endif


// liveness_analysis_simple is a pure backward analysis (independent of
// dept_value_type). Therefore, the dept_value_type is set to the value type of
// the analysis for which it is used.
#if ACCESS_BASED
#define PT_VALUE_TYPE pt_node_set
#else
#define PT_VALUE_TYPE unlabeled_edges
#endif
//#define PT_VALUE_TYPE non_deterministic_simple_graph

// True if we take meet of value contexts
#define MOVP 0

//#define DOT_FILE "/home/vini/Work/Education/GCC/Installations/heap-analysis/plugins/hra-test/graph.dot"
//#define EDGE_FILE "edge_file"
//#define UNIQUE_EDGE_FILE "unique_edge_file"
//#define HEAP_FILE "heap_file"
//#define USEFUL_AP_FILE "useful_ap_file"
//#define STAT_FILE "done.txt"
//#define SETS_TVP_FILE "sets.tvp"
//#define CFG_TVP_FILE "cfg.tvp"
#define NEW_ADDR(...) 
#define GC_ADDR(...) 
//#define NEW_ADDR(...) { \
//        FILE * new_file_ptr = fopen (NEW_FILE, "a"); \
//        fprintf (new_file_ptr, __VA_ARGS__); \
//        fclose (new_file_ptr); \
//}
//#define GC_ADDR(...) { \
//        FILE * gc_file_ptr = fopen (GC_FILE, "a"); \
//        fprintf (gc_file_ptr, __VA_ARGS__); \
//        fclose (gc_file_ptr); \
//}

// Whether statements need to be reanalyzed when flow-insensitive (FI) information changes.
#define FI_REANALYSIS     ACCESS_BASED
//#define FI_REANALYSIS     0

// Defining outn=(inn-kill) U gen U outn.
//#define FORCED_MONOTONICITY 	0
#define FORCED_MONOTONICITY 	(0 | ACCESS_BASED)

// Either both alloc-based and access-based should use or neither -- for
// correct comparison of alias pairs count.
#define SKIP_EMPTY_CFG		1
// Skip paths ending at exit(0) or paths with infinite loop (and no break)
#define SKIP_NORETURN_PATHS	1

// Whether or not to reuse a value-context if it is not being used by any other
// call site. Bypassing unaffected context-dept technique adds adjacent blocks
// to worklist based on flow-sensitive data (and not unaffected context-dept
// data). If we reuse a context, a block may not get added to worklist if its
// flow-sensitive data does not change, even though the unaffected context-dept
// data may have changed. This happened with mcf.
#define REUSE_PROCEDURE_CONTEXT	(0 & !BYPASSING_UNAFFECTED)

#if (TIME_STATISTICS == 0)
#define RESULT_CONTAINER 			1
#define RESULT(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define STATS(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define INFO(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define INFO_CONTAINER 1
//#define RESULT(...) fprintf (stderr, __VA_ARGS__); fflush (stderr);
#define PROFILE_RESULT(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define PROFILE					(0 & ACCESS_BASED)
#define CHECK_CONTAINER 			0
#define INTERMEDIATE_RESULT 			1
#define SUMMARIZE_ALIASED_PATHS 		0
#define STATISTICS_CONTAINER 			(1 & !GC_ON_THE_FLY)
#define LIVE_STATISTICS_CONTAINER		(1 & STATISTICS_CONTAINER)
#define ALLOC_STATISTICS_CONTAINER		(0 & STATISTICS_CONTAINER)
#define RHS_POINTEES_STATS			(0 & STATISTICS_CONTAINER)
#define ALIAS_STATISTICS_CONTAINER 		(0 & !GC_ON_THE_FLY)
#define DATA_SIZE_STATISTICS			0
#define POINTS_TO				(0 || DATA_SIZE_STATISTICS)
#define DUMP_ANALYSIS				0
#define TVLA_DUMP				0
#else
#define STATS(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define RESULT(...) 
#define INFO(...) 
#define STATISTICS_CONTAINER 			1
#define LIVE_STATISTICS_CONTAINER		(1 & STATISTICS_CONTAINER)
#endif

#define UNSOUND_FUNC_PTR 	0
#define UNSOUND_ARRAY 		0
#define UNSOUND_RETURN 		0
#define MERGE_NON_POINTER_FIELDS 0
#define IGNORE_NON_POINTER_FIELDS 0

// Note that GC_ON_THE_FLY wrongly adds blocks unreachable from NONRETURN_BLOCK
// assuming that they need to be processed.
//#define GC_ON_THE_FLY			0

//#define LIVENESS_DETERMINISTIC 		(1  & !ACCESS_BASED)
// KSK07 generates alias closure of live access paths
// #define GREEDY_ALIAS_CLOSURE 		0
//#define ACCUM_LIVE_CONTEXT_INDEPT	0

#define BYPASSING_UNREACHABLE	0
#define BYPASSING_UNUSED	1
#define BYPASSING_UNAFFECTED	(1 & BYPASSING_UNUSED)

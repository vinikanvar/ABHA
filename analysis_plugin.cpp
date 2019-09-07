/************************
 * @author Vini Kanvar
************************/

#include "analysis_plugin.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

#define GCC_POINTS_TO 0
#define LIVENESS_SIMPLE_POINTS_TO_SIMPLE 0

#if ACCESS_BASED
#define LIVENESS_SIMPLE_POINTS_TO_FI 1
#else
#define LIVENESS_SIMPLE_ALLOCATION_SITE 1
#endif

#define POINTS_TO_SIMPLE 0
#define LIVENESS_SIMPLE 0
#define LIVENESS_POINTS_TO_BASIC 0
#define POINTS_TO_BASIC 0
#define OLD_POINTS_TO 0
#define RELEVANCE 0
#define ALIAS 0
#define TESTING 0
#define TESTING_FI 0
#define TESTING_DETERMINISTIC 0

class statistics get_arg_glob_connected_nodes_stats;
class statistics extract_arg_glob_connected_graph_stats;
class statistics get_reachable_nodes_stats;
class statistics clean_useless_nodes_stats;
class statistics clean_disconnected_nodes_stats;
class statistics delete_local_variables_stats;
class statistics get_dead_graph_variables_stats;
class statistics delete_dead_pointers_stats;
class statistics process_assignment_statement_stats;
class statistics initialize_block_worklist_stats;
class statistics merge_graph_stats;
class statistics clean_unreachable_nodes_stats;
class statistics clean_stats;
class statistics copy_value_stats;
class statistics is_value_same_stats;
class statistics print_value_stats;
class statistics is_node_property_same_stats;
class statistics transfer_in_edges_stats;
class statistics transfer_out_edges_stats;
class statistics forward_get_same_dest_context_stats;
class statistics forward_process_call_statement_stats;
class statistics backward_process_call_statement_stats;
class statistics backward_get_same_dest_context_stats;
class statistics in_out_value_differ_stats;

// class parser's object PROGRAM is made global
parser program;
side_effects function_side_effects;
#if TVLA_DUMP
tvla tvla_io;
#endif
#if ALLOC_STATISTICS_CONTAINER
struct dead_locals_statistics dead_locals_stats;
#endif


static unsigned int
aggregate_analysis ()
{
	// Run this analysis only in LTO mode
	if (!in_lto_p)
		return 0;

#if DEBUG_CONTAINER
        FUNCTION_NAME ();
#endif

#if TESTING
	points_to_analysis_simple pta_s;
	// Preprocess the control flow graph and parse the program
	pta_s.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");
	test1_non_deterministic_basic_graph ();
	test2_non_deterministic_basic_graph ();
	test3_non_deterministic_basic_graph ();
	test4_non_deterministic_basic_graph ();
	test5_non_deterministic_basic_graph ();
	test6_non_deterministic_basic_graph ();
	test7_non_deterministic_basic_graph ();
	test8_non_deterministic_basic_graph ();
	test9_non_deterministic_basic_graph ();
	test10_non_deterministic_basic_graph ();
	test11_non_deterministic_basic_graph ();
	test12_non_deterministic_basic_graph ();
	test13_non_deterministic_basic_graph ();
	test14_non_deterministic_basic_graph ();
	test15_non_deterministic_basic_graph ();
	test16_non_deterministic_basic_graph ();
	test17_non_deterministic_basic_graph ();
	test18_non_deterministic_basic_graph ();
	test19_non_deterministic_basic_graph ();
	test20_non_deterministic_basic_graph ();
	test21_non_deterministic_simple_graph ();
	test22_non_deterministic_simple_graph ();
	test23_non_deterministic_simple_graph ();
	test24_non_deterministic_simple_graph ();
	test25_non_deterministic_simple_graph ();
	test26_non_deterministic_simple_graph ();
	test27_non_deterministic_simple_graph ();
	test28_non_deterministic_simple_graph ();
	test29_non_deterministic_simple_graph ();
	test30_non_deterministic_simple_graph ();
	test31_non_deterministic_simple_graph ();
	test32_non_deterministic_simple_graph ();
	test33_non_deterministic_simple_graph ();
	test34_non_deterministic_simple_graph ();
	test35_non_deterministic_simple_graph ();
	test36_non_deterministic_simple_graph ();
	test37_non_deterministic_simple_graph ();
	test38_non_deterministic_simple_graph ();
	test39_non_deterministic_simple_graph ();
	test40_non_deterministic_simple_graph ();
	test41_non_deterministic_simple_graph ();
	test42_non_deterministic_simple_graph ();
	test43_non_deterministic_simple_graph ();
	test44_non_deterministic_simple_graph ();
	test45_non_deterministic_simple_graph ();
	test46_non_deterministic_simple_graph ();
	test47_non_deterministic_simple_graph ();
	test48_non_deterministic_simple_graph ();
	test49_non_deterministic_simple_graph ();
	test50_non_deterministic_simple_graph ();
	test51_non_deterministic_simple_graph ();
	test52_non_deterministic_simple_graph ();
	test53_non_deterministic_simple_graph ();
	test54_non_deterministic_simple_graph ();
	test55_non_deterministic_simple_graph ();
	test56_non_deterministic_simple_graph ();
	test_bb_order ();

	allocation_site_based_analysis<variables> asba (true);
	asba.preprocess_and_parse_program ();
//	test1_allocation_site_based_analysis ();
//	test2_allocation_site_based_analysis ();
//	test3_allocation_site_based_analysis ();
	test4_allocation_site_based_analysis ();
	program.delete_block_aux ();
#endif


#if TESTING_FI
	points_to_analysis_fi pta_fi_test (true);
	pta_fi_test.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");
	program.print_assignment_data ();

//	test1_ap_fi_graph ();
//	test1_pt_fi_graph ();
//	test1_pt_access_fi_map ();
//	test1_points_to_analysis_fi ();
//	test2_points_to_analysis_fi ();
//	test3_points_to_analysis_fi ();
//	test1_points_to_analysis_fi_region ();
//	test1_points_to_analysis_fi_len ();
//	test2_points_to_analysis_fi_len ();
	test3_points_to_analysis_fi_ap_tree ();

	program.delete_block_aux ();
#endif

#if TESTING_DETERMINISTIC
	allocation_site_based_analysis<deterministic_graph> pta_alloc (true);
	pta_alloc.preprocess_and_parse_program ();
	liveness_analysis_deterministic la (true);
	la.preprocess_and_parse_program ();
	la.set_dependent_analysis (&pta_alloc);
	
	//test1_deterministic_insert ();	
	test2_deterministic_copy ();	

	program.delete_block_aux ();

#endif

#if GCC_POINTS_TO
	program.print_original_gcc_points_to_pairs ();
	program.print_gcc_fn_pointees ();
#endif

////////////////////////////////////////////////////////////////////////////////////////////

#if LIVENESS_SIMPLE_ALLOCATION_SITE

	// 1a. liveness analysis simple
	// 1b. store callees_global_defs/uses, function_param_defs
	// 2a. allocation-site based pta (use 1a and 1b)
	// 2b. meet over valid paths, accumulate caller to callee
	// 2c. compute callees_lhs_derefs, accumulate callee to caller
	// 3a. liveness_analysis_deterministic/non_deterministic (use 2b, 2c, 1b)
	// 3b. meet over valide paths, accumulate caller to callee
	// 4a. allocation-site based pta (use 3a, 1b)

#if LIVENESS_DETERMINISTIC
	liveness_analysis<deterministic_graph, deterministic_node> la_det (true);
#else
	liveness_analysis<non_deterministic_graph, non_deterministic_node> la_non_det (true);
#endif

////////////////////////////////////////////////////////////////////////////////////////////

	{
#if LIVENESS_DETERMINISTIC
		allocation_site_based_analysis<deterministic_graph> pta_alloc_for_live_det (true);
#else
		allocation_site_based_analysis<non_deterministic_graph> pta_alloc_for_live_non_det (true);
#endif
		{
			double live_greedy_time = 0, preproc_time = 0, pta_time = 0;
			struct timeval  tv1, tv2;
		
			time_t t=time(NULL);
			struct tm tm= *localtime(&t);
			RESULT ("In file analysis_plugin.cpp, benchmark started on: %d-%d-%d Time %d:%d:%d\n",
				tm.tm_mday,tm.tm_mon+1, tm.tm_year + 1900, tm.tm_hour, tm.tm_min, tm.tm_sec);
		
			liveness_analysis_simple la_s (true);
			DEBUG ("\nla_s created");
			gettimeofday(&tv1, NULL);
			la_s.preprocess_and_parse_program ();
			gettimeofday(&tv2, NULL);
			preproc_time = ((double) (tv2.tv_usec - tv1.tv_usec) / 1000000) 
				+ (double) (tv2.tv_sec - tv1.tv_sec);
			DEBUG ("\nPreprocessing and parsing done\n");
		
			gettimeofday(&tv1, NULL);
			la_s.analyze_program ();
			gettimeofday(&tv2, NULL);
			live_greedy_time = ((double) (tv2.tv_usec - tv1.tv_usec) / 1000000) 
				+ (double) (tv2.tv_sec - tv1.tv_sec);
		
			la_s.store_contexts_info ();

			#if CHECK_CONTAINER
			la_s.is_one_context_per_function ();
			#endif
			#if STATISTICS_CONTAINER
			// la_s.print_statistics ();
			#endif
		
			RESULT ("\npreproc_time = %lf", preproc_time);
			RESULT ("\nlive_greedy_time = %lf", live_greedy_time);
			FILE * stat_file = fopen (STAT_FILE, "a");
			fprintf (stat_file, "\npreproc_time = %lf", preproc_time);
			fprintf (stat_file, "\nlive_greedy_time = %lf", live_greedy_time);
			fclose (stat_file);
		
			// Do not delete parsed data from blocks because on-the-fly generated
			// types are used by allocations-site based graphs which are required
			// by liveness analysis.
			// program.delete_block_aux ();
			// la_s.restore_control_flow_graph ();
			RESULT ("\nCompleted liveness_analysis_simple\n");
			for (int i = 0; i < 80; i++)
				RESULT ("-");
			RESULT ("\n");
		
			allocation_site_based_analysis<variables> pta_alloc (true);
			pta_alloc.preprocess_and_parse_program ();
			DEBUG ("\nPreprocessing and parsing done\n");
			pta_alloc.set_dependent_analysis (&la_s);
		
			DEBUG ("\ntotal time started");
			// Suryansh start time
			gettimeofday(&tv1, NULL);
			pta_alloc.analyze_program ();
			// Suryansh stop time
			gettimeofday(&tv2, NULL);
			pta_time = ((double) (tv2.tv_usec - tv1.tv_usec) / 1000000) 
				+ (double) (tv2.tv_sec - tv1.tv_sec);
			RESULT ("\nTotal elapsed time (Calculated by gettimeofday() ) = %lf seconds\n", pta_time);
			DEBUG ("\ntotal time ended");
		
			#if ALLOC_STATISTICS_CONTAINER
			pta_alloc.print_statistics ();
			#endif
		
			// program.delete_block_aux ();
			// pta_s.restore_control_flow_graph ();
			RESULT ("\nCompleted allocation_site_based_analysis\n");
			for (int i = 0; i < 80; i++)
				RESULT ("-");
		
			// print_time_statistics ();
		
			RESULT ("\npta_time = %lf", pta_time);
			stat_file = fopen (STAT_FILE, "a");
			fprintf (stat_file, "\npta_time = %lf", pta_time);
			fclose (stat_file);
	
///////////////////////////////////////////////////////////////////////////////////////////////////

			double movp_pta_time = 0;
			gettimeofday(&tv1, NULL);
#if LIVENESS_DETERMINISTIC 
			pta_alloc.meet_over_valid_paths (pta_alloc_for_live_det);
			DEBUG ("\npta_alloc.meet done");
			// Accumulate aux (context_indept) info.
			// Note that this cannot be done during the analysis because this
			// accumulation needs fixed point computation.
			// context_dept info is already accumulated during analysis.
			pta_alloc_for_live_det.accumulate_contexts (true);
			DEBUG ("\npta_alloc_for_live.accum done");
			pta_alloc_for_live_det.store_contexts_info ();
			DEBUG ("\npta_alloc_for_live.store done");
			#if DEBUG_CONTAINER
			DEBUG ("\nBEFORE ACCUMULATION");
			function_side_effects.print_side_effects ();
			#endif
	        	// Accumulate aux (callees_lhs_derefs) info.
	        	// Note that this cannot be done during the analysis because this
        		// accumulation needs fixed point computation.
		        pta_alloc_for_live_det.accumulate_contexts (false);
			#if DEBUG_CONTAINER
			pta_alloc_for_live_det.print_program_contexts ();
			#endif
			#if DEBUG_CONTAINER
			DEBUG ("\nAFTER ACCUMULATION");
			function_side_effects.print_side_effects ();
			#endif
			#if CHECK_CONTAINER
			pta_alloc_for_live_det.is_one_context_per_function ();
			#endif

#else
			pta_alloc.meet_over_valid_paths (pta_alloc_for_live_non_det);
			DEBUG ("\npta_alloc.meet done");
			// Accumulate aux (context_indept) info.
			// Note that this cannot be done during the analysis because this
			// accumulation needs fixed point computation.
			// context_dept info is already accumulated during analysis.
			pta_alloc_for_live_non_det.accumulate_contexts (true);
			DEBUG ("\npta_alloc_for_live.accum done");
			pta_alloc_for_live_non_det.store_contexts_info ();
			DEBUG ("\npta_alloc_for_live.store done");
	        	// Accumulate aux (callees_lhs_derefs) info.
	        	// Note that this cannot be done during the analysis because this
        		// accumulation needs fixed point computation.
		        pta_alloc_for_live_non_det.accumulate_contexts (false);
			#if DEBUG_CONTAINER
			pta_alloc_for_live_non_det.print_program_contexts ();
			#endif
			#if CHECK_CONTAINER
			pta_alloc_for_live_non_det.is_one_context_per_function ();
			#endif
#endif
			gettimeofday(&tv2, NULL);
			movp_pta_time = ((double) (tv2.tv_usec - tv1.tv_usec) / 1000000) 
				+ (double) (tv2.tv_sec - tv1.tv_sec);
		
			RESULT ("\nmovp_pta_time = %lf", movp_pta_time);
			stat_file = fopen (STAT_FILE, "a");
			fprintf (stat_file, "\nmovp_pta_time = %lf", movp_pta_time);
			fclose (stat_file);
			DEBUG ("\nend of liveness_analysis_simple (variables)");
			DEBUG ("\nend of pta_alloc<variables>");

#if ALLOC_STATISTICS_CONTAINER
			RESULT ("\nALLOC ACCUMULATED context-indept values");
			stat_file = fopen (STAT_FILE, "a");
			fprintf (stat_file, "\naccumulated context-indept values");
			fclose (stat_file);
#if LIVENESS_DETERMINISTIC 
			pta_alloc_for_live_det.print_bypassing_statistics ();
#else
			pta_alloc_for_live_non_det.print_bypassing_statistics ();
#endif
#endif
		}

//////////////////////////////////////////////////////////////////////////////////////////////

		DEBUG ("\nPreprocessing and parsing done\n");
#if LIVENESS_DETERMINISTIC
		pta_alloc_for_live_det.set_dependent_analysis (&la_det);
		la_det.set_dependent_analysis (&pta_alloc_for_live_det);
		#if DEBUG_CONTAINER
		pta_alloc_for_live_det.print_program_contexts ();
		#endif
		// Preprocess the control flow graph and parse the program
		la_det.preprocess_and_parse_program ();

#else
		pta_alloc_for_live_non_det.set_dependent_analysis (&la_non_det);
		la_non_det.set_dependent_analysis (&pta_alloc_for_live_non_det);
		#if DEBUG_CONTAINER
		pta_alloc_for_live_non_det.print_program_contexts ();
		#endif
		// Preprocess the control flow graph and parse the program
		la_non_det.preprocess_and_parse_program ();
#endif
	
		double live_time = 0;
		struct timeval  tv1, tv2;
		gettimeofday(&tv1, NULL);
#if LIVENESS_DETERMINISTIC
		la_det.analyze_program ();
		RESULT ("\nCompleted liveness_analysis_deterministic analysis\n");
		for (int i = 0; i < 80; i++)
			RESULT ("-");
	
#else
		la_non_det.analyze_program ();
		RESULT ("\nCompleted liveness_analysis_non_deterministic analysis\n");
		for (int i = 0; i < 80; i++)
			RESULT ("-");
#endif

		gettimeofday(&tv2, NULL);
		live_time = ((double) (tv2.tv_usec - tv1.tv_usec) / 1000000) 
			+ (double) (tv2.tv_sec - tv1.tv_sec);
	
		RESULT ("\nlive_time = %lf", live_time);
		FILE * stat_file = fopen (STAT_FILE, "a");
		fprintf (stat_file, "\nlive_time = %lf", live_time);
		fclose (stat_file);

#if LIVE_STATISTICS_CONTAINER
		gettimeofday(&tv1, NULL);
		// Free all blocks except bb=2 of pta_alloc_for_live_det/non_det
		// Free all blocks except bb=2 of la_det/non_det
#if LIVENESS_DETERMINISTIC
		DEBUG ("\nfree_pta");
		pta_alloc_for_live_det.free_context_values ();
		DEBUG ("\nfree_live");
		la_det.free_context_values ();
		//#if ACCUM_LIVE_CONTEXT_INDEPT
		la_det.meet_over_valid_paths (la_det);
		la_det.accumulate_contexts (true);
		//#endif
#else
		pta_alloc_for_live_non_det.free_context_values ();
		la_non_det.free_context_values ();
		//#if ACCUM_LIVE_CONTEXT_INDEPT
		la_non_det.meet_over_valid_paths (la_non_det);
		la_non_det.accumulate_contexts (true);
		//#endif
#endif
		gettimeofday(&tv2, NULL);
		double movp_live_time = ((double) (tv2.tv_usec - tv1.tv_usec) / 1000000) 
			+ (double) (tv2.tv_sec - tv1.tv_sec);
	
		RESULT ("\nmovp_live_time = %lf", movp_live_time);
		stat_file = fopen (STAT_FILE, "a");
		fprintf (stat_file, "\nmovp_live_time = %lf", movp_live_time);
		fclose (stat_file);

#if LIVENESS_DETERMINISTIC
		la_det.print_statistics ();
#else
		la_non_det.print_statistics ();
#endif
#endif
	
		// program.delete_block_aux ();
		// la_det.restore_control_flow_graph ();
	
		// print_time_statistics ();
	
	}

////////////////////////////////////////////////////////////////////////////////////////////

	RESULT ("\n");
	for (int i = 0; i < 80; i++)
		RESULT ("-");

	program.delete_block_aux ();

	INFO ("\nPROGRAM\n=======\n");
#endif

////////////////////////////////////////////////////////////////////////////////////////////

#if LIVENESS_SIMPLE_POINTS_TO_FI

	print_memory_statistics ();

	double live_time = 0, preproc_time = 0, pta_time = 0;
	struct timeval  tv1, tv2;

	time_t t=time(NULL);
	struct tm tm= *localtime(&t);
	RESULT ("In file analysis_plugin.cpp, benchmark started on: %d-%d-%d Time %d:%d:%d\n",
		tm.tm_mday,tm.tm_mon+1, tm.tm_year + 1900, tm.tm_hour, tm.tm_min, tm.tm_sec);

	liveness_analysis_simple la_s (true);
	DEBUG ("\nla_s created");
	gettimeofday(&tv1, NULL);
	la_s.preprocess_and_parse_program ();
	gettimeofday(&tv2, NULL);
	preproc_time = ((double) (tv2.tv_usec - tv1.tv_usec) / 1000000) + (double) (tv2.tv_sec - tv1.tv_sec);
	DEBUG ("\nPreprocessing and parsing done\n");

	gettimeofday(&tv1, NULL);
	la_s.analyze_program ();
	la_s.print_program_contexts ();
	gettimeofday(&tv2, NULL);
	live_time = ((double) (tv2.tv_usec - tv1.tv_usec) / 1000000) + (double) (tv2.tv_sec - tv1.tv_sec);

#if STATISTICS_CONTAINER
	la_s.print_statistics ();
#endif

	// program.delete_block_aux ();
	// la_s.restore_control_flow_graph ();
	RESULT ("\nCompleted liveness_analysis_simple\n");
	for (int i = 0; i < 80; i++)
		RESULT ("-");
	RESULT ("\n");

	FILE * stat_file = fopen (STAT_FILE, "a");
	tm= *localtime(&t);
	fprintf (stat_file, "liveness_simple completed %d-%d-%d Time %d:%d:%d\n",
		tm.tm_mday,tm.tm_mon+1, tm.tm_year + 1900, tm.tm_hour, tm.tm_min, tm.tm_sec);
	fprintf (stat_file, "\nlive_time = %lf", live_time);
	fclose (stat_file);

	points_to_analysis_fi pta_fi (true);
	pta_fi.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");

#if TVLA_DUMP
	tvla_io.print_tvp_file ();
#endif

	pta_fi.set_dependent_analysis (&la_s);

	INIT_PROFILE_STATS ();
	FUNBEGIN ();

	DEBUG ("\ntotal time started");
	// Suryansh start time
	gettimeofday(&tv1, NULL);
	pta_fi.analyze_program ();
	// Suryansh stop time
	gettimeofday(&tv2, NULL);
	pta_time = ((double) (tv2.tv_usec - tv1.tv_usec) / 1000000) + (double) (tv2.tv_sec - tv1.tv_sec);
	RESULT ("\nTotal elapsed time (Calculated by gettimeofday() ) = %lf seconds\n", pta_time);
	DEBUG ("\ntotal time ended");

	FUNEND ();
	PRINT_PROFILE_STATS ();

#if STATISTICS_CONTAINER
	pta_fi.print_program_contexts ();
	pta_fi.print_statistics ();
#endif

	program.delete_block_aux ();
	// pta_s.restore_control_flow_graph ();
	RESULT ("\nCompleted liveness_analysis_simple based ");
	RESULT ("points_to_analysis_simple\n");
	for (int i = 0; i < 80; i++)
		RESULT ("-");

	// print_time_statistics ();

	RESULT ("\npreproc_time = %lf", preproc_time);
	RESULT ("\nlive_time = %lf", live_time);
	RESULT ("\npta_time = %lf", pta_time);
	stat_file = fopen (STAT_FILE, "a");
	fprintf (stat_file, "\npreproc_time = %lf", preproc_time);
	fprintf (stat_file, "\nlive_time = %lf", live_time);
	fprintf (stat_file, "\npta_time = %lf", pta_time);
	fclose (stat_file);

	print_memory_statistics ();

	RESULT ("\n");
	for (int i = 0; i < 80; i++)
		RESULT ("-");

	INFO ("\nPROGRAM\n=======\n");
#endif


#if LIVENESS_SIMPLE_POINTS_TO_SIMPLE

	time_t t=time(NULL);
	struct tm tm= *localtime(&t);
	RESULT ("In file analysis_plugin.cpp, benchmark started on: %d-%d-%d Time %d:%d:%d\n",
		tm.tm_mday,tm.tm_mon+1, tm.tm_year + 1900, tm.tm_hour, tm.tm_min, tm.tm_sec);

	liveness_analysis_simple la_s (false);
	la_s.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");
	la_s.analyze_program ();

#if STATISTICS_CONTAINER
	la_s.print_statistics ();
#endif

	program.delete_block_aux ();
	// la_s.restore_control_flow_graph ();
	RESULT ("\nCompleted liveness_analysis_simple\n");
	for (int i = 0; i < 80; i++)
		RESULT ("-");
	RESULT ("\n");

	points_to_analysis_simple pta_s;
	pta_s.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");
	pta_s.set_dependent_analysis (&la_s);

	DEBUG ("\ntotal time started");
	struct timeval  tv1, tv2;
	// Suryansh start time
	gettimeofday(&tv1, NULL);
	pta_s.analyze_program ();
	// Suryansh stop time
	gettimeofday(&tv2, NULL);
	RESULT ("\nTotal elapsed time (Calculated by gettimeofday() ) = %f seconds\n",
		(double) (tv2.tv_usec - tv1.tv_usec) / 1000000 + (double) (tv2.tv_sec - tv1.tv_sec));
	DEBUG ("\ntotal time ended");

//#if STATISTICS_CONTAINER
	pta_s.print_statistics ();

	program.print_variable_data ();
//#endif

	program.delete_block_aux ();
	// pta_s.restore_control_flow_graph ();
	RESULT ("\nCompleted liveness_analysis_simple based ");
	RESULT ("points_to_analysis_simple\n");
	for (int i = 0; i < 80; i++)
		RESULT ("-");

	print_time_statistics ();

	RESULT ("\n");
	for (int i = 0; i < 80; i++)
		RESULT ("-");

	INFO ("\nPROGRAM\n=======\n");
#endif

#if POINTS_TO_SIMPLE
	points_to_analysis_simple pta_s;
	// Preprocess the control flow graph and parse the program
	pta_s.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");

	initialize_time_statistics ();
	time_t start = time (0);

	pta_s.analyze_program ();

	time_t stop = time (0);
	double diff = difftime (stop, start);
	fprintf (dump_file, "\nTime: %f seconds", diff);
	print_time_statistics ();

#if STATISTICS_CONTAINER
	pta_s.print_statistics ();
#endif

	t=time(NULL);
	tm= *localtime(&t);
	RESULT ("\nStopped on: %d-%d-%d Time %d:%d:%d\n",
		tm.tm_mday,tm.tm_mon+1, tm.tm_year + 1900, tm.tm_hour, tm.tm_min, tm.tm_sec);

	RESULT ("\nPROGRAM\n");
	program.delete_block_aux ();
	// pta_s.restore_control_flow_graph ();
#endif

#if LIVENESS_SIMPLE
	liveness_analysis_simple la_s (false);
	// Preprocess the control flow graph and parse the program
	la_s.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");
	la_s.analyze_program ();
	RESULT ("\nLIVE\n=========\n");
	la_s.print_statistics ();
	program.print_variable_data ();
	RESULT ("\nPROGRAM\n=============\n");
	program.delete_block_aux ();
	// la_s.restore_control_flow_graph ();
#endif

#if LIVENESS_POINTS_TO_BASIC
	relevance_analysis ra;
	points_to_analysis_basic pta_b;
	ra.set_dependent_analysis (&pta_b);
	pta_b.set_dependent_analysis (&ra);
	// Preprocess the control flow graph and parse the program
	ra.preprocess_and_parse_program ();
	pta_b.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");
	ra.analyze_program ();
	program.delete_block_aux ();
	// ra.restore_control_flow_graph ();
#endif

#if RELEVANCE
	relevance_analysis ra;
	// Preprocess the control flow graph and parse the program
	ra.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");
	ra.analyze_program ();
	program.delete_block_aux ();
	// ra.restore_control_flow_graph ();
#endif

#if POINTS_TO_BASIC
	points_to_analysis_basic pta_b;
	// Preprocess the control flow graph and parse the program
	pta_b.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");
	pta_b.analyze_program ();
	program.delete_block_aux ();
	// pta_b.restore_control_flow_graph ();
#endif

#if OLD_POINTS_TO
	points_to_analysis pta;
	// Preprocess the control flow graph and parse the program
	pta.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");
	pta.analyze_program ();
	program.delete_block_aux ();
	// pta.restore_control_flow_graph ();
#endif

#if ALIAS 
	alias_analysis aa;
	// Preprocess the control flow graph and parse the program
	aa.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");
	aa.analyze_program ();
	program.delete_block_aux ();
	// aa.restore_control_flow_graph ();

	liveness_analysis_deterministic la (true);
	la.set_dependent_analysis (&aaa);
	// Preprocess the control flow graph and parse the program
	la.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");
	la.analyze_program ();
	program.delete_block_aux ();
	// la.restore_control_flow_graph ();
#endif

	return 0;
}



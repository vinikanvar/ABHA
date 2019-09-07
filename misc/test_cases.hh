
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef TEST_CASES 
#define TEST_CASES

#include "../misc/debug.hh"
#include "../dfa/liveness_analysis.hh"
#include "../dfa/points_to_analysis_fi.hh"
#include "../dfv/ap_fi_graph.hh"
#include "../dfv/access_name.hh"

void test1_non_deterministic_basic_graph ();
void test2_non_deterministic_basic_graph ();
void test3_non_deterministic_basic_graph ();
void test4_non_deterministic_basic_graph ();
void test5_non_deterministic_basic_graph ();
void test6_non_deterministic_basic_graph ();
void test7_non_deterministic_basic_graph ();
void test8_non_deterministic_basic_graph ();
void test9_non_deterministic_basic_graph ();
void test10_non_deterministic_basic_graph ();
void test11_non_deterministic_basic_graph ();
void test12_non_deterministic_basic_graph ();
void test13_non_deterministic_basic_graph ();
void test14_non_deterministic_basic_graph ();
void test15_non_deterministic_basic_graph ();
void test16_non_deterministic_basic_graph ();
void test17_non_deterministic_basic_graph ();
void test18_non_deterministic_basic_graph ();
void test19_non_deterministic_basic_graph ();
void test20_non_deterministic_basic_graph ();
void test21_non_deterministic_simple_graph ();
void test22_non_deterministic_simple_graph ();
void test23_non_deterministic_simple_graph ();
void test24_non_deterministic_simple_graph ();
void test25_non_deterministic_simple_graph ();
void test26_non_deterministic_simple_graph ();
void test27_non_deterministic_simple_graph ();
void test28_non_deterministic_simple_graph ();
void test29_non_deterministic_simple_graph ();
void test30_non_deterministic_simple_graph ();
void test31_non_deterministic_simple_graph ();
void test32_non_deterministic_simple_graph ();
void test33_non_deterministic_simple_graph ();
void test34_non_deterministic_simple_graph ();
void test35_non_deterministic_simple_graph ();
void test36_non_deterministic_simple_graph ();
void test37_non_deterministic_simple_graph ();
void test38_non_deterministic_simple_graph ();
void test39_non_deterministic_simple_graph ();
void test40_non_deterministic_simple_graph ();
void test41_non_deterministic_simple_graph ();
void test42_non_deterministic_simple_graph ();
void test43_non_deterministic_simple_graph ();
void test44_non_deterministic_simple_graph ();
void test45_non_deterministic_simple_graph ();
void test46_non_deterministic_simple_graph ();
void test47_non_deterministic_simple_graph ();
void test48_non_deterministic_simple_graph ();
void test49_non_deterministic_simple_graph ();
void test50_non_deterministic_simple_graph ();
void test51_non_deterministic_simple_graph ();
void test52_non_deterministic_simple_graph ();
void test53_non_deterministic_simple_graph ();
void test54_non_deterministic_simple_graph ();
void test55_non_deterministic_simple_graph ();
void test56_non_deterministic_simple_graph ();
void test_deterministic_node ();

void test_bb_order ();
void test1_ap_fi_graph ();
void test1_pt_fi_graph ();
void test1_pt_access_fi_map ();
static void my_update_ap (set<pt_node_index> & pt_n_proc,
        set<pt_node_index> & lptr,
        set<pt_node_index> & must_lptr,
        label l,
        def_stmt_set ds,
        set<pt_node_index> & rptr,
        pt_fi_graph & g_pt,
        ap_fi_graph & g_ap,
        pt_access_fi_map & pt_access_map);
void test1_points_to_analysis_fi ();
void test2_points_to_analysis_fi ();
void test3_points_to_analysis_fi ();
void test1_points_to_analysis_fi_region ();
void test1_points_to_analysis_fi_len ();
void test2_points_to_analysis_fi_len ();
void test3_points_to_analysis_fi_ap_tree ();

void test1_allocation_site_based_analysis ();
void test2_allocation_site_based_analysis ();
void test3_allocation_site_based_analysis ();
void test4_allocation_site_based_analysis ();

void test1_deterministic_insert ();
void test2_deterministic_copy ();


#endif

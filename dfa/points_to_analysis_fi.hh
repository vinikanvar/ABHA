
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef POINTS_TO_ANALYSIS_FI
#define POINTS_TO_ANALYSIS_FI

#include "../misc/debug.hh"
#include "../misc/parser.hh"
#include "../misc/block_information.hh"
#include "../ipa/context.hh"
#include "../ipa/forward_inter_procedural_analysis.hh"
#include "../dfv/variables.hh"
#include "../dfv/pt_node_set.hh"
#include "../dfv/pt_fi_graph.hh"
#include "../dfv/ap_fi_graph.hh"
#include "../dfv/access_name.hh"
#include "../dfv/pt_access_fi_map.hh"

class points_to_analysis_fi : public forward_inter_procedural_analysis<pt_node_set, variables>
{
public:
	pt_fi_graph 		g_pt;
	ap_fi_graph 		g_ap;
	pt_access_fi_map	pt_access_map;

	// Save the mapping from each gPT node to context and IN-block it is
	// valid at. This is used to find which <context,block> need to be
	// reanalysed when a gPT edge changes.
#if FI_REANALYSIS
	map<pt_node_index, set<pair<context_index, basic_block> > > in_value_to_blocks;
#endif

        // For statistics, counting the total number of affected nodes, and
        // number of program points that affect nodes.
        unsigned int tot_stmttouch;
        unsigned int tot_update_points;
	unsigned int tot_potaffreg;
	unsigned int tot_finalaffreg;
	

        using inter_procedural_analysis<pt_node_set, variables>::get_called_functions;
	using inter_procedural_analysis<pt_node_set, variables>::delete_context_aux_info;

private:

	set<struct cgraph_node *> get_called_functions (context<pt_node_set, variables> & src_context, basic_block call_site, tree function_pointer);
	pt_node_set * initial_value ();
	pt_node_set * boundary_value ();
	void generate_missing_globals (pt_node_set & value);
	void generate_missing_locals (pt_node_set & value, struct cgraph_node * curr_function);
	void generate_missing_params (pt_node_set & value, struct cgraph_node * curr_function);
	void generate_fresh_heap_nodes (pt_node_set & value);
	void generate_missing_vars (set<label> & vars, pt_node_set & value);
	void generate_fresh_vars (set<label> & vars, pt_node_set & value);

	void process_in_value (context<pt_node_set, variables> * current_context, basic_block current_block);
	void process_call_statement (context<pt_node_set, variables> * src_context, basic_block call_site);
	void process_function_arguments (context<pt_node_set, variables> * src_context, basic_block call_site, pt_node_set * value, struct cgraph_node * called_function);
	void process_return_value (context<pt_node_set, variables> * src_context, basic_block call_site, pt_node_set * value, struct cgraph_node * called_function, bool to_kill);
	bool process_parsed_data (context<pt_node_set, variables> * current_context, basic_block current_block, pt_node_set * calling_value, bool to_kill = true);
	bool process_assignment_statement (pt_node_set & value, context<pt_node_set, variables> * current_context, basic_block current_block, unsigned int assignment_data_index, bool to_kill = true);
#if SUMM_STMT_CLOSURE == 0
	bool process_assignment_statement (pt_node_set & value, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, context<pt_node_set, variables> * current_context, basic_block current_block, unsigned int assignment_data_index, bool to_kill = true);
#endif
	void generate_lhs_rhs_nodes (pt_node_set & value, constraint_expr & lhs, constraint_expr & rhs, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, bool to_kill);
	void generate_rhs_nodes (pt_node_set & value, constraint_expr & rhs, set<pt_node_index> & rhs_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	void generate_lhs_nodes (pt_node_set & value, constraint_expr & lhs, set<pt_node_index> & may_lhs_nodes, set<pt_node_index> & must_lhs_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, bool is_rhs_non_empty);
	void populate_excl_edges (set<pt_node_index> & must_lhs_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, pt_node_set & value);
	void populate_incl_edges (set<pt_node_index> & may_lhs_nodes, set<pt_node_index> & rhs_nodes, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, pt_node_set & value);
	void generate_pointer_nodes (pt_node_set & value, label var, list<label> * field_sequence, set<pt_node_index> & pointer_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	void generate_field_nodes (pt_node_set & value, pt_node_index src_node, tree src_pointer_type, label field, set<pt_node_index> & field_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);

	void get_live_data (pt_node_set & out_value, context<pt_node_set, variables> & current_context, basic_block current_block, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<pt_node_index> & must_lhs_nodes);
	void get_live_data (pt_node_set & out_value, context<pt_node_set, variables> & current_context, basic_block current_block, set<pt_node_index> & must_lhs_nodes);
	variables * get_live_out_value (context<pt_node_set, variables> & current_context, basic_block current_block);
	set<unsigned int> get_callees_global_defs (struct cgraph_node * function);
	set<unsigned int> get_callees_global_uses (struct cgraph_node * function);
	pt_node_set * extract_par_glob_reachable_value (struct cgraph_node * dest_function, pt_node_set & value_in, set<pt_node_index> & int_bndry_nodes, map<pt_node_index, pt_node_index> & caller_clone);
	map<pt_node_index, set<pt_node_index> > restore_par_glob_unreachable_nodes (set<pt_node_index> & callee_out_value, set<pt_node_index> & par_glob_unreachable_nodes, set<pt_node_index> & int_bndry_nodes, pt_node_set & restored_out_value, map<pt_node_index, pt_node_index> & caller_clone, map<pt_node_index, set<pt_node_index> > & callee_clone);

	
public:
	set<variable_id> get_dead_variables (pt_node_set & value, context<pt_node_set, variables> & current_context, basic_block current_block);
#if SUMM_STMT_CLOSURE == 0
	void clone_and_update_subgraph (pt_node_set & value_in, set<pt_node_index> & must_lptr, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, context<pt_node_set, variables> * current_context, bool to_gen_fresh_heap, bool to_append_clone);
#endif
	void clone_and_update_subgraph (pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, map<pt_node_index, pt_node_index> & clone);
	pt_fi_node * get_valid_clone (pt_node_index nid, set<pt_node_index> & value_in, map<pt_node_index, bool> & cloned_nodes, map<pt_node_index, pt_node_index> & clone);
	void clone_edges (map<pt_node_index, pt_node_index> & clone, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, map<pt_node_index, bool> & affected_nodes, unsigned int old_max_node_id, set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges);

	void add_old_fs_new_fi_edge (pt_node_index srcid, pt_node_index dest_id, unsigned int old_max_node_id, set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges);
	void reanalyse_fi_dept_blocks (set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges);

	map<pt_node_index, pt_node_index> clone_nodes (pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte,  map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, map<pt_node_index, max_depth> & new_pt_to_max_depth, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name, map<pt_node_index, bool> & affected_nodes);
	map<pt_node_index, pt_node_index> get_node_clones (map<pt_node_index, bool> & affected_nodes, map<pt_node_index, max_depth> & new_pt_to_max_depth, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
	pt_node_index generate_clone (access_name & new_access_name, max_depth new_max_depth);
	void initialize_fresh_ans (int old_max_node_id, pt_node_set & value);
	map<pt_node_index, bool> find_new_ans_and_affected_region (set<pt_node_index> & nvisit, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, map< pt_node_index, max_depth> & new_pt_to_max_depth, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
	void find_new_summ_cmpts (set<pt_node_index> & nvisit, set<pt_node_index> & ext_bndry, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, max_depth> & new_pt_to_max_depth, set<set<pt_node_index> > & summ_cmpts);
	void dfs_nodes_rev_po (pt_node_index pt_nid, set<pt_node_index> & visited, list<pt_node_index> & nodes_rev_po, pt_node_set & value_in, set<pt_node_index> & nreach, set<pt_node_index> & lptr, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	pt_node_index get_next_node (map<unsigned int, pt_node_index> & nreach_worklist);
	void pull_new_ans_rev_po (set<pt_node_index> & nreach, set<pt_node_index> & ext_bndry, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<set<pt_node_index> > & summ_cmpts, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
	void pull_new_ans_rev_po (map<unsigned int, pt_node_index> & nreach_worklist, map<pt_node_index, unsigned int> & nodes_rev_po, set<pt_node_index> & ext_bndry, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<set<pt_node_index> > & summ_cmpts, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
	void pull_new_ans (set<pt_node_index> & nvisit, set<pt_node_index> & ext_bndry, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<pt_node_index> & ext_bndry_pulled_nodes, set<set<pt_node_index> > & summ_cmpts, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
#if SUMM_K_CONSISTENT
	bool compute_new_summ_cmpts (pt_fi_node & pt_n, set<pt_node_index> & ext_bndry, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, max_depth> & new_pt_to_max_depth, set<set<pt_node_index> > & summ_cmpts);
	void compute_new_summ_cmpts (set<pt_node_index> & nvisit, set<pt_node_index> & ext_bndry, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, max_depth> & new_pt_to_max_depth, set<set<pt_node_index> > & summ_cmpts);
	void compute_summ_cmpts_map (set<set<pt_node_index> > & summ_cmpts, map<pt_node_index, pt_node_index> & summ_cmpts_map);
	void remove_wild_card_subsumed_aps (access_name & pt_access_name);
#elif SUMM_TYPE_CLOSURE
	void set_ap_static_name (pt_node_index pt_nid, access_name & pt_access_name);
#endif
	void pull_new_an (set<pt_node_index> & nvisit, set<pt_node_index> & ext_bndry, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
	bool pull_new_an (pt_fi_node & pt_n, set<pt_node_index> & ext_bndry, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, set<pt_node_index> & ext_bndry_pulled_nodes, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
#if SUMM_TYPE_K && PULL_ACCESS_NAME == 0
	void push_an_subgraph (pt_node_index pt_nid, set<pt_node_index> & ext_bndry, set<pt_node_index> & nreach, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<set<pt_node_index> > & summ_cmpts, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
	void push_an_subgraph (pt_node_index pt_nid, set<pt_node_index> & new_succ_nodes, set<pt_node_index> & ext_vis_nodes, set<pt_node_index> & ext_bndry, set<pt_node_index> & nreach, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<set<pt_node_index> > & summ_cmpts, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
	void push_new_an_subgraph (set<pt_node_index> & nvisit, set<pt_node_index> & ext_bndry, set<pt_node_index> & nreach, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<set<pt_node_index> > & summ_cmpts, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
	void push_an_edge (pt_fi_node & pt_n, set<pt_node_index> & new_succ_nodes, set<pt_node_index> & ext_bndry, set<pt_node_index> & nreach, pt_node_set & value_in, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, def_stmt_set ds, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
	bool push_an_edge (pt_node_index src_nid, label out_label, pt_node_index dest_nid, set<pt_node_index> & ext_bndry, set<pt_node_index> & nreach, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
#endif

	bool is_unused_heap_node (pt_node_index pnid);

public:

	points_to_analysis_fi (bool is_val_context);
	~points_to_analysis_fi ();
	pt_fi_graph * get_g_pt ();
	ap_fi_graph * get_g_ap ();
	pt_access_fi_map * get_pt_access_map ();
	void preprocess_and_parse_program ();
	void delete_local_variables (struct cgraph_node * src_function, struct cgraph_node * dest_function, pt_node_set & out_value, void * new_clone); 
	void delete_nodes_and_info (set<label> & vars, pt_node_set & out_value, map<pt_node_index, pt_node_index> & new_clone);

	void append_clone_map (map<pt_node_index, pt_node_index> & new_clone, context<pt_node_set, variables> & current_context);
	void append_clone_map (map<pt_node_index, set<pt_node_index> > & new_clone, context<pt_node_set, variables> & current_context);

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
	bool is_node_strictly_stronger (pt_node_index n1, pt_node_index n2, set<pt_node_index> & valid_nodes);
	bool is_node_stronger (pt_node_index n1, pt_node_index n2, set<pt_node_index> & valid_nodes);
	bool is_edge_strictly_stronger (label f, pt_node_index m1, pt_node_index n1, pt_node_index m2, pt_node_index n2, set<pt_node_index> & valid_nodes);
	bool is_node_ap_strictly_stronger (pt_node_index n1, pt_node_index n2);
	bool is_edge_compatible (pt_node_index m, label f, pt_node_index n);
	void kill_weak_access_nodes (pt_node_set & valid_nodes);
	void find_weak_access_nodes (set<pt_node_index> & valid_nodes, set<pt_node_index> & weak_access_nodes, set<pt_node_index> & optimum_valid_nodes);
	void insert_strictly_stronger_edges (pt_node_index n1, set<pt_node_index> & valid_nodes, set<pt_node_index> & optimum_valid_nodes, set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges);
	void insert_strictly_stronger_in_edges (pt_node_index n1, pt_node_index strictly_stronger_n1, set<pt_node_index> & valid_nodes, set<pt_node_index> & optimum_valid_nodes, set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges);
	void insert_strictly_stronger_out_edges (pt_node_index n1, pt_node_index strictly_stronger_n1, set<pt_node_index> & valid_nodes, set<pt_node_index> & optimum_valid_nodes, set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges);
	void replace_strictly_stronger_edge (label f, pt_node_index m1, pt_node_index n1, pt_node_index m2, pt_node_index n2, set<pt_node_index> & valid_nodes, set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges);
#endif
	
	unsigned int get_max_acyclic_ap_len (set<pt_node_index> & pt_nodes);
	void get_max_acyclic_ap_len (pt_node_index pnid, unsigned int pnid_curr_len, set<pt_node_index> & valid_nodes, map<pt_node_index, map<label, set<pt_node_index> > > visited_edges, map<pt_node_index, unsigned int> & max_acyclic_len);
	void get_max_acyclic_ap_len (pt_node_index pnid, unsigned int pnid_curr_len, set<pt_node_index> & valid_nodes, set<pt_node_index> visited_nodes, map<pt_node_index, unsigned int> & max_acyclic_len);
	void get_max_acyclic_ap_len (pt_node_index pnid, set<pt_node_index> & valid_nodes, set<pt_node_index> & visited_nodes, map<pt_node_index, unsigned int> & height);
	void get_non_temp_ap_alias_set (map<list<label>, list<list<label> > > & ap_alias_set, map<list<label>, list<list<label> > > & ap_alias_set_non_temp);
	void get_non_temp_ap_alias_set (map<list<label>, set<list<label> > > & ap_alias_set, map<list<label>, set<list<label> > > & ap_alias_set_non_temp);
	void get_useful_ap_alias_set (map<list<label>, set<list<label> > > & in_ap_alias_set, basic_block current_block, map<list<label>, list<list<label> > > & repeating_useful_ap_alias_set);
	// void get_useful_pt_ap_nodes (set<pt_node_index> & in_values, unsigned int index, bool is_assignment_index, set<ap_node_index> & useful_ap_nodes, set<pt_node_index> & useful_pt_nodes);
	// void get_useful_rhs_pt_ap_nodes (set<pt_node_index> & in_values, constraint_expr & rhs, set<ap_node_index> & rhs_ap_nodes, set<pt_node_index> & rhs_pt_nodes);
	// void get_useful_lhs_pt_ap_nodes (set<pt_node_index> & in_values, constraint_expr & lhs, set<ap_node_index> & lhs_ap_nodes, set<pt_node_index> & lhs_pt_nodes);
	void get_useful_aps (unsigned int index, bool is_assignment_index, set<ap_node_index> & useful_ap_nodes, set<list<label> > & useful_ap_paths);
	void get_useful_rhs_ap_nodes (constraint_expr & rhs, set<ap_node_index> & rhs_ap_nodes, set<list<label> > & rhs_ap_paths);
	void get_useful_lhs_ap_nodes (constraint_expr & lhs, set<ap_node_index> & lhs_ap_nodes, set<list<label> > & lhs_ap_paths);
	bool is_useful_path (list<label> & ap, set<list<label> > & useful_path);
	void get_access_paths (set<pt_node_index> & ptn, map<pt_node_index, set<list<label> > > & node_aps, bool is_k);
	bool is_ap_valid_alias (list<label> & ap1);
	void get_k_access_paths (pt_node_index pnid, set<pt_node_index> & valid_nodes, map<pt_node_index, set<list<label> > > & node_aps);
	bool append_k_access_paths (pt_node_index src_id, label field, pt_node_index dest_id, map<pt_node_index, set<list<label> > > & node_aps);
	bool append_ap_field (list<label> ap, label field, pt_node_index dest_id, map<pt_node_index, set<list<label> > > & node_aps);
	void get_ap_alias_set (set<pt_node_index> & pt_nodes, set<list<label> > & useful_ap_paths, map<list<label>, set<list<label> > > & ap_alias_set);
	void get_access_path_pairs (set<pt_node_index> & pt_nodes, set<ap_node_index> & useful_ap_nodes, set<pair<list<label>, list<label> > > & ap_pairs, bool restrict_to_useful);
	void get_ap_pair (list<label> & ap1, list<label> & ap2, set<pair<list<label>, list<label> > > & ap_pairs);
	void print_fi_value ();
	void print_access_paths (map<pt_node_index, set<list<label> > > & node_aps);
	void print_ap_alias_set (map<list<label>, set<list<label> > > & ap_alias_set);
	void print_ap_alias_set (map<list<label>, list<list<label> > > & ap_alias_set);
	void print_clone_map (map<pt_node_index, pt_node_index> & clone);
	void print_clone_map (map<pt_node_index, set<pt_node_index> > & clone);
	void print_context_statistics (map<function_index, context_enums<pt_node_set, variables> > & function_contexts);
	void print_analysis_statistics (map<function_index, context_enums<pt_node_set, variables> > & function_contexts);
	void print_value (pt_node_set & ptn);

	void delete_aux_info (void * aux_info);	
};

#endif

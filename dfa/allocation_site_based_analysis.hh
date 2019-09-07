
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef ALLOCATION_SITE_BASED_ANALYSIS
#define ALLOCATION_SITE_BASED_ANALYSIS

#include "../misc/debug.hh"
#include "../misc/parser.hh"
#include "../misc/block_information.hh"
#include "../ipa/context.hh"
#include "../ipa/forward_inter_procedural_analysis.hh"
#include "../dfv/variables.hh"
#include "../dfv/deterministic_graph.hh"
#include "../dfv/unlabeled_edges.hh"
#include "../dfa/liveness_analysis.hh"
#include "../dfv/side_effects.hh"

#define dfv_stats_file "/home/vini/Work/Education/GCC/Installations/heap-analysis/plugins/hra-source/statistics/allocation_site_based_analysis/dfv_stats.hh"

struct unaffected_pta
{
	// This is inaccessible from any of the transitive calls i.e. it is
	// context indendent i.e., unused. Therefore, as per Hakajoo Oh, it is
	// bypassed based on reachability.
	unlabeled_edges context_indept;

	// This is not killed at any program point in the transitive callees
	// (assuming weak updates happen) but is context dependent i.e., used
	// by the function.
	// This is different from Hakajoo Oh in the sense that they pass directly
	// accessed vars, whereas we pass only directly def vars.
	unlabeled_edges context_dept;

	unaffected_pta ();
	~unaffected_pta ();
};

template <class LIVE_VALUE_TYPE>
class allocation_site_based_analysis : public forward_inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>
{
public:
	// For statistics, counting the total/max number of affected nodes, and
	// number of program points that affect nodes.
	unsigned int tot_stmttouch;
	unsigned int max_stmttouch;
	unsigned int tot_update_points;

        using inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::get_called_functions;
        using inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::process_assignment_statement;
        using inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::get_dependent_analysis;
        using inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::get_source_contexts;
        using inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::get_destination_contexts;
	using inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::delete_context_aux_info;
        using inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::set_blocks_order;
        using inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::check_and_delete_local_variables;
        using inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::get_dependent_context;
        using inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::get_dest_of_dept_context;
        using forward_inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::process_destination_context;
        using forward_inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE>::copy_in_to_out;

private:

	set<struct cgraph_node *> get_called_functions (context<unlabeled_edges, LIVE_VALUE_TYPE> & src_context, basic_block call_site, tree function_pointer);
	unlabeled_edges * initial_value ();
	unlabeled_edges * boundary_value ();
	void initialize_locals (unlabeled_edges & start_value_copy, context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context);

	void process_in_value (context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context, basic_block current_block);
	void process_call_statement (context<unlabeled_edges, LIVE_VALUE_TYPE> * src_context, basic_block call_site);
	void initialize_out_value (context<unlabeled_edges, LIVE_VALUE_TYPE> * src_context, basic_block call_site);
	bool is_dest_of_dept_context_exist (context<unlabeled_edges, LIVE_VALUE_TYPE> * src_context, basic_block call_site, struct cgraph_node * dest_function);
	void process_function_arguments (context<unlabeled_edges, LIVE_VALUE_TYPE> * src_context, basic_block call_site, unlabeled_edges * value, struct cgraph_node * called_function);
	void process_return_value (context<unlabeled_edges, LIVE_VALUE_TYPE> * src_context, basic_block call_site, unlabeled_edges * value, struct cgraph_node * called_function, bool to_kill);
	bool process_parsed_data (context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context, basic_block current_block, unlabeled_edges * calling_value, bool to_kill = true);
	bool process_assignment_statement (unlabeled_edges & value, context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context, basic_block current_block, unsigned int assignment_data_index, bool to_kill = true);
	void get_rhs_vars (unlabeled_edges & value, constraint_expr & rhs, set<label> & rhs_vars);
	void get_lhs_vars (unlabeled_edges & value, constraint_expr & lhs, set<label> & may_lhs_vars, set<label> & must_lhs_vars);
	void get_callees_glob_par_defs (context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context, set<variable_id> & callees_glob_par_defs);
	LIVE_VALUE_TYPE * get_live_out_value (context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context, basic_block current_block);
	
public:

	allocation_site_based_analysis (bool is_val_context);
	~allocation_site_based_analysis ();
	void preprocess_and_parse_program ();
	unlabeled_edges * extract_par_glob_reachable_value (struct cgraph_node * dest_function, unlabeled_edges & value);
	unlabeled_edges * extract_changing_context_dept_pta (context<unlabeled_edges, LIVE_VALUE_TYPE> & curr_context, unlabeled_edges & context_dept_pta);
	void remove_unaffected_context_dept_pta (context<unlabeled_edges, LIVE_VALUE_TYPE> & curr_context, unlabeled_edges & context_dept_pta);

	void restore_unaffected_context_dept_pta (context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context, unlabeled_edges & value);
	void restore_unaffected_context_dept_pta (context<unlabeled_edges, LIVE_VALUE_TYPE> & src_context, basic_block call_site, struct cgraph_node * dest_function, unlabeled_edges & value);

	LIVE_VALUE_TYPE * get_dept_function_in_value (struct cgraph_node * func);
	void delete_local_variables (struct cgraph_node * src_function, struct cgraph_node * dest_function, unlabeled_edges & out_value, void * info); 
	void get_live_data (unlabeled_edges & out_value, context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context, basic_block current_block);
	set<label> get_dead_variables (unlabeled_edges & value, context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context, basic_block current_block);
	void sync_pts_live_value (label pts_node, deterministic_node & live_node, unlabeled_edges & pts_value, deterministic_graph & live_value, map<label, set<deterministic_node *> > & sync_pts_live_nodes, set<label> & live_pts_nodes);
	void kill_dead_pts_edges (unlabeled_edges & pts_value, context<unlabeled_edges, deterministic_graph> & current_context, basic_block current_block);

	void delete_aux_info (void * aux_info);
	void print_aux_info (void * aux_info);
	void copy_unaffected_context_dept_aux (unlabeled_edges & src_value, context<unlabeled_edges, LIVE_VALUE_TYPE> & dest_context, bool is_erase_old);
	void copy_context_value (void * src_con, void * dest_con);
	void collect_callees_lhs_derefs ();
	void store_context_info (context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context);
	void save_context_indept_pta (context<unlabeled_edges, LIVE_VALUE_TYPE> & src_context, basic_block call_site, struct cgraph_node * dest_function, unlabeled_edges & context_indept_pta);
	void copy_context_indept_aux (unlabeled_edges & src_value, context<unlabeled_edges, LIVE_VALUE_TYPE> & dest_context);
	bool caller_to_callee_info (context<unlabeled_edges, LIVE_VALUE_TYPE> & con);
	void compute_lhs_derefs (context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context, set<variable_id> & lhs_derefs);
	void compute_alias_def_deref (variable_id var, label var_offset, basic_block current_block, context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context, set<variable_id> & lhs_derefs);
	bool callee_to_caller_info (context<unlabeled_edges, LIVE_VALUE_TYPE> & con);

	void get_reaching_vars (set<label> & vars, set<label> & reaching_vars, map<label, set<label> > & in_edge_list_1, map<label, set<label> > & in_edge_list_2, map<label, set<label> > & in_edge_list_3);
	void get_reaching_vars (label var, set<label> & reaching_vars, map<label, set<label> > & in_edge_list_1, map<label, set<label> > & in_edge_list_2, map<label, set<label> > & in_edge_list_3);

	void get_path_prefixes (list<label> & path, set<list<label> > & paths);
	void get_useful_paths (unsigned int index, bool is_assignment_index, set<list<label> > & useful_paths);
	void get_useful_rhs_paths (constraint_expr & rhs, set<list<label> > & rhs_paths);
	void get_useful_lhs_paths (constraint_expr & lhs, set<list<label> > & lhs_paths);
	void get_useful_ap_alias_set (map<list<label>, set<list<label> > > & in_ap_alias_set, basic_block current_block, map<list<label>, list<list<label> > > & repeating_useful_ap_alias_set);


	void get_dead_locals_stats ();
	unlabeled_edges * get_pts_context_indept_value (context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context);
	void get_points_to_in_value (context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context, basic_block current_block, unlabeled_edges & points_to_in);
	void print_bypassing_analysis_statistics (map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> > & function_contexts);
	void print_analysis_statistics (map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> > & function_contexts);
	void print_alias_analysis_statistics (map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> > & function_contexts);
	void dump_useful_aps (unsigned int funcid, basic_block current_block, FILE * dfv_stats_file_ptr);
	void dump_analysis (map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> > & function_contexts);

	void print_value (unlabeled_edges & value);
};

#endif

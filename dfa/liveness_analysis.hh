
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef LIVENESS_ANALYSIS
#define LIVENESS_ANALYSIS

#include "../misc/debug.hh"
#include "../misc/block_information.hh"
#include "../misc/parser.hh"
#include "../ipa/context.hh"
#include "../ipa/backward_inter_procedural_analysis.hh"
#include "../dfv/deterministic_graph.hh"
#include "../dfa/allocation_site_based_analysis.hh"

#define OPEN_FST_FILE "/home/vini/Work/Education/GCC/Installations/new-hra/out_graph"

template <class LIVE_VALUE_TYPE>
struct unaffected_live
{
        // This is inaccessible from any of the transitive calls i.e. it is
        // context indendent i.e., unused. Therefore, as per Hakajoo Oh, it is
        // bypassed based on reachability.
        LIVE_VALUE_TYPE context_indept;

        // This is not killed at any program point in the transitive callees
        // (assuming weak updates happen) but is context dependent i.e., used
        // by the function.
	// This is different from Hakajoo Oh in the sense that they pass
	// directly accessed vars on lhs/rhs, whereas we pass only directly
	// accessed vars on lhs only.
        LIVE_VALUE_TYPE context_dept;
};

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
class liveness_analysis : public backward_inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>
{
public:
	using inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::get_called_functions;
	using inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::get_dependent_analysis;
	using inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::get_dependent_context;
	using inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::get_source_contexts;
	using inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::delete_context_aux_info;
	using inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::process_assignment_statement;
	using inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::free_context_values;
	using inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::set_blocks_order;
	using inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::check_and_delete_local_variables;
	using inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::get_dest_of_dept_context;
	using backward_inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::copy_out_to_in;
	using backward_inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges>::process_destination_context;

private:

	set<struct cgraph_node *> get_called_functions (context<LIVE_VALUE_TYPE, unlabeled_edges> & src_context, basic_block call_site, tree function_pointer);
	LIVE_VALUE_TYPE * initial_value ();
	LIVE_VALUE_TYPE * boundary_value ();
	void process_call_statement (context<LIVE_VALUE_TYPE, unlabeled_edges> * src_context, basic_block call_site);
	void process_call_statement (LIVE_VALUE_TYPE & out_value, context<LIVE_VALUE_TYPE, unlabeled_edges> & src_context, basic_block asgn_call_block, basic_block io_context_block, struct cgraph_node * dest_function, bool to_kill);
	void initialize_in_value (context<LIVE_VALUE_TYPE, unlabeled_edges> * src_context, basic_block io_context_block);
	bool process_parsed_data (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, basic_block current_block, LIVE_VALUE_TYPE * returning_value, bool to_kill = true);
	bool process_use_statement (LIVE_VALUE_TYPE & value, context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, basic_block current_block, unsigned int variable_index);
	bool process_assignment_statement (LIVE_VALUE_TYPE & value, context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, basic_block current_block, unsigned int assignment_data_index, bool to_kill = true);
	set<LIVE_VALUE_SUBTYPE *> process_lhs (LIVE_VALUE_TYPE & value, context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, basic_block current_block, constraint_expr & lhs, bool to_kill, bool to_gen);
	void process_lhs_scalar (LIVE_VALUE_TYPE & value, constraint_expr & lhs, bool to_kill, set<LIVE_VALUE_SUBTYPE *> & lvalue_nodes);
	void process_lhs_deref (LIVE_VALUE_TYPE & value, constraint_expr & lhs, bool to_kill, set<LIVE_VALUE_SUBTYPE *> & lvalue_nodes);
	void process_rhs (LIVE_VALUE_TYPE & value, unsigned int assignment_data_index, constraint_expr & rhs, LIVE_VALUE_SUBTYPE & lvalue_node, LIVE_VALUE_TYPE & lvalue_graph);
	LIVE_VALUE_TYPE * get_unaffected_live_value (context<LIVE_VALUE_TYPE, unlabeled_edges> & current_context);
	unlabeled_edges * get_points_to_in_value (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, basic_block current_block);
	void process_link_alias_lhs (LIVE_VALUE_TYPE & value, context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, basic_block current_block, constraint_expr & lhs, set<LIVE_VALUE_SUBTYPE *> & link_alias_lvalue_nodes);
	void generate_alias_closure (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, basic_block current_block);
	void get_live_pts_nodes (LIVE_VALUE_TYPE & live_value, unlabeled_edges & pts_value, set<label> & reaching_nodes);
	void generate_live_access_paths (LIVE_VALUE_TYPE & live_value, unlabeled_edges & pts_value, set<label> & valid_pts_nodes);
	void generate_live_edge (label pts_src_nid, LIVE_VALUE_SUBTYPE & live_src_node, LIVE_VALUE_TYPE & live_value, unlabeled_edges & pts_value, set<label> & valid_pts_nodes, set<pair<label, label> > & visited_pts_live_nodes);
	void generate_live_edge (label pts_src_nid, LIVE_VALUE_SUBTYPE & live_src_node, label l, LIVE_VALUE_TYPE & live_value, unlabeled_edges & pts_value, set<label> & valid_pts_nodes, set<pair<label, label> > & visited_pts_live_nodes);

	void sync_pts_live_value (unlabeled_edges & pts_value, LIVE_VALUE_TYPE & live_value, map<label, set<LIVE_VALUE_SUBTYPE *> > & sync_pts_live_nodes);
	void sync_pts_live_value (unlabeled_edges & pts_value, LIVE_VALUE_TYPE & live_value, map<label, set<LIVE_VALUE_SUBTYPE *> > & sync_pts_live_nodes, set<label> & internal_live_pts_nodes, set<label> & leaf_live_pts_nodes);
	void sync_pts_live_value (label pts_node, LIVE_VALUE_SUBTYPE & live_node, unlabeled_edges & pts_value, LIVE_VALUE_TYPE & live_value, map<label, set<LIVE_VALUE_SUBTYPE *> > & sync_pts_live_nodes, set<label> & internal_live_pts_nodes, set<label> & leaf_live_pts_nodes);

public:
	
	void delete_local_variables (struct cgraph_node * src_function, struct cgraph_node * dest_function, LIVE_VALUE_TYPE & in_value, void * info);	
	bool is_dest_of_dept_context_exist (context<LIVE_VALUE_TYPE, unlabeled_edges> * src_context, basic_block call_site, struct cgraph_node * dest_function);
	void process_function_arguments (context<LIVE_VALUE_TYPE, unlabeled_edges> * src_context, basic_block call_site, LIVE_VALUE_TYPE * value, struct cgraph_node * called_function);
	void process_return_value (context<LIVE_VALUE_TYPE, unlabeled_edges> * src_context, basic_block call_site, LIVE_VALUE_TYPE * value, struct cgraph_node * called_function, bool to_kill);
	LIVE_VALUE_TYPE * extract_def_deref_ret_rooted_value (context<LIVE_VALUE_TYPE, unlabeled_edges> & src_context, struct cgraph_node * called_function, LIVE_VALUE_TYPE & value_out);
	void * get_dept_context_aux (struct cgraph_node * func);	
	LIVE_VALUE_TYPE * extract_changing_context_dept_live (context<LIVE_VALUE_TYPE, unlabeled_edges> & curr_context,	LIVE_VALUE_TYPE & context_dept_live);
	void copy_unaffected_context_dept_aux (LIVE_VALUE_TYPE & src_graph, context<LIVE_VALUE_TYPE, unlabeled_edges> & dest_context,bool is_erase_old);
	void copy_unaffected_context_dept_live (context<LIVE_VALUE_TYPE, unlabeled_edges> & src_context, basic_block call_site, struct cgraph_node * dest_function, LIVE_VALUE_TYPE & value);
	void free_context_analysis_values (context<LIVE_VALUE_TYPE, unlabeled_edges> & curr_context);

	void print_aux_info (void * aux_info);
	void delete_aux_info (void * aux_info);

        void copy_context_value (void * src_con, void * dest_con);
        void save_context_indept_live (context<LIVE_VALUE_TYPE, unlabeled_edges> & src_context, basic_block call_site, struct cgraph_node * dest_function, LIVE_VALUE_TYPE & context_indept_live);
        void copy_context_indept_aux (LIVE_VALUE_TYPE & src_value, context<LIVE_VALUE_TYPE, unlabeled_edges> & dest_context);
	bool caller_to_callee_info (context<LIVE_VALUE_TYPE, unlabeled_edges> & con);

	void copy_live_values (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, basic_block current_block, LIVE_VALUE_TYPE & all_live_values);
	void get_access_paths (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, basic_block current_block, set<list<label> > & all_aps, unsigned int & tot_aps, bool is_accum_aps);
	void print_value (LIVE_VALUE_TYPE & g);
	void get_access_paths_stats (set<list<label> > & aps, unsigned int & local_aps, unsigned int & global_aps);
	void get_pt_live_stats (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, basic_block current_block, LIVE_VALUE_TYPE & all_live_values, unsigned int & tot_program_aps_count, unsigned int & tot_pta_aps_count, unsigned int & tot_valid_aps_count, unsigned int (& valid_percent_func_count)[21], map<function_index, unsigned int> & func_pta, float & valid_percent, unsigned int & pt_aps_locals, unsigned int & pt_aps_globals, unsigned int & valid_aps_locals, unsigned int & valid_aps_globals);
	void print_analysis_statistics (map<function_index, context_enums<LIVE_VALUE_TYPE, unlabeled_edges> > & function_contexts);
	liveness_analysis (bool is_val_context);
	~liveness_analysis ();
	void preprocess_and_parse_program ();
};

#endif

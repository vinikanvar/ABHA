
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef UNLABELED_EDGES
#define UNLABELED_EDGES

#include "../misc/debug.hh"
#include "../misc/parser.hh"

typedef unsigned int label;
typedef unsigned int variable_id;

#if ALLOC_STATISTICS_CONTAINER
struct dead_locals_statistics
{
	// Dead locals in the points-to graph
	set<label> dead_locals_pta;
	// Dead locals at the program point
	set<label> dead_locals_pp;
	// Live locals at the program point
	set<label> live_locals_pp;

	unsigned int tot_dead_locals_pta;
	unsigned int tot_dead_locals_pp;
	unsigned int tot_live_locals_pp;

	// Number of times liveness based filtering is performed
	unsigned int tot_filterings;
};
extern dead_locals_statistics dead_locals_stats;
#endif

class unlabeled_edges
{
public:
	map<label, set<label> > out_edge_list;

	// This is populated only at fixpoint
	map<label, set<label> > in_edge_list;

        // Count of the number of program points which reference to this data
        // flow value.
        unsigned int reference_count;

public:

	unlabeled_edges ();
	~unlabeled_edges ();

	void erase ();
	void increment_reference_count ();
	void decrement_reference_count ();
	bool is_value_same (unlabeled_edges & value);
	unlabeled_edges * copy_value (bool is_loop_merge);
	void copy_value (unlabeled_edges & value, bool is_loop_merge);
	void clean ();

	void gen (label variable, set<label> & dest_vars);
	void gen (set<label> & variables, set<label> & dest_vars);
	void kill (label variable);
	void kill (set<label> & variables);
	void kill_pointees (set<label> & pointees);
	void kill_out_edges (unlabeled_edges & value);
	void kill_dead_pts_edges (set<label> & live_pts_nodes);
	void get_destination_vars (label variable, set<label> & dest_vars);
	void get_destination_vars (set<label> & vars, set<label> & dest_vars);
	void get_pointer_vars (label variable, label offset, set<label> & pointer_vars);
	static void get_points_to_pairs_statistics (map<label, set<label> > & points_to_pairs, unsigned int & tot_ptee_count, unsigned int & tot_local_ptee_count, unsigned int & tot_global_ptee_count, unsigned int & tot_heap_ptee_count, unsigned int & tot_ptr_count, unsigned int & tot_local_ptr_count, unsigned int & tot_global_ptr_count, unsigned int & tot_heap_ptr_count);
	void get_field_vars (label var, tree var_type, label offset, set<label> & pointer_vars);
	void get_heap_field_vars (label var, tree var_type, label offset, set<label> & pointer_vars);
	void get_deref_vars (label variable, label offset, set<label> & dest_vars);
	void get_must_pointer_vars (label variable, label offset, set<label> & dest_nodes);
	label get_single_pointee (set<label> & dest_vars);


	unlabeled_edges * extract_value (set<label> & reachable_from_vars, set<label> & destination_of_vars);
	void get_reachable_vars (set<label> & vars, set<label> & reachable_vars);
	void get_reachable_vars (label var, set<label> & reachable_vars);
	void extract_destination_edges (set<label> & vars, unlabeled_edges & destination_value);
	void get_reaching_vars (set<label> & vars, set<label> & reaching_vars);
	void get_reaching_vars (label var, set<label> & reaching_vars);
	void compute_in_edge_list ();

	static void get_field_statistics (label var, unsigned int & field_count, set<label> & visited_nodes);
	static void get_valid_graph_statistics (map<label, set<label> > & valid_points_to_pairs, unsigned int & count_explicit_valid_nodes, unsigned int & count_explicit_valid_edges, unsigned int & count_valid_nodes, unsigned int & count_valid_edges);
	static void get_used_points_to_pairs (map<label, set<label> > & points_to_pairs, basic_block bb, map<label, set<label> > & used_points_to_pairs);
	static void get_context_used_points_to_pairs_statistics (map<unsigned int, map<label, set<label> > > & context_used_points_to_pairs, float & avg_context_ptr_used_ptees, float & avg_context_local_ptr_used_ptees, float & avg_context_global_ptr_used_ptees, float & avg_context_heap_ptr_used_ptees);
	void get_graph_statistics (map<label, set<label> > & in_block_points_to_pairs);
	void get_graph_statistics (unsigned int & max_num_nodes, float & max_avg_out_edges, map<label, set<label> > & program_points_to_pairs, map<label, set<label> > & program_root_aliases, set<set<list<int> > > & program_aliases, map<label, set<label> > & program_reachable_roots, map<list<label>, set<list<label> > > & ap_alias_set, map<map<label, set<label> >, map<list<label>, set<list<label> > > > & memoized_points_to_alias, bool print);
	static unsigned int get_max_acyclic_ap_len (map<label, set<label> > & points_to_edges);
	static void get_max_acyclic_ap_len (label var, unsigned int var_curr_len, map<label, set<label> > & points_to_edges, map<label, set<label> > visited_points_to_edges, map<label, set<label> > visited_field_edges, map<label, unsigned int> & max_acyclic_len);
	static void get_max_acyclic_ap_len (label var, map<label, set<label> > & points_to_edges, set<label> & visited_nodes, map<label, unsigned int> & height);
	bool append_k_access_paths (label src, label field, label dest, map<label, set<list<label> > > & var_aps);
	static void append_ap_field (list<label> & ap, label field);
	void append_acyclic_access_paths (label src, label field, label dest, map<label, set<list<label> > > & var_aps);
	void get_access_paths (map<label, set<list<label> > > & var_aps, bool is_k);
	void get_ap_alias_set (map<list<label>, set<list<label> > > & ap_alias_set);
	static bool is_useful_path (list<label> & ap, set<list<label> > & useful_path);
	bool is_ap_valid_alias (list<label> & ap1);
	void get_ap_pair (list<label> & ap1, list<label> & ap2, set<pair<list<label>, list<label> > > & ap_pairs);
	static void get_non_temp_ap_alias_set (map<list<label>, set<list<label> > > & ap_alias_set, map<list<label>, set<list<label> > > & ap_alias_set_non_temp);
	static void get_non_temp_ap_alias_set (map<list<label>, list<list<label> > > & ap_alias_set, map<list<label>, list<list<label> > > & ap_alias_set_non_temp);
	void get_k_access_paths (label var, map<label, set<list<label> > > & var_aps);
	void get_acyclic_access_paths (label var, set<label> visited_nodes, map<label, set<list<label> > > & var_aps);

	void collect_aps (map<label, set<list<label> > > & var_aps, set<list<label> > & all_aps);
	void get_access_paths (set<list<label> > & aps, struct cgraph_node * cnode);
	void get_k_access_paths (label var, map<label, set<list<label> > > & sent_var_aps, map<label, set<list<label> > > & new_var_aps);
	void push_k_access_paths (set<list<label> > & src_aps, label src_field, label in_field, map<label, set<list<label> > > & sent_var_aps, map<label, set<list<label> > > & new_var_aps);
	bool append_k_access_paths (set<list<label> > & src_aps, label field, label dest, map<label, set<list<label> > > & sent_var_aps, map<label, set<list<label> > > & new_var_aps);

	void count_dead_vars (set<label> & variables);
	static void print_ap_alias_set (map<list<label>, list<list<label> > > & ap_alias_set);
	static void print_ap_alias_set (map<list<label>, set<list<label> > > & ap_alias_set);
	void print_access_paths (map<label, set<list<label> > > & var_aps);
	void print_access_paths (set<list<label> > & aps);
	static void print_access_path (list<label> & ap);

	static unsigned int compare_memoized_value (map<label, set<label> > & out_edges, map<map<label, set<label> >, set<pair<list<label>, list<label> > > > & memoized_points_to_alias);
	static unsigned int print_memoized_value (map<map<label, set<label> >, set<pair<list<label>, list<label> > > > & memoized_points_to_alias);
	static void print_points_to_pairs (map<label, set<label> > & points_to_pairs);
	static void print_points_to_pairs (label ptr, map<label, set<label> > & points_to_pairs);
	static void print_used_points_to_pairs (map<label, set<label> > & points_to_pairs, basic_block bb);
	static unsigned int print_points_to_pairs (map<label, set<label> > & points_to_pairs, set<label> & heap_to_stack_pointees);
	void print_value (FILE * file);

	void dump_data_flow_value (unsigned int funcid, unsigned int bbid, unsigned int bbio, FILE * edge_file_ptr,	FILE * heap_file_ptr, FILE * unique_edge_file_ptr, set<map<label, map<label, set<label> > > > & unique_points_to_graphs);
	void dump_unique_data_flow_value (map<label, map<label, set<label> > > & dfg, set<map<label, map<label, set<label> > > > & unique_points_to_graphs, FILE * unique_edge_file_ptr);
};

#endif

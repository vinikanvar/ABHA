
/************************
 * @author Vini Kanvar
************************/

/* This class is simple in the sense that it does not use UNDEF/JUNK node of
 * [KMR12]*/
//HK Algo

#include "../common.hh"

#ifndef NON_DETERMINISTIC_SIMPLE_GRAPH
#define NON_DETERMINISTIC_SIMPLE_GRAPH

#include "../misc/debug.hh"
#include "../dfv/non_deterministic_simple_node.hh"

typedef unsigned int node_index;

class non_deterministic_simple_graph
{
public:

	// STACK is required. The root node of the graph is not always the first
	// entry of the map of NODES. For example, when a part of the graph is
	// extracted.
	non_deterministic_simple_node * stack;
	map<node_index, non_deterministic_simple_node *> nodes;

	// Count of the number of program points which reference to this data
	// flow value.
	unsigned int reference_count;

public:

	non_deterministic_simple_graph ();
	~non_deterministic_simple_graph ();

	void increment_reference_count ();
	void decrement_reference_count ();

	bool is_element (label v);
	void clean ();
	set<node_index> clean_unreachable_nodes ();
	void clean_useless_nodes ();
	void clean_disconnected_nodes ();
	void subsume_in_universal ();
	void subsume_in_universal_pointees (set<node_index> & pointees);
	void remove_pointers_with_universal_pointees (set<node_index> & pointers, label l);
	void delete_local_variables (set<label> & local_variables);
	set<label> get_dead_graph_variables (set<label> & dead_variables);
	void get_structurally_dead_variables (set<label> & dead_graph_variables);
	void delete_dead_pointers (set<label> & dead_graph_variables);
	set<node_index> get_arg_glob_connected_nodes (set<unsigned int> arg_glob_vars);
	non_deterministic_simple_graph * extract_arg_glob_connected_graph (set<node_index> arg_glob_connected_nodes);
	void transfer_connected_edges (non_deterministic_simple_node * src_node, non_deterministic_simple_node * dest_node, set<node_index> & connected_nodes);
	non_deterministic_simple_graph * copy_value (bool is_loop_merge);
        void copy_value (non_deterministic_simple_graph & g, bool is_loop_merge);
	map<node_index, node_index> copy_nodes (non_deterministic_simple_graph & g);
	void copy_edges (non_deterministic_simple_graph & g, map<node_index, node_index> & copy_nodes_map);
	void merge_graph (non_deterministic_simple_graph & g, non_deterministic_simple_node & n, map<node_index, node_index> & copy_nodes_map, set<node_index> & visited_nodes, bool is_loop_merge);
	bool merge_nodes (non_deterministic_simple_node & n1, non_deterministic_simple_node & n2, bool is_loop_merge);
	node_index merge_with_sibling_nodes (non_deterministic_simple_node & n, bool is_loop_merge);
	void merge_child_nodes (non_deterministic_simple_node & n, bool is_loop_merge);
	void m_limit_graph (int m_limit);

	set<label> get_pointees (label pointer);
	void generate_addressof_nodes (label variable, set<node_index> & addr_nodes);
	void generate_addressof_field_nodes (label variable, set<node_index> & addr_nodes);
	void get_addressof_nodes (label variable, set<node_index> & addr_nodes);
	bool get_pointer_nodes (label variable, list<label> * field_sequence, set<node_index> & pointer_nodes);
	void generate_pointer_nodes (label variable, list<label> * field_sequence, set<node_index> & pointer_nodes);
	void get_must_pointer_nodes (label variable, list<label> * field_sequence, set<node_index> & destination_nodes);
	bool get_deref_nodes (label variable, list<label> * field_sequence, set<node_index> & destination_nodes);
	void generate_deref_nodes (label variable, list<label> * field_sequence, set<node_index> & destination_nodes);
	void get_field_nodes (set<node_index> & s, label field, set<node_index> & field_nodes);
	void generate_field_nodes (set<node_index> & s, tree s_type, label field, set<node_index> & field_nodes);
	void generate_heap_field_nodes (node_index heap_node_id, tree heap_pointer_type, label field, set<node_index> & heap_field_nodes);
	set<node_index> generate_field_nodes (set<node_index> & s, label field);
	bool get_destination_nodes (set<node_index> & s, label l, set<node_index> & destination_nodes);
	bool substitute_universal_node (set<node_index> & s);
	void get_in_nodes (set<node_index> & pointees, set<node_index> & in_nodes);
	set<node_index> get_var_node (label var);
	void get_nodes_names (set<node_index> & s, set<label> & names);

	void delete_out_edges (set<node_index> source_nodes, label l);
	void delete_out_edges (non_deterministic_simple_node & n, label l);
	void delete_in_edges (non_deterministic_simple_node & n, label l);
	void insert_edges (set<node_index> lhs_nodes, set<node_index> rhs_nodes, label l);
	void insert_field_edges (set<node_index> & src_ndoes, csvarinfo_t src_var);
	void initialize (set<label> & vars, label init_value);
	bool is_value_same (non_deterministic_simple_graph & g);
	bool is_in_value_same (non_deterministic_simple_graph & g);
	bool is_inout_value_same (non_deterministic_simple_graph & g);
	bool get_equivalent_states (non_deterministic_simple_graph & g, map<state_index, state_index, state_order> & equiv_state_pairs);
	bool get_equivalent_states (state_index & s1, state_index & s2, non_deterministic_simple_graph & g1, non_deterministic_simple_graph & g2, map<state_index, state_index, state_order> & equiv_state_pairs);
	bool get_equivalent_nodes (map<state_index, state_index, state_order> & equiv_state_pairs, map<node_index, node_index> & equiv_node_pairs);
	bool map_equivalent_nodes (state_index & s1, state_index & s2, map<state_index, state_index, state_order> & equiv_state_pairs, map<node_index, node_index> & equiv_node_pairs);
	// bool get_equivalent_nodes (int index, map<state_index, state_index, state_order> & equiv_state_pairs, map<node_index, pair<node_index, int> > & equiv_node_pairs);
	// bool permute_and_map_equivalent_nodes (vector<node_index> & s1, int i, vector<node_index> & s2, map<state_index, state_index, state_order> & equiv_state_pairs, int index, map<node_index, pair<node_index, int> > & equiv_node_pairs); 
	// bool map_equivalent_nodes (vector<node_index> & s1, vector<node_index> & s2, int index, map<node_index, pair<node_index, int> > & equiv_node_pairs);
	// void unmap_nodes (int index, map<node_index, pair<node_index, int> > & equiv_node_pairs);
	// void swap_nodes (vector<node_index> & s, int i, int j);

	bool are_improper_nodes_okay ();
	bool is_in_comparison_okay (non_deterministic_simple_graph & g, map<node_index, node_index> & equiv_node_pairs, map<state_index, state_index, state_order> & equiv_state_pairs);
	bool is_in_comparison_weaker (non_deterministic_simple_graph & g, map<node_index, node_index> & equiv_node_pairs, map<state_index, state_index, state_order> & equiv_state_pairs, bool reverse_node_property);
	bool is_inout_comparison_okay (non_deterministic_simple_graph & g, map<node_index, node_index> & equiv_node_pairs);
	bool is_inout_comparison_okay (non_deterministic_simple_graph & g, map<node_index, node_index> & equiv_node_pairs, map<state_index, state_index, state_order> & equiv_state_pairs);
	bool is_every_node_paired (map<node_index, node_index> & equiv_node_pairs);
	bool is_graph_okay ();
	bool is_node_unmerged (non_deterministic_simple_node & nodei);
	void get_access_paths (node_index node_id, list<int> in_path, set<list<int> > & populated_paths, set<node_index> & gray_nodes, set<node_index> & black_nodes);
	void get_node_aliases (node_index node_id, list<int> out_path, set<list<int> > & populated_paths, set<node_index> & gray_nodes, set<node_index> & black_nodes);
	void get_access_paths (map<list<int>, set<node_index> > & access_paths_map);
	void print_access_path (list<int> path);
	void print_access_paths ();
	void get_aliases (set<set<list<int> > > & set_of_aliases, set<set<list<int> > > & program_aliases);
	void print_aliases (set<set<list<int> > > & set_of_aliases);
	non_deterministic_simple_graph * get_compact_graph ();
	void get_reachable_roots (map<label, set<label> > & reachable_roots, map<label, set<label> > & program_reachable_roots);
	void print_kill_nodes (set<node_index> & kill_nodes);
	void print_reachable_roots (map<label, set<label> > & reachable_roots);
	bool is_reachable (label l1, label l2);
	void get_root_aliases (map<label, set<label> > & root_aliases, map<label, set<label> > & program_root_aliases);
	unsigned int print_root_aliases (map<label, set<label> > & root_aliases);
	void get_points_to_pairs (map<pair<label, label>, set<label> > & points_to_pairs);
	void get_points_to_pairs (set<node_index> & s, map<pair<label, label>, set<label> > & points_to_pairs);
	void get_points_to_pairs (non_deterministic_simple_node & src, map<pair<label, label>, set<label> > & points_to_pairs);
	void print_points_to_pairs (map<pair<label, label>, set<label> > & points_to_pairs, bool one_per_line);
	float count_average_out_edges ();
	void get_nodes_edges (unsigned int & max_num_nodes, float & max_avg_out_edges, bool print);
	void get_graph_statistics (unsigned int & max_num_nodes, float & max_avg_out_edges, map<pair<label, label>, set<label> > & program_points_to_pairs, map<label, set<label> > & program_root_aliases, set<set<list<int> > > & program_aliases, map<label, set<label> > & program_reachable_roots, bool print);
	void print_value (const char * file);

private:

	void delete_in_edges (non_deterministic_simple_node & n);
};

#endif

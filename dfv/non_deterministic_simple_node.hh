
/************************
 * @author Vini Kanvar
************************/

/* This class is simple in the sense that it does not use UNDEF/JUNK node of
 * [KMR12]*/
// HK Algo

#include "../common.hh"

#ifndef NON_DETERMINISTIC_SIMPLE_NODE
#define NON_DETERMINISTIC_SIMPLE_NODE

#include "../misc/debug.hh"
#include "../misc/parser.hh"

typedef unsigned int node_index;
typedef unsigned int label;
//typedef HOST_WIDE_INT label;

// Are two values considered equal based on in-node-properties or
// in-out-node-properties? INOUT uses DEPTH_FIRST_COMPARISON () along with
// matching the node's in-property.
enum value_properties {in, inout};
const value_properties value_property = in;
// Are two nodes considered equal based on their in-language or their
// in-graph-structure? Note that our analysis does not consider merging of
// nodes based on out-properties.
enum node_properties {in_language, in_isomorphism, name};
//const node_properties node_property = in_language;
const node_properties node_property = name;

typedef set<node_index> state_index;

// To keep EQUIV_STATE_PAIRS sorted by cardinality
struct state_order
{
	bool operator () (state_index a, state_index b)
	{
		if (a.size () < b.size ())
			return true;
		if (a.size () > b.size ())
			return false;
		if (a < b)
			return true;
		return false;
	}
};

class non_deterministic_simple_node
{
	node_index node_id;

	// Edges may contain cycles due to 
	// -- cyclic data structures
	// -- allocation site based heap allocation

	map<label, set<node_index> > in_edge_list;
	map<label, set<node_index> > out_edge_list;

public:

	static unsigned int number_of_nodes;

	non_deterministic_simple_node ();
	~non_deterministic_simple_node ();

	unsigned int get_node_id ();
	map<label, set<node_index> > get_out_edge_list ();
	map<label, set<node_index> > get_in_edge_list ();
	int count_in_edges ();
	int count_out_edges ();
	void get_reachable_nodes (node_index root, map<node_index, non_deterministic_simple_node *> & nodes_map, set<node_index> & reachable_nodes);
	void get_heap_reachable_nodes (node_index root, map<node_index, non_deterministic_simple_node *> & nodes_map, set<node_index> & reachable_nodes);
	void get_reaching_nodes (map<node_index, non_deterministic_simple_node *> & nodes_map, set<node_index> & reaching_nodes);
	non_deterministic_simple_node * get_acyclic_parent (map<node_index, non_deterministic_simple_node *> & nodes);
	bool is_acyclic_ancestor (node_index ancestor, map<node_index, non_deterministic_simple_node *> & nodes, set<node_index> & visited_nodes);
	void mark_connected_nodes (node_index root, map<node_index, non_deterministic_simple_node *> & nodes, set<node_index> & connected_nodes);
	bool is_node_nameless (node_index stack_id);
	bool is_node_useless (node_index stack_id);
	void delete_in_edges (label l);
	void delete_out_edges (label l);
	void delete_edge (label l, non_deterministic_simple_node & out_node);

	bool depth_first_comparison (non_deterministic_simple_node & n, map<node_index, non_deterministic_simple_node *> & this_nodes, map<node_index, non_deterministic_simple_node *> & n_nodes, map<node_index, node_index> & equiv_node_pairs, map<state_index, state_index, state_order> & equiv_state_pairs, bool reverse_node_property = false);
	bool depth_first_edge_comparison (non_deterministic_simple_node & n, label l, map<node_index, non_deterministic_simple_node *> & this_nodes, map<node_index, non_deterministic_simple_node *> & n_nodes, map<node_index, node_index> & equiv_node_pairs, map<state_index, state_index, state_order> & equiv_state_pairs, bool reverse_node_property);
	bool depth_first_node_comparison (set<node_index> nodes_list, map<node_index, non_deterministic_simple_node *> & this_nodes, map<node_index, non_deterministic_simple_node *> & n_nodes, map<node_index, node_index> & equiv_node_pairs, map<state_index, state_index, state_order> & equiv_state_pairs, bool reverse_node_property);
	bool is_in_graph_isomorphic (non_deterministic_simple_node & n, map<node_index, non_deterministic_simple_node *> & this_nodes, map<node_index, non_deterministic_simple_node *> & n_nodes, map<node_index, node_index> & equiv_node_pairs);
	bool is_in_edge_list_isomorphic (non_deterministic_simple_node & n, label l, map<node_index, non_deterministic_simple_node *> & this_nodes, map<node_index, non_deterministic_simple_node *> & n_nodes, map<node_index, node_index> & equiv_node_pairs);
	bool is_in_node_list_isomorphic (set<node_index> nodes_list, map<node_index, non_deterministic_simple_node *> & this_nodes, map<node_index, non_deterministic_simple_node *> & n_nodes, map<node_index, node_index> & equiv_node_pairs);
	bool is_in_language_same (node_index n1, node_index n2, map<state_index, state_index, state_order> & equiv_state_pairs);
	bool is_in_language_same (node_index root, state_index s1, state_index s2, map<node_index, non_deterministic_simple_node *> & nodes, set<set<state_index> > & equiv_states);
	bool only_temporary_reachable (label l, node_index nid, node_index root, map<node_index, non_deterministic_simple_node *> & nodes, set<node_index> & visited_nodes);
	bool are_different_temporary_nodes (non_deterministic_simple_node & n1, non_deterministic_simple_node & n2);
	void get_out_dfa_edges (node_index root, state_index state, map<label, state_index> & dfa_state_out_edges, map<node_index, non_deterministic_simple_node *> & nodes);
	void get_in_dfa_edges (node_index root, state_index state, map<label, state_index> & dfa_state_in_edges, map<node_index, non_deterministic_simple_node *> & nodes);
	bool are_states_merged (state_index & s1, state_index & s2, set<set<state_index> > & equiv_states);

	bool is_node_proper (non_deterministic_simple_node & n);
	bool are_nodes_improper (non_deterministic_simple_node & n1, non_deterministic_simple_node & n2);
	bool is_node_property_same (non_deterministic_simple_node & n, map<node_index, non_deterministic_simple_node *> & this_nodes, map<node_index, non_deterministic_simple_node *> & n_nodes, map<state_index, state_index, state_order> & equiv_state_pairs, bool reverse_node_property);
	bool is_node_property_same (non_deterministic_simple_node & n1, non_deterministic_simple_node & n2, map<node_index, non_deterministic_simple_node *> & nodes, bool is_loop_merge);

	bool get_destination_nodes (label l, node_index stack_id, set<node_index> & destination_nodes);
	bool get_destination_nodes (set<label> & labels, node_index stack_id, set<node_index> & destination_nodes);
	set<node_index> get_var_node (label var, label prefix_var, map<node_index, non_deterministic_simple_node *> & nodes);
	label get_node_name (node_index stack_id);
	void insert_edge (label l, non_deterministic_simple_node & dest, node_index stack_id);
	void transfer_in_edges (non_deterministic_simple_node & n, map<node_index, non_deterministic_simple_node *> & nodes, node_index stack_id);
	set<node_index> transfer_out_edges (non_deterministic_simple_node & n, map<node_index, non_deterministic_simple_node *> & nodes, node_index stack_id);
	void copy_node_edges (non_deterministic_simple_node & n, map<node_index, node_index> copy_nodes_map);

	bool is_in_language_comparison_okay (node_index root, state_index dfa_state, node_index n1, node_index n2, map<node_index, non_deterministic_simple_node *> & nodes, set<state_index> & visited_dfa_states);
	bool is_node_comparison_okay (non_deterministic_simple_node & n, map<node_index, non_deterministic_simple_node *> this_nodes, map<node_index, non_deterministic_simple_node *> n_nodes, map<node_index, node_index> equiv_node_pairs);
	bool is_edge_comparison_okay (node_index matching_node_id, map<node_index, node_index> & equiv_node_pairs, map<label, set<node_index> > this_edges, map<label, set<node_index> > g_edges);
	void make_edge_deterministic (map<node_index, non_deterministic_simple_node *> & nodes, node_index stack_id);
        void print_node (const char * file, map<node_index, non_deterministic_simple_node *> & nodes);
        void print_node_reverse (const char * file);
};


#endif

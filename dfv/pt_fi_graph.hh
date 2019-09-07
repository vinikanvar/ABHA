
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef PT_FI_GRAPH
#define PT_FI_GRAPH

#include "../misc/debug.hh"
#include "../dfv/pt_fi_node.hh"

typedef unsigned int pt_node_index;
typedef pair<pt_node_index, pair<label, pt_node_index> > g_pt_edge;

class pt_fi_graph
{
public:

	map<pt_node_index, pt_fi_node *> 	nodes;
	pt_fi_node	 			stack;

	// These are named (local,global) and heap variable nodes that are not
	// pointed by any node, although these may be pointing to other nodes.
	// Exception: on-the-fly created heap field nodes may be pointed to by
	// other nodes.
	set<pt_node_index>			fresh_named_nodes;
	set<pt_node_index>			fresh_heap_nodes;

#if SUMM_TYPE_K
	// node partial order
	map<pt_node_index, set<pt_node_index> > 	strictly_stronger_nodes;
	// edge partial order
	map<g_pt_edge, set<g_pt_edge> >			strictly_stronger_edges;

	// node partial order. Used for stats. Do not reset this map.
	map<pt_node_index, set<pt_node_index> > 	program_strictly_stronger_nodes;
	// Used for stats. Total weak nodes in all calls and max weak
	// nodes at a call to find partial order.
	unsigned int 					tot_weak_nodes;
	unsigned int					tot_weak_strong_nodes;
	unsigned int					max_weak_nodes_at_pp;
	float						tot_avg_weak_nodes;
	unsigned int					po_calls;
#endif

public:

	pt_fi_graph ();
	~pt_fi_graph ();

	int get_max_node_id ();
#if SUMM_K_CONSISTENT
	void get_all_names (set<pt_node_index> & s, set<label> & names);
#endif
	void get_nodes_names (set<pt_node_index> & s, set<label> & names);
	label get_node_name (pt_node_index nid);
	void get_nodes (set<label> & variables, set<pt_node_index> & valid_nodes, set<pt_node_index> & var_nodes);
	set<pt_node_index> get_generated_nodes (int old_max_node_id);
	void get_fresh_named_nodes (set<pt_node_index> & var_nodes);
	bool is_fresh_named_node (pt_node_index pnid);
	bool is_fresh_heap_node (pt_node_index pnid);
	bool is_heap_node (pt_node_index pnid);
	void get_in_nodes (pt_node_index pointee, set<pt_node_index> & in_nodes);
	void get_in_nodes (pt_node_index dest_nid, label l, set<pt_node_index> & in_nodes, set<pt_node_index> & valid_nodes);
	void get_out_nodes (pt_node_index src_nid, label l, set<pt_node_index> & out_nodes, set<pt_node_index> & valid_nodes);
	bool get_destination_nodes (set<pt_node_index> & src_nodes, label l, set<pt_node_index> & dest_nodes);
	bool get_destination_nodes (set<pt_node_index> & src_nodes, label l, set<pt_node_index> & dest_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	void get_destination_nodes (pt_node_index src_node, label l, set<pt_node_index> & dest_nodes, set<pt_node_index> & valid_nodes);
	void get_destination_nodes (set<pt_node_index> & src_nodes, label l, set<pt_node_index> & dest_nodes, set<pt_node_index> & valid_nodes);
	bool get_destination_nodes (set<pt_node_index> & src_nodes, label l, set<pt_node_index> & dest_nodes, set<pt_node_index> & valid_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	void get_out_adj_nodes (set<pt_node_index> pt_nids, set<pt_node_index> & lptr, set<pt_node_index> & rptr, map<pt_node_index, map<label, set<pt_node_index> > > & invis_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & invis_out_edges, set<pt_node_index> & out_adj_nodes, set<pt_node_index> & valid_nodes);
	void get_in_out_adj_nodes (set<pt_node_index> & pt_n_proc, set<pt_node_index> & valid_nodes, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, set<pt_node_index> & rpte,  map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
#if SUMM_TYPE_CLOSURE == 0 && FILTER_EXISTING_EDGES
	void keep_new_edges (set<pt_node_index> & valid_nodes, set<pt_node_index> & must_lptr, set<pt_node_index> & lptr, label l, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
#endif
	set<pt_node_index> find_visit_nodes (set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<pt_node_index> & valid_nodes);
	void get_addressof_nodes (label variable, set<pt_node_index> & addr_nodes);
	void generate_addressof_nodes (set<label> & vars, set<pt_node_index> & var_nodes);
	void generate_addressof_nodes (label variable, set<pt_node_index> & addr_nodes);	
	void generate_fresh_addressof_nodes (label var, set<pt_node_index> & addr_nodes);
	void generate_addressof_field_nodes (label variable, set<pt_node_index> & addr_nodes);
	bool get_pointer_nodes (label variable, list<label> * field_sequence, set<pt_node_index> & pointer_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	bool get_deref_nodes (label variable, list<label> * field_sequence, set<pt_node_index> & destination_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	void generate_deref_nodes (label variable, list<label> * field_sequence, set<pt_node_index> & destination_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	void get_must_pointer_nodes (label variable, list<label> * field_sequence, set<pt_node_index> & destination_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<pt_node_index> & valid_nodes);
	void get_field_nodes (set<pt_node_index> & src_nids, label field, set<pt_node_index> & field_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	bool get_field_nodes (pt_node_index src_node, label field, set<pt_node_index> & field_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	bool get_field_nodes (pt_node_index src_node, tree src_pointer_type, label field, set<pt_node_index> & field_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);

	void get_field_nodes (set<pt_node_index> & src_nodes, tree src_pointer_type, label field, set<pt_node_index> & field_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	void generate_field_nodes (set<pt_node_index> & src_nodes, tree src_pointer_type, label field, set<pt_node_index> & field_nodes, map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_in_field_edges, map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_out_field_edges);
	void generate_field_nodes (pt_node_index src_node, tree src_pointer_type, label field, set<pt_node_index> & field_nodes, map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_in_field_edges, map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_out_field_edges);
	void generate_heap_field_nodes (pt_node_index heap_node_id, csvarinfo_t field_info, label field, map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_in_field_edges, map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_out_field_edges);
	void get_field_nodes (pt_node_index src_node, set<pt_node_index> & field_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
	void compute_new_field_edges (pt_node_index heap_node_id, tree root_type, map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_in_field_edges, map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_out_field_edges);

	set<label> get_pointees (label pointer, set<pt_node_index> & valid_nodes);
	set<pt_node_index> get_reachable_nodes (set<label> & vars, set<pt_node_index> & valid_nodes);
	void get_reachable_nodes (label var, set<pt_node_index> & reachable_nodes, set<pt_node_index> & valid_nodes);

	set<pt_node_index> get_reachable_nodes (set<pt_node_index> & nvisit, set<pt_node_index> & lptr, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<pt_node_index> & valid_nodes);
	set<pt_node_index> get_int_bndry_nodes (set<pt_node_index> & inside_nodes, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<pt_node_index> & valid_nodes);
	set<pt_node_index> get_ext_bndry_nodes (set<pt_node_index> & inside_nodes, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<pt_node_index> & valid_nodes);

	void insert_fresh_nodes (map<pt_node_index, bool> & new_nodes);
	void insert_field_edges (set<pt_node_index> & src_nodes, csvarinfo_t src_var);
	void insert_edges (set<pt_node_index> lhs_nodes, set<pt_node_index> rhs_nodes, label l);
	pt_fi_node * get_clone (pt_node_index nid, map<pt_node_index, pt_node_index> & clone);
	void clone_out_edges (pt_node_index nid, set<pt_node_index> & int_bndry_nodes, map<pt_node_index, set<pt_node_index> > & caller_callee_clone, set<pt_node_index> & valid_nodes, map<pt_node_index, set<pt_node_index> > & transitive_call_clone, map<pt_node_index, map<label, set<pt_node_index> > > & cloned_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & cloned_out_edges);
	void get_transitive_clones (pt_node_index nid, map<pt_node_index, set<pt_node_index> > & callee_clone, set<pt_node_index> & transformed_value, set<pt_node_index> & transitive_clones, set<pt_node_index> & visited_nodes);

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
	void clear_partial_order_info ();
	set<pt_node_index> get_strictly_stronger_nodes (pt_node_index n);
	bool is_node_strictly_stronger (pt_node_index n1, pt_node_index n2);
	bool is_edge_strictly_stronger (g_pt_edge e1, g_pt_edge e2);
	void add_strictly_stronger_edge (g_pt_edge e1, g_pt_edge e2);
	void add_strictly_stronger_node (pt_node_index n1, pt_node_index n2);
	void record_weak_nodes_statistics (unsigned int weak_nodes_count_pp, unsigned int weak_strong_nodes_count_pp);
	void print_partial_order_statistics ();
#endif
	void count_clones (unsigned int & tot_stack_clones, unsigned int & tot_heap_clones, unsigned int & max_stack_clones, unsigned int & max_heap_clones, unsigned int & tot_repeating_stack_vars, unsigned int & tot_repeating_heap_vars, bool all_valid);
	void count_clones (unsigned int & tot_stack_clones, unsigned int & tot_heap_clones, unsigned int & max_stack_clones, unsigned int & max_heap_clones, unsigned int & tot_repeating_stack_vars, unsigned int & tot_repeating_heap_vars, set<pt_node_index> & valid_nodes, bool all_valid = false);
	unsigned int count_graph_edges (set<pt_node_index> & valid_nodes);
	void print_statistics ();
	void get_points_to_pairs (set<pt_node_index> & pt_nodes, map<label, set<label> > & points_to_pairs, map<label, set<label> > & summ_stack_to_stack_pointers);
	unsigned int print_points_to_pairs (map<label, set<label> > & points_to_pairs, bool one_line, set<label> & heap_to_stack_pointees);
	void print_node_fields (FILE * file, map<pt_node_index, set <pair<label, pt_node_index> > > & field_edges, map<pt_node_index, pt_fi_node *> & nodes, pt_node_index stack_id);
#if SUMM_K_CONSISTENT
	void print_summary_nodes ();
#endif
	set<pt_node_index> print_subgraph (FILE * file, set<pt_node_index> & pt_nodes);
	void print_graph (FILE * file);

private:

	void get_int_ext_bndry_nodes (set<pt_node_index> & inside_nodes, set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, set<pt_node_index> & int_bndry, set<pt_node_index> & ext_bndry, set<pt_node_index> & valid_nodes);
};

#endif

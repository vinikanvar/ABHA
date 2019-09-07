
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef PT_FI_NODE
#define PT_FI_NODE

#include "../misc/debug.hh"
#include "../misc/parser.hh"

typedef unsigned int pt_node_index;
typedef unsigned int label;
//typedef HOST_WIDE_INT label;

class pt_fi_node
{
	pt_node_index 				node_id;
	map<label, set<pt_node_index> > 	in_edge_list;
	map<label, set<pt_node_index> > 	out_edge_list;

#if SUMM_K_CONSISTENT
	bool					is_summary_node;
#endif

public:

	static unsigned int number_of_nodes;

	pt_fi_node ();
	pt_fi_node (map<pt_node_index, pt_fi_node *> & nodes);
	~pt_fi_node ();

	pt_node_index get_node_id ();
	map<label, set<pt_node_index> > get_in_edge_list ();
	map<label, set<pt_node_index> > get_out_edge_list ();
	set<pt_node_index> get_in_nodes (label l);
	set<pt_node_index> get_out_nodes (label l);

#if SUMM_K_CONSISTENT
	bool get_is_summary_node ();
	void set_is_summary_node ();
	void get_all_names (pt_node_index stack_id, set<label> & names);
	void get_all_varinfos (pt_node_index stack_index, set<csvarinfo_t> & ps);
#endif

	static bool is_node_valid_at_point (pt_node_index nid, set<pt_node_index> & valid_nodes);
	static void get_nodes_valid_at_point (set<pt_node_index> & pt_nodes, set<pt_node_index> & valid_nodes);
	label get_node_name (pt_node_index stack_id);
	void get_out_adj_nodes (set<pt_node_index> & out_adj_nodes, set<pt_node_index> & valid_nodes);
	void get_out_adj_nodes (set<pt_node_index> & lptr, set<pt_node_index> & rptr, map<pt_node_index, map<label, set<pt_node_index> > > & invis_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & invis_out_edges, set<pt_node_index> & out_adj_nodes, set<pt_node_index> & valid_nodes);
	void get_in_adj_nodes (set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & invis_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & invis_out_edges, set<pt_node_index> & in_adj_nodes, set<pt_node_index> & valid_nodes);
	bool get_destination_nodes (label l, pt_node_index stack_id, set<pt_node_index> & dest_nodes);
#if SUMM_TYPE_CLOSURE == 0
	bool get_destination_nodes (label l, pt_node_index stack_id, set<pt_node_index> & dest_nodes, set<pt_node_index> & value_excl_out_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges);
#endif
	bool compute_offset (label l, pt_node_index stack_id, set<pt_node_index> & dest_nodes, label & computed_offset);
	void get_in_out_adj_nodes (set<pt_node_index> & lptr, set<pt_node_index> & must_lptr, label l, set<pt_node_index> & rpte, map<pt_node_index, map<label, set<pt_node_index> > > & invis_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & invis_out_edges, set<pt_node_index> & adjoining_nodes, set<pt_node_index> & valid_nodes);
	void mark_reachable_nodes (map<pt_node_index, pt_fi_node *> & nodes_map, set<pt_node_index> & lptr, set<pt_node_index> & rptr, map<pt_node_index, map<label, set<pt_node_index> > > & invis_in_edges, map<pt_node_index, map<label, set<pt_node_index> > > & invis_out_edges, set<pt_node_index> & reachable_nodes, set<pt_node_index> & valid_nodes);
	bool insert_edge (label l, pt_fi_node & dest, pt_node_index stack_id);

	int count_in_edges ();
	int count_out_edges ();
	void get_points_to_pairs (set<pt_node_index> & pt_nodes, map<label, set<label> > & points_to_pairs, map<label, set<label> > & summ_stack_to_stack_pointers, map<pt_node_index, pt_fi_node *> & nodes, pt_node_index stack_id);
	void get_node_varinfo (pt_node_index stack_index, csvarinfo_t & p);
	set<pt_node_index> print_node_pointers (FILE * file, set<pt_node_index> & pt_nodes, map<pt_node_index, pt_fi_node *> & nodes, pt_node_index stack_id);
	void get_node_fields (set<pt_node_index> & pt_nodes, map<pt_node_index, set <pair<label, pt_node_index> > > & field_edges);
	void print_node (FILE * file, map<pt_node_index, pt_fi_node *> & nodes, bool print_dump_file = true);
	void print_node_reverse (FILE * file);

};


#endif


/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef DETERMINISTIC_GRAPH
#define DETERMINISTIC_GRAPH

#include "../misc/debug.hh"
#include "../dfv/deterministic_node.hh"

typedef unsigned int variable_id;
typedef unsigned int node_index;

class deterministic_graph
{
public:
        // Count of the number of program points which reference to this data
        // flow value.
        unsigned int reference_count;

	map<label_sites, deterministic_node *>  nodes;

	// STACK should be declared after NODES so that any new
	// DETERMINISTIC_GRAPH has NODES before creating STACK.
	deterministic_node 			stack;

public:

	deterministic_graph ();
	~deterministic_graph ();

	void increment_reference_count ();
	void decrement_reference_count ();

	void clean ();
	void erase ();
	bool is_empty ();
	deterministic_node * get_destination_node (label l);
	deterministic_node * get_destination_node (deterministic_node & n, label l);
	set<deterministic_node *> get_destination_nodes (deterministic_node & n, label l);
	void insert_destination_nodes (deterministic_node & src_node, label offset, set<deterministic_node *> & dest_nodes);
	void get_reachable_nodes (label_sites & src, set<label_sites> & reachable_nodes);
	bool is_value_same (deterministic_graph & g);
	void copy_value (deterministic_graph &g, bool is_loop_merge);
	deterministic_graph * copy_value (bool is_loop_merge);
	deterministic_node * update_deterministic_edge (deterministic_node & src_node, label soutl, sites & soutss, set<pair<node_index, node_index> > & visited_pairs);
	deterministic_node * insert_edge (deterministic_node & src_node, label l, site s, bool latest_use_only = false);
	deterministic_node * insert_edge (deterministic_node & src_node, label l, sites & ss, bool is_latest_use_only = false);
	void copy_subgraph (deterministic_node & src_node, deterministic_node & dest_node, deterministic_graph & dest_graph);
	void copy_subgraph (deterministic_node & src_node, deterministic_node & dest_node, deterministic_graph & dest_graph, set<pair<label_sites, label_sites> > & visited_pairs);
	void copy_subgraph (deterministic_node & src_node, deterministic_node & dest_node);
	void copy_subgraph (deterministic_node & src_node, deterministic_node & dest_node, label dest_offset, deterministic_graph & dest_graph);
	void copy_subgraph (deterministic_node & src_node, deterministic_node & dest_node, label dest_offset);
	void extract_subgraph (variable_id v, deterministic_graph & dest_graph);
	void extract_subgraph (set<variable_id> vids, deterministic_graph & dest_graph);

	void temp_delete_edge (deterministic_node & src, label l, deterministic_node & dest);
	void delete_edge (deterministic_node & src_node, label l, bool is_clean = true);
	void delete_out_edges (deterministic_node & node);
	set<label> get_dead_variables (set<unsigned int> local_variables);

	void get_valid_live_nodes (map<label, set<deterministic_node *> > & sync_pts_live_nodes, set<label_sites> & valid_live_nodes);
	void get_k_access_paths (set<list<label> > & aps, unsigned int & tot_aps, bool is_accum_aps, struct cgraph_node * cnode);
	void get_k_access_paths (set<list<label> > & aps, unsigned int & tot_aps, bool is_accum_aps, struct cgraph_node * cnode, map<label, set<deterministic_node *> > & sync_pts_live_nodes);
	void get_k_access_paths (set<list<label> > & aps, unsigned int & tot_aps, bool is_accum_aps, struct cgraph_node * cnode, set<label_sites> & valid_live_nodes, bool consider_validity);
	void get_k_access_paths (label_sites & lss, map<label_sites, set<list<label> > > & sent_lss_aps, map<label_sites, set<list<label> > > & new_lss_aps, unsigned int & tot_aps, bool is_accum_aps, struct cgraph_node * cnode, set<label_sites> & valid_live_nodes, bool consider_validity);
	static bool append_k_access_paths (set<list<label> > & src_aps, label field, label_sites & dest_lss, map<label_sites, set<list<label> > > & new_lss_aps);
	static void append_ap_field (list<label> & ap, label field);
	static void collect_access_paths (map<label_sites, set<list<label> > > & lss_aps, set<list<label> > & all_aps);
	static void get_access_paths_stats (map<label_sites, set<list<label> > > & lss_aps, unsigned int & aps_count);

	void get_graph_stats (unsigned int & node_count, unsigned int & edge_count, unsigned int & use_sites_count, set<site> & unique_use_sites);
	static void print_access_paths (map<label_sites, set<list<label> > > & lss_aps);
	static void print_access_paths (set<list<label> > & aps);
	static void print_access_path (list<label> & ap);

	bool is_graph_reachability_okay ();
	bool is_graph_labelling_okay ();

	void print_value (const char * file);
};

#endif

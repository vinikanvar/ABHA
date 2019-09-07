
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef NON_DETERMINISTIC_GRAPH
#define NON_DETERMINISTIC_GRAPH

#include "../misc/debug.hh"
#include "../dfv/non_deterministic_node.hh"
#include "../dfv/deterministic_graph.hh"

typedef unsigned int variable_id;
typedef unsigned int node_index;

class non_deterministic_graph
{
public:
        // Count of the number of program points which reference to this data
        // flow value.
        unsigned int reference_count;

	map<label_site_pair, non_deterministic_node *>  nodes;

	// STACK should be declared after NODES so that any new
	// NON_DETERMINISTIC_GRAPH has NODES before creating STACK.
	non_deterministic_node 			stack;

public:

	non_deterministic_graph ();
	~non_deterministic_graph ();

	void increment_reference_count ();
	void decrement_reference_count ();

	void clean ();
	void erase ();
	bool is_empty ();
	non_deterministic_node * get_destination_node (label l);
	set<non_deterministic_node *> get_destination_nodes (non_deterministic_node & n, label l);
	void insert_destination_nodes (non_deterministic_node & src_node, label offset, set<non_deterministic_node *> & dest_nodes);
	non_deterministic_node * get_node (label l, site_pair sp);
	void get_reachable_nodes (label_site_pair & src, set<label_site_pair> & reachable_nodes);
	bool is_value_same (non_deterministic_graph & g);
	void copy_value (non_deterministic_graph &g, bool is_loop_merge);
	non_deterministic_graph * copy_value (bool is_loop_merge);
	non_deterministic_node * insert_edge (non_deterministic_node & src_node, label l, site_pair sp);
	non_deterministic_node * insert_edge (non_deterministic_node & src_node, label l, site s, bool is_alloc_site = false);
	void copy_subgraph (non_deterministic_node & src_node, non_deterministic_node & dest_node, non_deterministic_graph & dest_graph);
	void copy_subgraph (non_deterministic_node & src_node, non_deterministic_node & dest_node, non_deterministic_graph & dest_graph, set<pair<label_site_pair, label_site_pair> > & visited_pairs);
	void copy_subgraph (non_deterministic_node & src_node, non_deterministic_node & dest_node);
	void copy_subgraph (non_deterministic_node & src_node, non_deterministic_node & dest_node, label dest_offset, non_deterministic_graph & dest_graph);
	void copy_subgraph (non_deterministic_node & src_node, non_deterministic_node & dest_node, label dest_offset);
	void copy_subgraph (variable_id v, non_deterministic_node & src_v_node, non_deterministic_graph & dest_graph);
	void copy_subgraph (non_deterministic_node & src_node, deterministic_node & dest_node, deterministic_graph & dest_graph, set<pair<node_index, node_index> > & visited_pairs);
	void extract_subgraph (set<variable_id> vids, non_deterministic_graph & dest_graph);

	void temp_delete_edge (non_deterministic_node & src, label l, non_deterministic_node & dest);
	void delete_edge (non_deterministic_node & src_node, label l, bool is_clean = true);
	void delete_out_edges (non_deterministic_node & node);
	set<label> get_dead_variables (set<unsigned int> local_variables);

	void get_valid_live_nodes (map<label, set<non_deterministic_node *> > & sync_pts_live_nodes, set<label_site_pair> & valid_live_nodes);
	void get_k_access_paths (set<list<label> > & aps, unsigned int & tot_aps, bool is_accum_aps, struct cgraph_node * cnode);
	void get_k_access_paths (set<list<label> > & aps, unsigned int & tot_aps, bool is_accum_aps, struct cgraph_node * cnode, map<label, set<non_deterministic_node *> > & sync_pts_live_nodes);
        void get_k_access_paths (set<list<label> > & aps, unsigned int & tot_aps, bool is_accum_aps, struct cgraph_node * cnode, set<label_site_pair> & valid_live_nodes, bool consider_validity);
        void get_k_access_paths (set<list<label> > & aps, struct cgraph_node * cnode, set<label_site_pair> & valid_live_nodes, bool consider_validity);
        void get_k_access_paths (label_site_pair & lsp, map<label_site_pair, set<list<label> > > & sent_lsp_aps, map<label_site_pair, set<list<label> > > & new_lsp_aps, struct cgraph_node * cnode, set<label_site_pair> & valid_live_nodes, bool consider_validity);
        static bool append_k_access_paths (set<list<label> > & src_aps, label field,  label_site_pair & dest_lsp, map<label_site_pair, set<list<label> > > & sent_lsp_aps, map<label_site_pair, set<list<label> > > & new_lsp_aps);
        static void append_ap_field (list<label> & ap, label field);
        static void collect_access_paths (map<label_site_pair, set<list<label> > > & lsp_aps, set<list<label> > & all_aps);
        static void get_access_paths_stats (map<label_site_pair, set<list<label> > > & lsp_aps, unsigned int & aps_count);

        static void print_access_paths (map<label_site_pair, set<list<label> > > & lsp_aps);
        static void print_access_paths (set<list<label> > & aps);
        static void print_access_path (list<label> & ap);

	void get_graph_stats (unsigned int & node_count, unsigned int & edge_count, unsigned int & use_sites_count, set<site> & unique_use_sites);
	bool is_graph_reachability_okay ();
	bool is_graph_labelling_okay ();

	void print_value (const char * file);
};

#endif

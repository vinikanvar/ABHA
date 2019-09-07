
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef DETERMINISTIC_NODE
#define DETERMINISTIC_NODE

#include "../misc/debug.hh"
#include "../misc/parser.hh"

// Root variables sites are set as negative of their id. 
// Field sites are set as their use sites.
typedef int site;
typedef set<site> sites;

// LABEL represents OFFSET.* and not OFFSET.

typedef unsigned int label;
typedef unsigned int node_index;
typedef pair<label, sites> label_sites;

#define ROOT_LINK 		-1
#define DISCONNECTED_LINK 	-2

class deterministic_node
{
	node_index				node_id;

	sites					desc_sites;

	// No need of type. We needed type when access paths were globalized
	// and same site was accessed from different functions/context. Here we
	// do not globalize and each context data flow value is separate.

	label					in_edge_label;

	// Save the sequence of fields that this in_edge_label represents.
	// Do not save each field in sequence on each edge because e.g. y=x->f
	// needs x.*.f.* sequence, all fields with same site.

	// Node should be uniquely identified by pair<label,sites> rather than
	// just sites. Example, (1)z=&(y->f);(2)use z->g; produces z.*.g.* with
	// use-site 2 and in-edge-label g.* but y.*.f.g.* with use-site 2 and
	// different in-edge label f.g.*. Without pair<label,sites>, node with
	// same use-site 2 will get pointed by different in-edge-labels.

	// list<label>				offset_sequence;
	map<label, label_sites>			out_edge_list;

	set<label_sites>			in_nodes;
	
public:
	static unsigned int number_of_nodes;

	deterministic_node (map<label_sites, deterministic_node *> & nodes);
	deterministic_node (sites & ss, label l, map<label_sites, deterministic_node *> & nodes);
	
	~deterministic_node ();

	node_index get_node_id ();
	sites get_desc_sites ();
	set<label_sites> get_in_nodes ();
	void replace_in_nodes (label_sites & old_ls, label_sites & new_ls);
	label get_in_edge_label ();
	label_sites get_label_sites ();
	map<label, label_sites> get_out_edge_list ();
	map<label, label_sites> * get_out_edge_list_pointer ();
	void get_out_nodes (set<label_sites> & out_nodes);
	void get_out_edge_labels (set<label> & out_edge_labels);
	label_sites get_destination_node (label l);
	bool is_in_nodes ();
	bool is_in_node (label_sites & lss);
	bool is_desc_site (site s);
	bool is_out_edge ();
	bool is_out_edge (label l, sites & ss);
	bool is_stack_node ();
	bool is_node_same (deterministic_node & g_n);
	void insert_desc_site (site s);
	deterministic_node * new_copy_node (map<label_sites, deterministic_node *> & dest_graph_nodes);
	void insert_edge (label l, deterministic_node & dest);
	void temp_delete_edge (label l, deterministic_node & dest);

	void get_node_stats (unsigned int & edge_count, unsigned int & use_sites_count, set<site> & unique_use_sites);
	bool is_node_okay (deterministic_node & stack);
	bool is_out_node_okay (label out_edge_label, deterministic_node & out_n);
	bool is_in_node_okay (deterministic_node & in_n);
	static void print_sites (sites &s);
	void print_in_edge_list (map<label_sites, deterministic_node *> & nodes);
	void print_out_edge_list (map<label_sites, deterministic_node *> & node);
	void print_node (map<label_sites, deterministic_node *> & nodes);
};

#endif

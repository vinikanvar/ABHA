
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef NON_DETERMINISTIC_NODE
#define NON_DETERMINISTIC_NODE

#include "../misc/debug.hh"
#include "../misc/parser.hh"

// Root variables sites are set as negative of their id. 
// Field sites are set as their <alloc site, use site>
typedef int site;
typedef pair<site, site> site_pair;

// LABEL represents OFFSET.* and not OFFSET.

typedef unsigned int label;
typedef unsigned int node_index;
typedef pair<label, site_pair> label_site_pair;

#define ROOT_LINK 		-1
#define DISCONNECTED_LINK 	-2

class non_deterministic_node
{
	node_index				node_id;

	// We assume that both alloc-site and desc-site are not non-zero in a
	// node. Therefore, we use the zero site to mark DISCONNECTED_LINK.
	site_pair				alloc_desc_site_pair;

	// No need of type. We needed type when access paths were globalized
	// and same site was accessed from different functions/context. Here we
	// do not globalize and each context data flow value is separate.

	label					in_edge_label;

	// Save the sequence of fields that this in_edge_label represents.
	// Do not save each field in sequence on each edge because e.g. y=x->f
	// needs x.*.f.* sequence, all fields with same site.

	// Node should be uniquely identified by pair<label,site_pair> rather than
	// just site_pair. Example, (1)z=&(y->f);(2)use z->g; produces z.*.g.* with
	// use-site 2 and in-edge-label g.* but y.*.f.g.* with use-site 2 and
	// different in-edge label f.g.*. Without pair<label,site_pair>, node with
	// same use-site 2 will get pointed by different in-edge-labels.

	// list<label>				offset_sequence;
	// Non-deterministic graph
	map<label, set<label_site_pair> >	out_edge_list;

	set<label_site_pair>			in_nodes;
	
public:
	static unsigned int number_of_nodes;

	non_deterministic_node (map<label_site_pair, non_deterministic_node *> & nodes);
	non_deterministic_node (site_pair & sp, label l, map<label_site_pair, non_deterministic_node *> & nodes);
	
	~non_deterministic_node ();

	node_index get_node_id ();
	site_pair get_alloc_desc_site_pair ();
	set<label_site_pair> get_in_nodes ();
	void replace_in_nodes (label_site_pair & old_lsp, label_site_pair & new_lsp);
	label get_in_edge_label ();
	label_site_pair get_label_site_pair ();
	map<label, set<label_site_pair> > get_out_edge_list ();
	map<label, set<label_site_pair> > * get_out_edge_list_pointer ();
	void get_out_nodes (set<label_site_pair> & out_nodes);
	void get_out_edge_labels (set<label> & out_edge_labels);
	set<label_site_pair> get_destination_nodes (label l);
	bool is_node_okay (non_deterministic_node & stack);
	bool is_in_node_okay (non_deterministic_node & in_n);
	bool is_out_node_okay (label out_edge_label, non_deterministic_node & out_n);
	bool is_in_nodes ();
	bool is_in_node (label_site_pair lsp);
	bool is_alloc_site (site s);
	bool is_desc_site (site s);
	bool is_out_edge ();
	bool is_out_edge (label l, site_pair & sp);
	bool is_stack_node ();
	bool is_node_same (non_deterministic_node & g_n);
	void set_alloc_site (site s);
	void set_desc_site (site s);
	non_deterministic_node * new_copy_node (map<label_site_pair, non_deterministic_node *> & dest_graph_nodes);
	void insert_edge (label l, non_deterministic_node & dest);
	void temp_delete_edge (label l, non_deterministic_node & dest);

	void get_node_stats (unsigned int & edge_count, unsigned int & use_sites_count, set<site> & unique_use_sites);
	static void print_site_pair (site_pair &s);
	void print_in_edge_list (map<label_site_pair, non_deterministic_node *> & nodes);
	void print_out_edge_list (map<label_site_pair, non_deterministic_node *> & node);
	void print_node (map<label_site_pair, non_deterministic_node *> & nodes);
};

#endif

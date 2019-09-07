
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef AP_FI_NODE
#define AP_FI_NODE

#include "../misc/debug.hh"
#include "../misc/parser.hh"

typedef unsigned int ap_node_index;
typedef int def_stmt;
typedef set<def_stmt> def_stmt_set;
typedef unsigned int label;
//typedef HOST_WIDE_INT label;
typedef unsigned int type;
#define DONT_CARE -1

class ap_fi_node
{
	ap_node_index 					node_id;

	// Out-edge information:
	// (a) out_edge_list: acyclic edges
	// (b) out_cyclic_edge_list: cyclic edges

#if SUMM_STMT_CLOSURE
	map<label, pair<def_stmt_set, ap_node_index> > 	out_edge_list;
#elif SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
	// SUMM_TYPE_K saves static_name of each pointee on edge.
	// SUMM_TYPE_CLOSURE saves closure of static_names of pointees in
	// destination node.
	map<pair<label, type>, ap_node_index> 		out_edge_list;
#else
	map<label, ap_node_index> 			out_edge_list;
#endif

#if gAP_CYCLIC && SUMM_TYPE_K
	map<pair<label, type>, ap_node_index> 		out_cyclic_edge_list;
#endif

	// In-edge information: 
	// (a) in-node: via acyclic edge
	// (b) in-nodes: via cyclic edges 
	// (c) in-edge-label 
	// (d) in-edge-type or static name of THIS node

	// Every node has exactly one acyclic in-edge.
	ap_node_index					in_node_id;
#if gAP_CYCLIC && SUMM_TYPE_K
	set<ap_node_index>				in_cyclic_node_ids;
	set<ap_node_index>				out_cyclic_node_ids;
#endif
	// In both gAP_CYCLIC and acyclic gAP of SUMM_TYPE_K, all in-nodes have
	// same <in_edge_label,static_name>. Therefore, we do not need a set<>
	// for these.
	label 						in_edge_label;
#if SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
	type						static_name;
#endif

#if SUMM_TYPE_CLOSURE
	// Set of heap types + stack names that the access path represents.
	// This information is required to find if an out-edge of a gAP node is
	// repeating.
	// Note that this should not be a set of gPT nodes because even the
	// newly added heap types of each gAP node are required in compute_ap()
	// while computing APs of other affected gPT nodes; however, new gPT
	// node (i.e. clone) is not available in compute_ap().  However, the
	// heap type of new gPT node is available from the old gPT node
	// (because types of clones remain same). 
	set<label>			 		static_names;
#endif

#if SUMM_K_FILTER || SUMM_K_PREFIX
	unsigned int					ap_len;
#endif

public:

	static unsigned int number_of_nodes;

	ap_fi_node ();
	ap_fi_node (map<ap_node_index, ap_fi_node *> & nodes);
	~ap_fi_node ();

	unsigned int get_node_id ();
	label get_in_edge_label ();
	ap_node_index get_in_node_id ();
#if gAP_CYCLIC && SUMM_TYPE_K
	set<ap_node_index> get_in_cyclic_node_ids ();
	map<pair<label, type>, ap_node_index> get_out_cyclic_edge_list ();
	void add_out_cyclic_node_ids (map<ap_node_index, set<ap_node_index> > & out_cyclic_edges);
#endif

#if SUMM_STMT_CLOSURE
	map<label, pair<def_stmt_set, ap_node_index> > get_out_edge_list ();
	void insert_edge (label l, def_stmt s, ap_fi_node & dest_node);
	def_stmt_set get_def_stmt_set (label l);
	ap_node_index get_destination_node (label l, def_stmt s);
	set<ap_node_index> get_destination_node (label l);
#elif SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
	set<ap_node_index> get_destination_nodes (label l);
	ap_node_index get_destination_node (label l, type t);
	map<pair<label, type>, ap_node_index> get_out_edge_list ();
	#if gAP_CYCLIC && !SUMM_POINTED_TO_BY && !SUMM_K_FILTER && !SUMM_K_PREFIX
	void insert_edge (label l, type t, ap_fi_node & dest_node, bool is_cyclic);
	#else
	void insert_edge (label l, type t, ap_fi_node & dest_node);
	#endif
#else
	ap_node_index get_destination_node (label l);
	map<label, ap_node_index> get_out_edge_list ();
	void insert_edge (label l, ap_fi_node & dest_node);
#endif

#if SUMM_K_CONSISTENT
	void get_reachable_nodes (set<ap_node_index> & reachable_nodes);
#elif SUMM_K_FILTER || SUMM_K_PREFIX
	unsigned int get_ap_len ();
	type get_static_name ();
#elif SUMM_TYPE_CLOSURE
	set<label> get_static_names ();
	void add_static_name (label static_name);
#elif SUMM_TYPE_K || SUMM_POINTED_TO_BY
	type get_static_name ();
#endif

#if SUMM_TYPE_K && gAP_CYCLIC
	void print_cyclic_edges ();
#endif
	void print_node (FILE * file);
};


#endif

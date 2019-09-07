/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef ACCESS_NAME
#define ACCESS_NAME

#include "../misc/debug.hh"
#include "../dfv/ap_fi_graph.hh"

typedef unsigned int ap_node_index;
typedef unsigned int label;

// We need node_name_type on stack to deal with following problem:
// Problem with SUMM_K_PREFIX=1 is that access name of node representing
// variable x and pointed by y, contains access paths {x,y} rather than
// {x,y.0}. Also the node representing variable y and pointed by x, also
// contains access paths {x,y} rather than {x.0,y}. Therefore,
// access_name_to_pt map is wrong. FIX: add variable name also in access name
// so that they are different for node representing x and node representing y.

// We need NODE_NAME_TYPE on heap for the following reason:
// It is required to distinguish heap locations of different types): Each heap
// type is uniquely mapped to a heap variable id of gcc.

// Access of a points-to node is defined by the following:
// (a) access paths 
// (b) node_name_type 
// (c) unbounded access paths (this is required if ap_nodes stores only acyclic
//     access paths).

class access_name
{
	label					node_name_type;
	set<ap_node_index> 			ap_nodes;

	// SUMM_K_PREFIX does not need this as an AP of K length itself
	// indicates that ap_unbounded=true.
	// This is set when AP_NODES stores only acyclic access paths,
	// i.e. it is not set if OUT_CYCLIC_EDGE_LIST is saved.
	bool 					ap_unbounded;

#if gAP_CYCLIC && SUMM_TYPE_K 
	// TODO: For most precise results, store 
	// set<pair<ap_node_index, g_ap_edges>> ap_nodes;
	// This will ensure that access name {<p1,{c1}>,<p1,{c2}>} is different
	// from {<p1,{c1,c2}>}. 
	// For simple implementation, we store 
	// set<ap_node_index> ap_nodes and g_ap_edges cyclic_edges.
	// This will not differentiate between access names:
	// {<p1,{c1}>,<p2,{c2}>} and {<p1,{c1,c2}>,<p2,{c2}>}, OR
	// {<p1,{}>,<p1,{c1}>} and {<p1,{c1}>}.
	// In order to differentiate the latter, we can set K=2 with
	// gAP_CYCLIC; then p1 cyclic and p1 acyclic are represented by two gAP
	// nodes.

	// In access_name, we do not need <l,t>. In ap_fi_node, we need <l,t>
	// in cyclic edges for quick access.
	g_ap_cyclic_edges				cyclic_edges;
#endif

#if SUMM_POINTED_TO_BY
	// All locations have the pointed-to-by-x predicate. A heap location
	// not pointed directly by a variable, has no predicate. In order to
	// distinguish such a heap location from a fresh heap location, we set
	// this bool to true.
	bool					is_var_reachable;
#endif

public:
	access_name ();
	~access_name ();
	access_name (set<ap_node_index> & new_ap_nodes, bool new_ap_unbounded, bool is_var_reachable);
	access_name (ap_node_index new_ap_nodes, bool new_ap_unbounded, bool is_var_reachable);
	set<ap_node_index> get_ap_nodes ();
	bool get_ap_unbounded ();
	label get_node_name_type ();
	void get_ap_nodes (ap_fi_graph & g_ap, label l,	set<ap_node_index> & ap_nids);
#if OVER_APPROX_CYCLIC_EDGES
	void over_approx_cyclic_edges (ap_fi_graph & g_ap);
#endif
	bool is_ap_unbounded ();
	bool is_ap_nodes_empty ();
	bool is_same (access_name & an);
	bool is_subset (access_name & an);
	friend bool operator< (const access_name & an1, const access_name & an2);
	void add_ap_nodes (set<ap_node_index> & new_ap_nodes);
	void add_ap_nodes (ap_node_index new_ap_nodes);
	void add_ap_unbounded (bool new_ap_unbounded);
	void add_node_name_type (label new_node_name_type);
	void add_access_name (access_name & an);
	void set_ap_nodes (set<ap_node_index> & new_ap_nodes);

#if gAP_CYCLIC && SUMM_TYPE_K 
	g_ap_cyclic_edges get_cyclic_edges ();
	void add_cyclic_edges (g_ap_cyclic_edges & new_cyclic_edges);
	void add_cyclic_edges (access_name & dest_access_name);
	void print_cyclic_edges ();
#endif
#if SUMM_POINTED_TO_BY
	bool get_is_var_reachable ();
	void add_is_var_reachable (bool new_is_var_reachable);
	void set_is_var_reachable (bool new_is_var_reachable);
#endif

	void print_ap_nodes (ap_fi_graph * g_ap);
	void print (ap_fi_graph * g_ap);
};

#endif


/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef AP_FI_GRAPH
#define AP_FI_GRAPH

#include "../misc/debug.hh"
#include "../dfv/ap_fi_node.hh"

typedef unsigned int ap_node_index;

#if gAP_CYCLIC && SUMM_TYPE_K
typedef map<ap_node_index, map<pair<label, type>, ap_node_index> > g_ap_edges;
// In access_name, we do not need <l,t>. In ap_fi_node, we need <l,t> in cyclic
// edges for quick access.
typedef map<ap_node_index, set<ap_node_index> > g_ap_cyclic_edges;
#endif

class ap_fi_graph
{
public:

	map<ap_node_index, ap_fi_node *> 	nodes;
	ap_fi_node 				stack;

public:

	ap_fi_graph ();
	~ap_fi_graph ();

	bool is_variable_node (ap_node_index nid);
	bool is_heap_node (ap_node_index nid);

#if SUMM_STMT_CLOSURE
	void update (ap_node_index ap_nid, label l, def_stmt_set ds, ap_node_index & dest_ap_node, bool & dest_ap_unbounded);
	ap_node_index update_edge (ap_fi_node & p, label l, def_stmt s);
	ap_node_index insert_edge (ap_fi_node & p, label l, def_stmt s);
#elif SUMM_TYPE_K
	#if gAP_CYCLIC
	void update (ap_node_index ap_nid, label l, type t, ap_node_index & dest_ap_node, bool & dest_ap_unbounded, g_ap_cyclic_edges & dest_cyclic_edges);
	pair<ap_node_index, bool> update_edge (ap_fi_node & p, label l, type t);
	#else
	void update (ap_node_index ap_nid, label l, type t, ap_node_index & dest_ap_node, bool & dest_ap_unbounded);
	ap_node_index update_edge (ap_fi_node & p, label l, type t);
	#endif
	ap_node_index insert_edge (ap_fi_node & p, label l, type t);
#elif SUMM_POINTED_TO_BY 
	void update (ap_node_index ap_nid, label l, type t, ap_node_index & dest_ap_node);
	ap_node_index update_edge (ap_fi_node & p, label l, type t);
	ap_node_index insert_edge (ap_fi_node & p, label l, type t);
#elif SUMM_K_FILTER || SUMM_K_PREFIX 
	void update (ap_node_index ap_nid, label l, type t, ap_node_index & dest_ap_node, bool & dest_ap_unbounded);
	ap_node_index update_edge (ap_fi_node & p, label l, type t);
	ap_node_index insert_edge (ap_fi_node & p, label l, type t);
#else
	void update (ap_node_index ap_nid, label l, type t, ap_node_index & dest_ap_node, bool & dest_ap_unbounded);
	ap_node_index update_edge (ap_fi_node & p, label l);
	ap_node_index insert_edge (ap_fi_node & p, label l);
#endif

#if SUMM_STMT_CLOSURE
	bool is_stmt_repeating (ap_fi_node & p, label l, def_stmt s);
#elif SUMM_TYPE_CLOSURE
	bool is_type_repeating (ap_fi_node & p, label l);
	bool is_type_repeating (ap_fi_node & p, set<label> & src_static_names, label l);
#elif SUMM_TYPE_K
	bool is_type_repeating (ap_fi_node & p, label l, type t, unsigned int num_repeating_edges=0);
	#if gAP_CYCLIC 
	bool is_in_field_label_same (ap_fi_node & p, label l_asterisk, type t_asterisk, label l_field, type t_field);
	bool is_in_label_same (ap_fi_node & p, label l, type t);
	ap_node_index get_type_repeating_node (ap_fi_node & p, label l_asterisk, type t_asterisk, label l_field, type t_field, unsigned int num_repeating_edges=0);
	#endif
#elif SUMM_K_FILTER || SUMM_K_PREFIX
	bool is_ap_long (ap_fi_node & p, label l);
#elif SUMM_K_CONSISTENT
	bool is_ap_summarized (ap_fi_node & p);	
#elif SUMM_POINTED_TO_BY
	bool is_var_path (ap_fi_node & p);
#endif

#if SUMM_K_CONSISTENT
	void remove_wild_card_subsumed_aps (set<ap_node_index> & ap_nids);
	void get_reachable_nodes (ap_node_index apid, set<ap_node_index> & reachable_nodes);
#endif
#if SUMM_STMT_CLOSURE
	def_stmt_set get_in_def_stmt_set (ap_fi_node & n);
	void get_access_paths (ap_node_index apnid, list<pair<label, def_stmt_set> > & ap);
#endif
	void get_access_paths (set<ap_node_index> & ap_nids, set<list<label> > & aps);
	void get_access_paths (ap_node_index apnid, list<label> & ap);
	void get_ap_nodes (list<label> & path, set<ap_node_index> & ap_nodes);
	static void append_ap_field (list<label> & ap, label field);
	void print_statistics ();
	static void print_access_path (list<label> & ap);
	void print_access_path (list<pair<label, def_stmt_set> > & ap);
	void print_subgraph (set<ap_node_index> & ap_nodes);
	void print_graph (FILE * file);
#if SUMM_TYPE_K && gAP_CYCLIC
	static void print_cyclic_edges (g_ap_edges & ce);
#endif
};

#endif

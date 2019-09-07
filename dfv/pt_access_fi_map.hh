/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef PT_ACCESS_FI_MAP
#define PT_ACCESS_FI_MAP

#include "../misc/debug.hh"
#include "../dfv/pt_fi_graph.hh"
#include "../dfv/ap_fi_graph.hh"
#include "../dfv/access_name.hh"

// Disable to split the access_name key into multiple maps
#define SINGLE_REVERSE_MAP 1

typedef unsigned int pt_node_index;
typedef unsigned int ap_node_index;
typedef unsigned int label;
typedef unsigned int max_depth;

class pt_access_fi_map
{
public:

	map<pt_node_index, access_name> 		pt_to_access_name;

#if SINGLE_REVERSE_MAP
	map<access_name, pt_node_index> 		access_name_to_pt;
#else
	map<set<ap_node_index>, set<pt_node_index> > 	ap_nodes_to_pts;
	// AP_UNBOUNDED is required is AP_NODES stores only acyclic access paths
	map<bool, set<pt_node_index> > 			ap_unbounded_to_pts;
	map<label, set<pt_node_index> > 		type_to_pts;
#endif

#if SUMM_K_CONSISTENT
	map<pt_node_index, max_depth>			pt_to_max_depth;
#endif

public:

	pt_access_fi_map ();
	pt_access_fi_map (pt_fi_graph & g_pt, ap_fi_graph & g_ap);
	~pt_access_fi_map ();

	pt_node_index find_clone (access_name & an);
	void find_affected_region (set<pt_node_index> & nreach, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name, map<pt_node_index, bool> & affected_nodes);

#if SUMM_K_CONSISTENT
	max_depth get_max_depth (pt_node_index pnid);
	max_depth get_max_depth (pt_node_index pnid, set<pt_node_index> & ext_bndry, map<pt_node_index, max_depth> & new_pt_to_max_depth);
	void set_max_depth (pt_node_index pt_nid, max_depth md, map<pt_node_index, max_depth> & new_pt_to_max_depth);
	void set_max_depth (pt_node_index pt_nid, max_depth md);
	void set_max_depth (map<pt_node_index, bool> & affected_nodes, map<pt_node_index, max_depth> & new_pt_to_max_depth);
	void update_max_depth (pt_node_index src_nid, label l, pt_node_index dest_nid, set<pt_node_index> & ext_bndry, map<pt_node_index, max_depth> & new_pt_to_max_depth);
	void print_max_depth_map (map<pt_node_index, max_depth> & new_pt_to_max_depth);
	void print_summ_cmpts (set<set<pt_node_index> > & summ_cmpts);
	void print_summ_cmpts_map (map<pt_node_index, pt_node_index> & summ_cmpts_map);
	void compute_summ_cmpts_map (set<set<pt_node_index> > & summ_cmpts, map<pt_node_index, pt_node_index> & summ_cmpts_map);
	void update_summ_cmpts (pt_node_index src_nid, label l, pt_node_index dest_nid, set<pt_node_index> & ext_bndry, map<pt_node_index, max_depth> & new_pt_to_max_depth, set<set<pt_node_index> > & summ_cmpts);
	set<pt_node_index> get_summ_cmpt (pt_node_index pt_nid, set<set<pt_node_index> > & summ_cmpts);
	void merge_summ_cmpts (pt_node_index src_nid, pt_node_index dest_nid, set<set<pt_node_index> > & summ_cmpts);
	void create_new_summ_cmpt (pt_node_index dest_nid, set<set<pt_node_index> > & summ_cmpts);
#endif

	access_name * get_access_name (pt_node_index pnid, set<pt_node_index> & ext_bndry, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
	access_name * get_access_name (pt_node_index pnid);
	label get_node_name_type (pt_node_index pnid);
	set<ap_node_index> get_ap_nodes (pt_node_index pnid);
	bool get_ap_unbounded (pt_node_index pnid);
	
	void set_access_name (pt_node_index pt_nid, access_name & new_access_name);
	void set_access_name (map<pt_node_index, bool> & affected_nodes, map<pt_node_index, access_name> & new_pt_to_access_name);
	void set_access_name_to_pt (access_name & new_access_name, pt_node_index pt_nid);

#if SUMM_STMT_CLOSURE
	def_stmt_set get_def_stmt_set (pt_node_index p_nid, label l, set<pt_node_index> & ext_bndry, ap_fi_graph & g_ap, map<pt_node_index, access_name> & new_pt_to_access_name);
#endif
	void compute_ap (pt_node_index pt_nid, label l, type t, def_stmt_set ds, set<pt_node_index> & ext_bndry, ap_fi_graph & g_ap, access_name & dest_access_name, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);
	void compute_ap (pt_node_index pt_nid, label l, type t, set<pt_node_index> & ext_bndry, ap_fi_graph & g_ap, access_name & dest_access_name, map<pt_node_index, pt_node_index> & summ_cmpts_map, map<pt_node_index, access_name> & new_pt_to_access_name);

	bool is_pt_access_map_okay (ap_fi_graph & g_ap);
	pt_node_index find_pt_with_access_name (access_name & an, pt_node_index exclude_nid);

	void print_statistics (ap_fi_graph & g_ap);
	void get_statistics (ap_fi_graph & g_ap, unsigned int & max_ap_nodes_per_node, unsigned int & max_cyclic_edges_per_node, unsigned int & tot_access_names_with_cyclic_edges, unsigned int & tot_access_names_with_no_cyclic_edge, unsigned int & tot_ap, unsigned int & tot_ce, unsigned int & tot_ap_len, set<pt_node_index> & valid_nodes, bool all_valid = false);
	void print_pt_nodes (set<pt_node_index> & pts);
	void print_submap (set<pt_node_index> & pt_nodes, ap_fi_graph & g_ap);
	void print_submap (pt_node_index pnid, ap_fi_graph & g_ap);
	void print_map (map<pt_node_index, access_name> & new_pt_to_access_name);
	void print_map (FILE * file, ap_fi_graph * g_ap);
	void print_reverse_map ();
};

#endif


/************************
 * @author Vini Kanvar
************************/

#include "pt_access_fi_map.hh"
#include <algorithm>

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

pt_access_fi_map::
pt_access_fi_map ()
{
	RESULT ("\nError: pt_access_fi_map constructor should be called with g_pt and g_ap");
}

pt_access_fi_map::
pt_access_fi_map (pt_fi_graph & g_pt, ap_fi_graph & g_ap)
{
	pt_node_index pt_stack = g_pt.stack.get_node_id ();
	ap_node_index ap_stack = g_ap.stack.get_node_id ();

	access_name new_access_name (ap_stack, false, false);

#if DEBUG_CONTAINER
	DEBUG ("\nap_stack=%d", ap_stack);
	DEBUG ("\ninitialization of pt_access_fi_map=");
	new_access_name.print (NULL);
#endif

	set_access_name (pt_stack, new_access_name);
#if SUMM_K_CONSISTENT
	set_max_depth (pt_stack, 0);
#endif
}

pt_access_fi_map::
~pt_access_fi_map ()
{
}

/**
 * If there exists AP of PT_NID->L in gAP, fetch its IN_DS. This is required so
 * that all ap1,ap2,... on PT_NID are appended with the def_stmt of each of
 * ap1->l, ap2->l,.... since all of them have become link aliases now.
 */

#if SUMM_STMT_CLOSURE
def_stmt_set pt_access_fi_map::
get_def_stmt_set (pt_node_index pt_nid,
	label l,
	set<pt_node_index> & ext_bndry,
	ap_fi_graph & g_ap,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{	
	DEBUG ("\nget_def_stmt_set (pt_nid=%d,l=%d)", pt_nid, l);
	def_stmt_set ds;
	map<pt_node_index, pt_node_index> empty_map;

	access_name * an = get_access_name (pt_nid, ext_bndry, empty_map, new_pt_to_access_name);
	access_name addr_an;
	if (!an)
		an = &addr_an;
	set<ap_node_index> ap;
	ap = an->get_ap_nodes ();
	set<ap_node_index>::iterator api;
	for (api = ap.begin (); api != ap.end (); api++)
	{
		ap_node_index ap_nid = *api;
		DEBUG ("\nap-node=%d,l=%d,ds=", ap_nid, l);
		if (!ap_nid)
		{
			RESULT ("\nError: gap node=%d -- AP of gpt node=%d!", ap_nid, pt_nid);
			return ds;
		}
		ap_fi_node * apn = g_ap.nodes[ap_nid];
		if (!apn)
		{
			RESULT ("\nError: gap node=%d -- AP of gpt node=%d not found", ap_nid, pt_nid);
			return ds;
		}

		// FIXME: FindStmtIds() should use EGen (i.e. old ids and new
		// ids). This is because APN (from new_pt_to_access_name) may
		// not contain the old ids (because some APs could have been
		// killed in new_pt_to_access_name). Old ids are required when
		// lhs and rhs are rooted at same variable. For example,
		// x=x->f, graph at IN=(x,n1),(n1,f_i1,n2),(n2,f_i2,n3). Then
		// when we set (x,n2), new_pt_to_access_name of n2 will not
		// return i2, unless old APs (i.e. x.f) of n2 are also
		// considered.
		def_stmt_set temp_ds = apn->get_def_stmt_set (l);

		#if DEBUG_CONTAINER
		def_stmt_set::iterator si;
		for (si = temp_ds.begin (); si != temp_ds.end (); si++)
			DEBUG ("%d,", *si);
		#endif

		// ds.insert (temp_ds.begin (), temp_ds.end ());
		merge_set (temp_ds, ds);
	}

	// If label is variable name or field, then insert DONT_CARE
	// If label is stack_deref, then statement ids are found
	// either from get_def_stmt_set() or are present in
	// gAP_c or are in DS.
	// Note: Statement ids are added on l=0 (ASTERISK) edges only.
	if (l && !ds.size ())
		ds.insert (DONT_CARE);

	#if DEBUG_CONTAINER
	DEBUG ("\npt-node in_n=%d,in_l=%d,ds=");
	def_stmt_set::iterator si;
	for (si = ds.begin (); si != ds.end (); si++)
		DEBUG ("%d,", *si);
	#endif

	return ds;
}
#endif

pt_node_index pt_access_fi_map::
find_clone (access_name & an)
{
	FUNBEGIN ();

#if SINGLE_REVERSE_MAP
	pt_node_index matching_pt = 0;
	if (access_name_to_pt.find (an) != access_name_to_pt.end ())
	{
		matching_pt = access_name_to_pt[an];
		DEBUG ("\nFound matching_pt=%d", matching_pt);
		RETURN (matching_pt);
		// return matching_pt;
	}

#if DEBUG_CONTAINER
	pt_node_index find_pnid = find_pt_with_access_name (an, 0);
	if (find_pnid)
	{
		RESULT ("\nError: find_clone() not working, found=%d for access name=", find_pnid);
		an.print (NULL);
		print_map (NULL, NULL);
	}
#endif

	// This is not an error. A new node in g_ap needs to be created
	// if a clone is not found.
	DEBUG ("\nNot found");
	RETURN (0);
	// return 0;

#else

	// Find gPT nodes having ap_nodes of an
	set<ap_node_index> ap_nodes = an.get_ap_nodes ();
	if (ap_nodes_to_pts.find (ap_nodes) == ap_nodes_to_pts.end ())
		return 0;
	set<pt_node_index> pts_ap_nodes = ap_nodes_to_pts[ap_nodes];
	if (!pts_ap_nodes.size ())
	{
		RESULT ("\nError: Empty set of pts stored for ap_nodes");
		RETURN (0);
		// return 0;
	}

	// Find gPT nodes having ap_unbounded of an
	bool ap_unbounded = an.get_ap_unbounded ();
	if (ap_unbounded_to_pts.find (ap_unbounded) == ap_unbounded_to_pts.end ())
		RETURN (0);
		// return 0;
	set<pt_node_index> pts_ap_unbounded = ap_unbounded_to_pts[ap_unbounded];
	if (!pts_ap_unbounded.size ())
	{
		RESULT ("\nError: Empty set of pts stored for ap_unbounded=%d", 
			ap_unbounded);
		RETURN (0);
		// return 0;
	}
	
	// Find gPT nodes having node_name_type of an
	label t = an.get_node_name_type ();
	if (type_to_pts.find (t) == type_to_pts.end ())
		RETURN (0);
		// return 0;
	set<pt_node_index> pts_type = type_to_pts[t];
	if (!pts_type.size ())
	{
		RESULT ("\nError: Empty set of pts stored for type=%d", t);
		RETURN (0);
		// return 0;
	}

	set<pt_node_index> common_pts_temp, common_pts;

	set_intersection (pts_ap_nodes.begin (), pts_ap_nodes.end (),
		pts_type.begin (), pts_type.end (),
		inserter (common_pts_temp, common_pts_temp.end ()));

	set_intersection (common_pts_temp.begin (), common_pts_temp.end (),
		pts_ap_unbounded.begin (), pts_ap_unbounded.end (),
		inserter (common_pts, common_pts.end ()));

#if DEBUG_CONTAINER
	DEBUG ("\ncommon_pts_temp=");
	set<pt_node_index>::iterator pi;
	for (pi = common_pts_temp.begin (); pi != common_pts_temp.end (); pi++)
		DEBUG ("%d,", *pi);
	DEBUG ("\nNumber of matching gpt nodes=%d", common_pts.size ());
#endif

	// This is not an error. A new node in g_ap needs to be created
	// if a clone is not found.
	if (!common_pts.size ())
		RETURN (0);
		// return 0;

	if (common_pts.size () > 1)
	{
		RESULT ("\nError: More than one gPT nodes have same access name");
		RETURN (0);
		// return 0;
	}

	pt_node_index matching_pt = *(common_pts.begin ());
	
	RETURN (matching_pt);
	// return matching_pt;
#endif
}

/**
 * output: AFFECTED_NODES -- we use map<> instead of set<> to be able to
 * parallelize the loop. find_affected_region() takes 4% of the total analysis
 * on mcf. But this had no effect perhaps because each thread does little work.
 */

void pt_access_fi_map::
find_affected_region (set<pt_node_index> & nreach,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name,
	map<pt_node_index, bool> & affected_nodes)
{
	FUNBEGIN ();

	set<pt_node_index>::iterator ni;
	#pragma omp parallel for
	for (ni = nreach.begin (); ni != nreach.end (); ni++)
	{
		pt_node_index nid = *ni;

		// An entry for every reachable node (except non-representative
		// summ_cmpt nodes) will exist in NEW_PT_TO_ACCESS_NAME. This
		// is because the APs of all the reachable nodes have been
		// reset. Therefore, the following is false.
		// It is possible that APs of a node in NREACH are not stored
		// in new_pt_to_access_name if the APs of its predecessor nodes
		// did not change. In this case, we can say the APs of this
		// node are not affected.
		// if (new_pt_to_access_name.find (nid) == new_pt_to_access_name.end ())
		//	continue;

		set<pt_node_index> empty_set;
		access_name * new_an = get_access_name (nid, empty_set, summ_cmpts_map, new_pt_to_access_name);
		access_name * old_an = get_access_name (nid);

		if ((!new_an || !old_an) && new_an != old_an)
			affected_nodes[nid] = true;
			// affected_nodes.insert (nid);

		if (new_an && old_an && !new_an->is_same (*old_an))
			affected_nodes[nid] = true;
			// affected_nodes.insert (nid);
	}

#if RESET_ACCESS_NAMES == 0
	if (nreach.size ())
	{
		RESULT ("\nError: If RESET_ACCESS_NAMES==0, why has nreach been computed?");
	}

	// Only affected nodes are saved in new_pt_to_access_name.
	map<pt_node_index, access_name>::iterator nan;
	#pragma omp parallel for
	for (nan = new_pt_to_access_name.begin (); nan != new_pt_to_access_name.end (); nan++)
	{
		pt_node_index nid = nan->first;
		access_name * new_an = nan->second;
		access_name * old_an = get_access_name (nid);

		if ((!new_an || !old_an) && new_an != old_an)
			affected_nodes[nid] = true;
			// affected_nodes.insert (nid);

		if (new_an && old_an && !new_an->is_same (*old_an))
			affected_nodes[nid] = true;
			// affected_nodes.insert (nid);
	}
#endif

	RETURN_VOID ();
}

#if SUMM_K_CONSISTENT
max_depth pt_access_fi_map::
get_max_depth (pt_node_index pnid,
	set<pt_node_index> & ext_bndry,
	map<pt_node_index, max_depth> & new_pt_to_max_depth)
{
	// If PNID is in EXT_BNDRY, then fetch its max_depth from PT_TO_MAX_DEPTH.
	// Else fetch its max_depth from NEW_PT_TO_MAX_DEPTH.

	if (ext_bndry.find (pnid) != ext_bndry.end ())
	{
		if (pt_to_max_depth.find (pnid) != pt_to_max_depth.end ())
			return pt_to_max_depth[pnid];
		else
		{
			RESULT ("\nError: pt_to_max_depth[pnid=%d] not found", pnid);
			return 0;
		}
	}
		
	if (new_pt_to_max_depth.find (pnid) != new_pt_to_max_depth.end ())
		return new_pt_to_max_depth[pnid];

	// It is not an error if max_depth of pnid is not found in
	// new_pt_to_max_depth. This could be because its new max_depth still
	// needs to be computed.

	return 0;
}
#endif

#if SUMM_K_CONSISTENT
max_depth pt_access_fi_map::
get_max_depth (pt_node_index pnid)
{
	if (pt_to_max_depth.find (pnid) != pt_to_max_depth.end ())
		return pt_to_max_depth[pnid];

	return 0;
}
#endif

access_name * pt_access_fi_map::
get_access_name (pt_node_index pnid,
	set<pt_node_index> & ext_bndry,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	FUNBEGIN ();

	// If PNID is in EXT_BNDRY, then fetch its access path from PT_TO_ACCESS_NAME.
	// Else fetch its access path from NEW_PT_TO_ACCESS_NAME.

	if (ext_bndry.find (pnid) != ext_bndry.end ())
	{
		if (pt_to_access_name.find (pnid) != pt_to_access_name.end ())
			RETURN (&pt_to_access_name[pnid]);
			// return &pt_to_access_name[pnid];
		else
		{
			RESULT ("\nError: pt_to_access_name[pnid=%d] not found", pnid);
			RETURN (NULL);
			// return NULL;
		}
	}

#if SUMM_K_CONSISTENT	
	// If PNID belongs to a summ_cmpt, then fetch the access name of the
	// representative node of its summ_cmpt.	
	if (summ_cmpts_map.find (pnid) != summ_cmpts_map.end ())
	{
		pt_node_index repr_nid = summ_cmpts_map[pnid];
		if (new_pt_to_access_name.find (repr_nid) != new_pt_to_access_name.end ())
			RETURN (&new_pt_to_access_name[repr_nid]);
			// return &new_pt_to_access_name[repr_nid];
		else
		{
			RETURN (NULL);
			// return NULL;
		}
	}
#endif

	if (new_pt_to_access_name.find (pnid) != new_pt_to_access_name.end ())
		RETURN (&new_pt_to_access_name[pnid]);
		// return &new_pt_to_access_name[pnid];

#if RESET_ACCESS_NAMES == 0
	// Tried on spec. Too approximate. When access name of nodes in loop
	// does not change, its in (killed) edge is retained.
	// Approximation: Do not use a reset value of affected nodes. Instead
	// use the value in pt_to_access_name so that faster fixed point is
	// reached.
	// This is too approximate. No killing happens. E.g. If x->n1, is
	// killed, name of n1 remains {x} only.
	if (pt_to_access_name.find (pnid) != pt_to_access_name.end ())
		RETURN (&pt_to_access_name[pnid]);
		// return &pt_to_access_name[pnid];
#endif

	// It is not an error if access name of pnid is not found in
	// new_pt_to_access_name. This could be because its new access paths
	// still need to be computed.

	RETURN (NULL);
	// return NULL;
}

access_name * pt_access_fi_map::
get_access_name (pt_node_index pnid)
{
	if (pt_to_access_name.find (pnid) != pt_to_access_name.end ())
		return &pt_to_access_name[pnid];

	return NULL;
}

label pt_access_fi_map::
get_node_name_type (pt_node_index pnid)
{
	if (pt_to_access_name.find (pnid) == pt_to_access_name.end ())
		return 0;

	return pt_to_access_name[pnid].get_node_name_type ();
}

bool pt_access_fi_map::
get_ap_unbounded (pt_node_index pnid)
{
	if (pt_to_access_name.find (pnid) == pt_to_access_name.end ())
		return 0;

	return pt_to_access_name[pnid].get_ap_unbounded ();
}

set<ap_node_index> pt_access_fi_map::
get_ap_nodes (pt_node_index pnid)
{
	if (pt_to_access_name.find (pnid) == pt_to_access_name.end ())
	{
		set<ap_node_index> s;
		return s;
	}

	return pt_to_access_name[pnid].get_ap_nodes ();
}

#if SUMM_K_CONSISTENT
void pt_access_fi_map::
compute_summ_cmpts_map (set<set<pt_node_index> > & summ_cmpts,
	map<pt_node_index, pt_node_index> & summ_cmpts_map)
{
	set<set<pt_node_index> >::iterator sci;
	for (sci = summ_cmpts.begin (); sci != summ_cmpts.end (); sci++)
	{
		set<pt_node_index> sc = *sci;
		pt_node_index repr_node = *(sc.begin ());
		set<pt_node_index>::iterator ci;
		for (ci = sc.begin (); ci != sc.end (); ci++)
		{
			pt_node_index n = *ci;
			if (summ_cmpts_map.find (n) != summ_cmpts_map.end ())
			{
				RESULT ("\nError: Summ_cmpt_map of ptnode=%d already assigned", n);
				continue;
			}
			summ_cmpts_map[n] = repr_node;
		}
	}
}
#endif

#if SUMM_K_CONSISTENT
void pt_access_fi_map::
update_summ_cmpts (pt_node_index src_nid, 
	label l,
	pt_node_index dest_nid,
	set<pt_node_index> & ext_bndry,
	map<pt_node_index, max_depth> & new_pt_to_max_depth,
	set<set<pt_node_index> > & summ_cmpts)
{
	max_depth src_md = get_max_depth (src_nid, ext_bndry, new_pt_to_max_depth);
	max_depth dest_md = get_max_depth (dest_nid, ext_bndry, new_pt_to_max_depth);

	if (dest_md != SUMM_K_CONSISTENT)
		return;

	if (src_md == SUMM_K_CONSISTENT)
		merge_summ_cmpts (src_nid, dest_nid, summ_cmpts);
	else
		create_new_summ_cmpt (dest_nid, summ_cmpts);
}
#endif

#if SUMM_K_CONSISTENT
set<pt_node_index> pt_access_fi_map::
get_summ_cmpt (pt_node_index pt_nid, 
	set<set<pt_node_index> > & summ_cmpts)
{
	set<set<pt_node_index> >::iterator sci;
	for (sci = summ_cmpts.begin (); sci != summ_cmpts.end (); sci++)
	{
		set<pt_node_index> sc = *sci;
		if (sc.find (pt_nid) != sc.end ())
			return sc;
	}
	set<pt_node_index> new_summ_cmpt;
	new_summ_cmpt.insert (pt_nid);
	return new_summ_cmpt;
}
#endif

#if SUMM_K_CONSISTENT
void pt_access_fi_map::
merge_summ_cmpts (pt_node_index src_nid,
	pt_node_index dest_nid,
	set<set<pt_node_index> > & summ_cmpts)
{
	set<pt_node_index> src_cmpt = get_summ_cmpt (src_nid, summ_cmpts);
	set<pt_node_index> dest_cmpt = get_summ_cmpt (dest_nid, summ_cmpts);
	if (src_cmpt == dest_cmpt)
		return;
	
	summ_cmpts.erase (src_cmpt);
	summ_cmpts.erase (dest_cmpt);
	// src_cmpt.insert (dest_cmpt.begin (), dest_cmpt.end ());
	merge_set (dest_cmpt, src_cmpt);
	summ_cmpts.insert (src_cmpt);
}
#endif

#if SUMM_K_CONSISTENT
void pt_access_fi_map::
create_new_summ_cmpt (pt_node_index dest_nid,
	set<set<pt_node_index> > & summ_cmpts)
{
	set<pt_node_index> dest_cmpt = get_summ_cmpt (dest_nid, summ_cmpts);
	summ_cmpts.insert (dest_cmpt);
}
#endif

#if SUMM_K_CONSISTENT
void pt_access_fi_map::
update_max_depth (pt_node_index src_nid, 
	label l,
	pt_node_index dest_nid,
	set<pt_node_index> & ext_bndry,
	map<pt_node_index, max_depth> & new_pt_to_max_depth)
{
	DEBUG ("\nupdate_max_depth(src=%d,dest=%d)", src_nid, dest_nid);
	max_depth src_md = get_max_depth (src_nid, ext_bndry, new_pt_to_max_depth);
	DEBUG ("\nsrc_max_depth=%d", src_md);	

	if (!l)
		set_max_depth (dest_nid, src_md + 1, new_pt_to_max_depth);
	else if (l == wild_card_id)
		set_max_depth (dest_nid, SUMM_K_CONSISTENT, new_pt_to_max_depth);
	else
		set_max_depth (dest_nid, src_md, new_pt_to_max_depth);
}
#endif

/**
 * This function sets the max_depth of 0 to K. A value greater than
 * K is also stored as K. It does not overwrite a greater max_depth
 * in pt_to_max_depth to a lower value.
 */

#if SUMM_K_CONSISTENT
void pt_access_fi_map::
set_max_depth (pt_node_index pt_nid, 
	max_depth new_md,
	map<pt_node_index, max_depth> & new_pt_to_max_depth)
{
	DEBUG ("\nset_max_depth(dest=%d)", pt_nid);
	DEBUG ("\nold_max_depth=%d, new_max_depth=%d", 
		new_pt_to_max_depth[pt_nid], new_md);

	if (new_md >= SUMM_K_CONSISTENT)
	{
		new_pt_to_max_depth[pt_nid] = SUMM_K_CONSISTENT;
		return;
	}

	max_depth old_md = new_pt_to_max_depth[pt_nid];

	if (old_md >= new_md)
		return;

	new_pt_to_max_depth[pt_nid] = new_md;
}
#endif

#if SUMM_K_CONSISTENT
void pt_access_fi_map::
set_max_depth (pt_node_index pt_nid, max_depth new_md)
{
	set_max_depth (pt_nid, new_md, pt_to_max_depth);
}
#endif

#if SUMM_K_CONSISTENT
void pt_access_fi_map::
set_max_depth (map<pt_node_index, bool> & affected_nodes,
	map<pt_node_index, max_depth> & new_pt_to_max_depth)
{
	map<pt_node_index, bool>::iterator ni;
	for (ni = affected_nodes.begin (); ni != affected_nodes.end (); ni++)
	{
		pt_node_index nid = ni->first;
		if (new_pt_to_max_depth.find (nid) == new_pt_to_max_depth.end ())
		{
			RESULT ("\nError: New max_depth of affected node=%d not set", nid);
			continue;
		}
		max_depth new_max_depth = new_pt_to_max_depth[nid];
		set_max_depth (nid, new_max_depth);
	}
}
#endif

void pt_access_fi_map::
set_access_name (pt_node_index pt_nid, access_name & new_access_name)
{
#if DEBUG_CONTAINER
	// This is not an error. Heap locations initially have 0 APs.
	if (new_access_name.is_ap_nodes_empty ())
	{
		DEBUG ("\nAPs of pt-node=%d is being set to empty", pt_nid);
		// return;
	}

	if (pt_to_access_name.find (pt_nid) != pt_to_access_name.end ())
	{
		access_name old_an = pt_to_access_name[pt_nid];
		// This is not an error. When an already existing node is used as a
		// clone, its APs are set again.
		if (old_an.is_ap_nodes_empty ())
		{
			DEBUG ("\nAPs of pt node=%d already exist", pt_nid);
			// return;
		}
	}

	DEBUG ("\nSetting aps of pt-node=%d to ap=", pt_nid);
	new_access_name.print_ap_nodes (NULL);

	DEBUG ("\nSet access_name of pt-node=%d", pt_nid);

	DEBUG ("\nBefore set_access_path of pt_nid=%d=", pt_nid);
	new_access_name.print (NULL);
#endif

	// Update pt_to_access_name after updating access_name_to_pt maps
	// because the latter needs to fetch the old access name of pt_nid in
	// order to delete the old access name before the new one is stored.
	set_access_name_to_pt (new_access_name, pt_nid);

	pt_to_access_name[pt_nid] = new_access_name;

#if DEBUG_CONTAINER
	// DEBUG ("\nAfter set_reverse_access_path of pt_nid=%d=", pt_nid);
	// print_map (NULL, NULL);
#endif
}

void pt_access_fi_map::
set_access_name (map<pt_node_index, bool> & affected_nodes,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	map<pt_node_index, bool>::iterator ni;
	for (ni = affected_nodes.begin (); ni != affected_nodes.end (); ni++)
	{
		pt_node_index nid = ni->first;	
		#if CHECK_CONTAINER
		if (new_pt_to_access_name.find (nid) == new_pt_to_access_name.end ())
		{
			RESULT ("\nError: New access name of affected node=%d not set", nid);
			continue;
		}
		#endif
		access_name new_access_name = new_pt_to_access_name[nid];
		set_access_name (nid, new_access_name);
	}
}

void pt_access_fi_map::
set_access_name_to_pt (access_name & new_access_name,
	pt_node_index pt_nid)
{
#if SINGLE_REVERSE_MAP

#if CHECK_CONTAINER
	if (pt_to_access_name.find (pt_nid) != pt_to_access_name.end ())
	{
		// No need to delete old access name as the following do not
		// change once set.
		// (a) node_name_type: type information is added to the parser's set
		// of variables. gPT heap node, as before, continues to have
		// the same heap id. 
		// (b) ap_nodes of root node does not change. ap_nodes of
		// on-the-fly created heap field node is set here for the first
		// time. 
		// FIXME: confirm this. But this is required only for
		// on-the-fly nodes.

		DEBUG ("\nfound old access name pt=%d", pt_nid);
		access_name old_access_name = pt_to_access_name[pt_nid];
		if (old_access_name.is_same (new_access_name))
		{
			DEBUG ("\nNo update for pt_nid=%d", pt_nid);
			return;
		}
		if (!old_access_name.is_subset (new_access_name))
		{
			RESULT ("\nError: old_access_name is not subset of new_access_name of pt=%d", 
				pt_nid);
			return;
		}

		// Old access name may be updated when first access_name with
		// only node_name_type is set, then ap_nodes of access_name is
		// updated.
		RESULT ("\nError: There should have been no change in  access name pt=%d", pt_nid);
		access_name_to_pt.erase (old_access_name);

#if DEBUG_CONTAINER
		DEBUG ("\nErased old pt_nid=%d from map", pt_nid);
		DEBUG ("\nErased access_name=");
		old_access_name.print (NULL);
#endif
	}
#endif

	access_name_to_pt[new_access_name] = pt_nid;

#else

	bool ap_unbounded = new_access_name.get_ap_unbounded ();
	ap_unbounded_to_pts[ap_unbounded].insert (pt_nid);
	DEBUG ("\nSet rev_map ap_unbounded=%d->%d", ap_unbounded, pt_nid);

	label t = new_access_name.get_node_name_type ();
	type_to_pts[t].insert (pt_nid);
	DEBUG ("\nSet rev_map type=%d->%d", t, pt_nid);

	set<ap_node_index> ap_nodes = new_access_name.get_ap_nodes ();

#if DEBUG_CONTAINER
	// No need to delete old ap_nodes as once access paths of gPT node
	// are set, they do not change in their lifetime. Check this. For
	// on-the-fly created heap field nodes, both their type and ap_nodes
	// are set for the first time here. For the root nodes whose type is
	// discovered on-the-fly, type_to_pts can be updated. 
	if (pt_to_access_name.find (pt_nid) != pt_to_access_name.end ())
	{
		DEBUG ("\nfound old access_name for pt=%d", pt_nid);
		access_name old_access_name = pt_to_access_name[pt_nid];
		set<ap_node_index> ap_nodes_old = old_access_name.get_ap_nodes ();
		if (ap_nodes_old != ap_nodes)
		{
			RESULT ("\nError: Old and new ap_nodes of pt=%d differ", pt_nid);
			return;
		}
	}
#endif
	ap_nodes_to_pts[ap_nodes].insert (pt_nid);

#if DEBUG_CONTAINER
	DEBUG ("\nSet rev_map ap_nodes={");
	set<ap_node_index>::iterator api;
	for (api = ap_nodes.begin (); api != ap_nodes.end (); api++)
		DEBUG ("%d,", *api);
	DEBUG ("}->%d", pt_nid);
#endif
#endif
}

void pt_access_fi_map::
compute_ap (pt_node_index pt_nid, 
	label l, 
	type t,
	set<pt_node_index> & ext_bndry,
	ap_fi_graph & g_ap,
	access_name & dest_access_name,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	def_stmt_set ds;
#if SUMM_STMT_CLOSURE
	ds = get_def_stmt_set (pt_nid, l, ext_bndry, g_ap, new_pt_to_access_name);
#endif

	compute_ap (pt_nid, l, t, ds, ext_bndry, g_ap, dest_access_name,
		summ_cmpts_map, new_pt_to_access_name);
}

/**
 * Given pt node PT_NID, out-edge label l with defining statement ids in DS,
 * this function computes the APs that PT_NID appended with f represents.
 * in: NEW_PT_TO_ACCESS_NAME
 * out: DEST_ACCESS_NAME
 */

void pt_access_fi_map::
compute_ap (pt_node_index pt_nid, 
	label l, 
	type t,
	def_stmt_set ds,
	set<pt_node_index> & ext_bndry,
	ap_fi_graph & g_ap,
	access_name & dest_access_name,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	FUNBEGIN ();

	DEBUG ("\ncompute_ap (pt_nid=%d,l=%d,t=%d)", pt_nid, l, t);

//	if (program.heap_var (t))
		dest_access_name.add_node_name_type (t);
#if SUMM_POINTED_TO_BY
//	else
	if (!program.heap_var (t))
		dest_access_name.add_is_var_reachable (true);
#endif

	access_name * pnid_access_name = get_access_name (pt_nid, ext_bndry, summ_cmpts_map, new_pt_to_access_name);
	access_name pnid_an;
	if (!pnid_access_name)
		pnid_access_name = &pnid_an;

	// If source has ap_unbounded=true, then dest is also set to have
	// ap_unbounded=true.
	bool pnid_ap_unbounded = false;
	pnid_ap_unbounded = pnid_access_name->get_ap_unbounded ();
	#if INTERMEDIATE_RESULT
	if (pnid_ap_unbounded)
		RESULT ("\n(2)pnid_ap_unbounded=true of node=%d(ext_bndry=%d),l=%d", 
			pt_nid, ext_bndry.find (pt_nid) != ext_bndry.end (), l);
	#endif
	dest_access_name.add_ap_unbounded (pnid_ap_unbounded);

#if gAP_CYCLIC && SUMM_TYPE_K
	// If source has cyclic_edges, then dest should also have the same
	// cyclic edges.
	pnid_access_name->add_cyclic_edges (dest_access_name);
#endif

#if SUMM_POINTED_TO_BY
	bool pnid_is_var_reachable = false;
	pnid_is_var_reachable = pnid_access_name->get_is_var_reachable ();
	dest_access_name.add_is_var_reachable (pnid_is_var_reachable);
#endif

	set<ap_node_index> ap_src;
	pnid_access_name->get_ap_nodes (g_ap, l, ap_src);
	set<ap_node_index>::iterator api;

	for (api = ap_src.begin (); api != ap_src.end (); api++)
	{
		DEBUG ("\nAdding AP from ap-node=%d via l=%d, ds=", *api, l);
		#if DEBUG_CONTAINER
		DEBUG ("\nAdding AP from ap-node=%d via l=%d, ds=", *api, l);
		def_stmt_set::iterator si;
		for (si = ds.begin (); si != ds.end (); si++)
			DEBUG ("%d,", *si);
		#endif

		ap_node_index src_ap = *api;

		ap_node_index curr_dest_ap_node = 0;
		bool curr_dest_ap_unbounded = false;

#if SUMM_STMT_CLOSURE
		g_ap.update (src_ap, l, ds, curr_dest_ap_node, curr_dest_ap_unbounded);
#elif SUMM_K_CONSISTENT
		if (summ_cmpts_map.find (pt_nid) != summ_cmpts_map.end ())
		{
			DEBUG ("\nAppend wild_card_id to src_ap of pt_nid=%d", pt_nid);
			g_ap.update (src_ap, wild_card_id, curr_dest_ap_node, curr_dest_ap_unbounded);
		}
		else
		{
			DEBUG ("\nAppend l=%d to src_ap of pt_nid=%d", l, pt_nid);
			g_ap.update (src_ap, l, curr_dest_ap_node, curr_dest_ap_unbounded);
		}
#elif SUMM_TYPE_K && gAP_CYCLIC
		g_ap_cyclic_edges curr_dest_cyclic_edges;
		g_ap.update (src_ap, l, t, curr_dest_ap_node, curr_dest_ap_unbounded, curr_dest_cyclic_edges);
#elif SUMM_TYPE_K && !gAP_CYCLIC
		g_ap.update (src_ap, l, t, curr_dest_ap_node, curr_dest_ap_unbounded);
#elif SUMM_POINTED_TO_BY
		g_ap.update (src_ap, l, t, curr_dest_ap_node);
#else
		g_ap.update (src_ap, l, t, curr_dest_ap_node, curr_dest_ap_unbounded);
#endif

		if (curr_dest_ap_node)
			dest_access_name.add_ap_nodes (curr_dest_ap_node);
		dest_access_name.add_ap_unbounded (curr_dest_ap_unbounded);
#if SUMM_TYPE_K && gAP_CYCLIC
		dest_access_name.add_cyclic_edges (curr_dest_cyclic_edges);
#endif
	}

	#if DEBUG_CONTAINER
	DEBUG ("\ndest_ap_nodes=");
	dest_access_name.print (NULL);
	#endif

	RETURN_VOID ();
}

bool pt_access_fi_map::
is_pt_access_map_okay (ap_fi_graph & g_ap)
{
	bool is_okay = true;
	map<pt_node_index, access_name>::iterator mi;
	for (mi = pt_to_access_name.begin (); mi != pt_to_access_name.end (); mi++)
	{
		pt_node_index pnid = mi->first;
		access_name pan = mi->second;
		if (pan.is_ap_nodes_empty ())
		{
			label node_name_type = pan.get_node_name_type ();
			if (!node_name_type)
			{
				RESULT ("\nError: APs of stack pt-node=%d is empty", pnid);
				continue;
			}
		}
		pt_node_index find_pnid = find_pt_with_access_name (pan, pnid);
		if (find_pnid)
		{
			RESULT ("\nError: Access name of pt-nodes= %d and %d are same", 
				pnid, find_pnid);
			print_submap (pnid, g_ap);
			print_submap (find_pnid, g_ap);
			is_okay = false;
		}
	}
	if (is_okay)
		DEBUG ("\npt_access_map okay");	

	return is_okay;
}

pt_node_index pt_access_fi_map::
find_pt_with_access_name (access_name & an, pt_node_index exclude_nid)
{
	map<pt_node_index, access_name>::iterator mi;
	for (mi = pt_to_access_name.begin (); mi != pt_to_access_name.end (); mi++)
	{
		if (exclude_nid == mi->first)
			continue;
		access_name curr_an = mi->second;
		if (an.is_same (curr_an))
			return mi->first;
	}
	return 0;
}

#if SUMM_K_CONSISTENT
void pt_access_fi_map::
print_max_depth_map (map<pt_node_index, max_depth> & new_pt_to_max_depth)
{
	map<pt_node_index, max_depth>::iterator mi;
	for (mi = new_pt_to_max_depth.begin (); mi != new_pt_to_max_depth.end (); mi++)
		RESULT ("\npt=%d, depth=%d", mi->first, mi->second);
}
#endif

#if SUMM_K_CONSISTENT
void pt_access_fi_map::
print_summ_cmpts (set<set<pt_node_index> > & summ_cmpts)
{
	RESULT ("\nsumm_cmpts:");
	set<set<pt_node_index> >::iterator sci;
	for (sci = summ_cmpts.begin (); sci != summ_cmpts.end (); sci++)
	{
		set<pt_node_index> sc = *sci;
		set<pt_node_index>::iterator ci;
		RESULT ("\n(");
		for (ci = sc.begin (); ci != sc.end (); ci++)
			RESULT ("%d,", *ci);
		RESULT (")");
	}
}
#endif

#if SUMM_K_CONSISTENT
void pt_access_fi_map::
print_summ_cmpts_map (map<pt_node_index, pt_node_index> & summ_cmpts_map)
{
	RESULT ("\nsumm_cmpts_map: ");
	map<pt_node_index, pt_node_index>::iterator mi;
	for (mi = summ_cmpts_map.begin (); mi != summ_cmpts_map.end (); mi++)
		RESULT ("(%d,%d),", mi->first, mi->second);
}
#endif

void pt_access_fi_map::
get_statistics (ap_fi_graph & g_ap,
	unsigned int & max_ap_nodes_per_node,
	unsigned int & max_cyclic_edges_per_node,
	unsigned int & tot_access_names_with_cyclic_edges,
	unsigned int & tot_access_names_with_no_cyclic_edge,
	unsigned int & tot_ap,
	unsigned int & tot_ce,
	unsigned int & tot_ap_len,
	set<pt_node_index> & valid_nodes,
	bool all_valid)
{
	unsigned int tot_ap_per_node = 0;
	unsigned int tot_cyclic_edges_per_node = 0;
	unsigned int avg_acyclic_len_per_ap = 0;

	map<pt_node_index, access_name>::iterator ni;
	for (ni = pt_to_access_name.begin (); ni != pt_to_access_name.end (); ni++)
	{
		pt_node_index pn = ni->first;

		if (!all_valid)
			if (!pt_fi_node::is_node_valid_at_point (pn, valid_nodes))
				continue;
					
		access_name an = ni->second;
		set<ap_node_index> ap_nodes = an.get_ap_nodes ();
		tot_ap += ap_nodes.size ();
		if (max_ap_nodes_per_node < ap_nodes.size ())
			max_ap_nodes_per_node = ap_nodes.size ();

		set<ap_node_index>::iterator pi;
		for (pi = ap_nodes.begin (); pi != ap_nodes.end (); pi++)
		{
			ap_node_index ap_nid = *pi;
			list<label> ap;
			g_ap.get_access_paths (ap_nid, ap);
			tot_ap_len += ap.size ();
		}

#if gAP_CYCLIC && SUMM_TYPE_K
		g_ap_cyclic_edges ce = an.get_cyclic_edges ();
		if (ce.size ())
		{
			tot_ce += ce.size ();
			if (max_cyclic_edges_per_node < ce.size ())
				max_cyclic_edges_per_node = ce.size ();

			tot_access_names_with_cyclic_edges++;
		}
		else
			tot_access_names_with_no_cyclic_edge++;
#endif
	}
}

void pt_access_fi_map::
print_statistics (ap_fi_graph & g_ap)
{
	// per_node means per gpt node
	unsigned int max_ap_nodes_per_node = 0;
	unsigned int max_cyclic_edges_per_node = 0;
	unsigned int tot_access_names_with_cyclic_edges = 0;
	unsigned int tot_access_names_with_no_cyclic_edge = 0;
	unsigned int tot_ap = 0;
	unsigned int tot_ap_len = 0;
	unsigned int tot_ce = 0;

	set<pt_node_index> empty_set;
	bool all_valid = true;
	
	get_statistics (g_ap, 
		max_ap_nodes_per_node, 
		max_cyclic_edges_per_node, 
		tot_access_names_with_cyclic_edges,
		tot_access_names_with_no_cyclic_edge,
		tot_ap,
		tot_ce,
		tot_ap_len,
		empty_set,
		true);

	float avg_ap_per_node = 0;
	float avg_ce_per_node = 0;
	float avg_ap_len_per_ap = 0;

	if (pt_to_access_name.size ())
		avg_ap_per_node = (float) tot_ap / pt_to_access_name.size ();
	if (pt_to_access_name.size ())
		avg_ce_per_node = (float) tot_ce / pt_to_access_name.size ();
	if (tot_ap)
		avg_ap_len_per_ap = (float) tot_ap_len / tot_ap;

	unsigned int tot_access_names = access_name_to_pt.size ();

	RESULT ("\nFI, max_ap_nodes_per_node=%d", max_ap_nodes_per_node);
	RESULT ("\nFI, avg_ap_per_node=%f", avg_ap_per_node);
	RESULT ("\nFI, avg_ce_per_node=%f", avg_ce_per_node);
	RESULT ("\nFI, avg_acyclic_len_per_ap=%f", avg_ap_len_per_ap);
	RESULT ("\nFI, max_cyclic_edges_per_node=%d", max_cyclic_edges_per_node);
	RESULT ("\nFI, tot_alias_sets=%d", tot_access_names);
	RESULT ("\nFI, tot_alias_sets_with_cyclic_ap=%d", tot_access_names_with_cyclic_edges);
	RESULT ("\nFI, tot_alias_sets_with_no_cyclic_ap=%d", tot_access_names_with_no_cyclic_edge);

        FILE * stat_file = fopen (STAT_FILE, "a");
	if (!stat_file)
	{
		RESULT ("\nError: cannot open STAT_FILE=%d", STAT_FILE);
		return;
	}
	fprintf (stat_file, "\nFI, max_ap_nodes_per_node=%d", max_ap_nodes_per_node);
	fprintf (stat_file, "\nFI, avg_ap_per_node=%f", avg_ap_per_node);
	fprintf (stat_file, "\nFI, avg_ce_per_node=%f", avg_ce_per_node);
	fprintf (stat_file, "\nFI, avg_acyclic_len_per_ap=%f", avg_ap_len_per_ap);
	fprintf (stat_file, "\nFI, max_cyclic_edges_per_node=%d", max_cyclic_edges_per_node);
	fprintf (stat_file, "\nFI, tot_alias_sets=%d", tot_access_names);
	fprintf (stat_file, "\nFI, tot_alias_sets_with_cyclic_edges=%d", tot_access_names_with_cyclic_edges);
	fprintf (stat_file, "\nFI, tot_alias_sets_with_no_cyclic_edge=%d", tot_access_names_with_no_cyclic_edge);

        fclose (stat_file);
}


void pt_access_fi_map::
print_submap (set<pt_node_index> & pt_nodes,
	ap_fi_graph & g_ap)
{
	set<ap_node_index> ap;
	set<pt_node_index>::iterator pi;
	for (pi = pt_nodes.begin (); pi != pt_nodes.end (); pi++)
		print_submap (*pi, g_ap);
}

void pt_access_fi_map::
print_submap (pt_node_index pnid,
	ap_fi_graph & g_ap)
{
	if (pt_to_access_name.find (pnid) == pt_to_access_name.end ())
	{
		RESULT ("\npt=%d,empty access_name", pnid);
		return;
	}

	access_name an = pt_to_access_name[pnid];
	RESULT ("\npt=%d", pnid);
	an.print (&g_ap);
}

void pt_access_fi_map::
print_map (map<pt_node_index, access_name> & new_pt_to_access_name)
{
	RESULT ("\nnew_pt_to_access_name=");
	map<pt_node_index, access_name>::iterator mi;
	for (mi = new_pt_to_access_name.begin (); mi != new_pt_to_access_name.end (); mi++)
	{
		RESULT ("\npt=%d", mi->first);
		access_name an = mi->second;
		an.print (NULL);
	}
}

void pt_access_fi_map::
print_map (FILE * file, ap_fi_graph * g_ap)
{
	RESULT ("\npt_to_access_name=");
	map<pt_node_index, access_name>::iterator mi;
	for (mi = pt_to_access_name.begin (); mi != pt_to_access_name.end (); mi++)
	{
		RESULT ("\npt=%d", mi->first);
		access_name an = mi->second;
		an.print (g_ap);
	}

	print_reverse_map ();
}

void pt_access_fi_map::
print_pt_nodes (set<pt_node_index> & pts)
{
	RESULT ("{");
	set<pt_node_index>::iterator pi;
	for (pi = pts.begin (); pi != pts.end (); pi++)
		RESULT ("%d,", *pi);
	RESULT ("}");
}

void pt_access_fi_map::
print_reverse_map ()
{
#if SINGLE_REVERSE_MAP
	RESULT ("\naccess_name_to_pt=");
	map<access_name, pt_node_index>::iterator rmi;
	for (rmi = access_name_to_pt.begin (); rmi != access_name_to_pt.end (); rmi++)
	{
		RESULT ("\nap={");
		access_name an = rmi->first;
		an.print_ap_nodes (NULL);
		RESULT ("}, pt=%d", rmi->second);
		bool ap_unbounded = an.get_ap_unbounded ();
		RESULT (",ap_unbounded=%d", ap_unbounded);
	}

#else

	RESULT ("\nap_nodes_to_pts=");
	map<set<ap_node_index>, set<pt_node_index> >::iterator api;
	for (api = ap_nodes_to_pts.begin (); api != ap_nodes_to_pts.end (); api++)
	{
		set<ap_node_index> aps = api->first;
		RESULT ("\n");
		print_pt_nodes (aps);
		RESULT ("->");
		set<pt_node_index> pts = api->second;
		print_pt_nodes (pts);
	}

	RESULT ("\nap_unbounded_to_pts=");
	map<bool, set<pt_node_index> >::iterator upi;
	for (upi = ap_unbounded_to_pts.begin (); upi != ap_unbounded_to_pts.end (); upi++)
	{
		bool ap_unbounded = upi->first;
		set<pt_node_index> pts = upi->second;
		RESULT ("\n%d->", ap_unbounded);
		print_pt_nodes (pts);
	}

	RESULT ("\ntype_to_pts=");
	map<label, set<pt_node_index> >::iterator tpi;
	for (tpi = type_to_pts.begin (); tpi != type_to_pts.end (); tpi++)
	{
		label t = tpi->first;
		set<pt_node_index> pts = tpi->second;
		RESULT ("\n%d->", t);
		print_pt_nodes (pts);
	}
#endif
}

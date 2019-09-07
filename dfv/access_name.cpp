
/************************
 * @author Vini Kanvar
************************/

#include "access_name.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

access_name::
access_name ()
{
	node_name_type = 0;
	ap_unbounded = false;
#if SUMM_POINTED_TO_BY
	is_var_reachable = false;
#endif
}

access_name::
access_name (set<ap_node_index> & new_ap_nodes, bool new_ap_unbounded, bool new_is_var_reachable)
{
	node_name_type = 0;
	ap_unbounded = false;
#if SUMM_POINTED_TO_BY
	is_var_reachable = false;
#endif
	add_ap_nodes (new_ap_nodes);
	add_ap_unbounded (new_ap_unbounded);
#if SUMM_POINTED_TO_BY
	add_is_var_reachable (new_is_var_reachable);
#endif
}

access_name::
access_name (ap_node_index new_ap_nodes, bool new_ap_unbounded, bool new_is_var_reachable)
{
	node_name_type = 0;
	ap_unbounded = false;
#if SUMM_POINTED_TO_BY
	is_var_reachable = false;
#endif
	add_ap_nodes (new_ap_nodes);
	add_ap_unbounded (new_ap_unbounded);
#if SUMM_POINTED_TO_BY
	add_is_var_reachable (new_is_var_reachable);
#endif
#if DEBUG_CONTAINER
	DEBUG ("\ninit access_name=");
	print ();
#endif
}

access_name::
~access_name ()
{
}

bool access_name::
is_ap_nodes_empty ()
{
	return !ap_nodes.size ();
}

bool access_name::
is_ap_unbounded ()
{
	if (ap_unbounded)
		return true;

#if gAP_CYCLIC && SUMM_TYPE_K 
	if (cyclic_edges.size ())
		return true;
#endif

	return false;
}

set<ap_node_index> access_name::
get_ap_nodes ()
{
	return ap_nodes;
}

bool access_name::
get_ap_unbounded ()
{
	return ap_unbounded;
}

label access_name::
get_node_name_type ()
{
	return node_name_type;
}

#if gAP_CYCLIC && SUMM_TYPE_K
g_ap_cyclic_edges access_name::
get_cyclic_edges ()
{
	return cyclic_edges;
}
#endif

#if SUMM_POINTED_TO_BY
bool access_name::
get_is_var_reachable ()
{
	return is_var_reachable;
}
#endif

void access_name::
get_ap_nodes (ap_fi_graph & g_ap,
	label l,
	set<ap_node_index> & ap_nids)
{
	FUNBEGIN ();

	set<ap_node_index>::iterator api;
	for (api = ap_nodes.begin (); api != ap_nodes.end (); api++)
	{
	        ap_node_index ap_nid = *api;
		// If both SRC (AP_NID) and PT_NID represent the same variable
		// V, and L is non-zero, then do not save V.L AP since V_L
		// variable would have already been stored when V_L variable
		// node is analyzed.
		// If K=1, in SUMM_K_PREFIX, then ap_nid could be v
		// (representing say summarized AP of v.ASTERISK.f.g); so v_l
		// may not exist. If K=1, then store v itself i.e. do not skip
		// call to g_ap.update ().
		// WRONG: v_l will not exist only when K=0, which we do not
		// allow. This has been confirmed on test-casses.
		if ((SUMM_K_PREFIX && SUMM_K_PREFIX != 1) || !SUMM_K_PREFIX)
//			|| (SUMM_K_CONSISTENT && SUMM_K_CONSISTENT != 1) || !SUMM_K_CONSISTENT)


		// For SUMM_K_PREFIX=1, already things are so imprecise that
		// stack types also mismatch. It improves precision by allowing
		// v_l access paths. Therefore, allow v_l for SUMM_K_PREFIX=1
		// irrespective of whether src (ap_nid) and pt_nid have same name.
//		pt_fi_node * pn = g_pt.nodes[pt_nid];
//		label pt_name = pn->get_node_name (g_pt.stack.get_node_id ());
//		ap_fi_node * an = g_ap.nodes[ap_nid];
//		label ap_name = an->get_in_edge_label ();
//		if (pt_name == ap_name && pt_name)


#if SUMM_K_CONSISTENT
		if (l && l != wild_card_id)
#else
		if (l)
#endif
			if (g_ap.is_variable_node (ap_nid))
			{
				DEBUG ("\nSkipping ap_nid=%d->l=%d", ap_nid, l);
				continue;
			}
#if ONLY_STACK_APS
		// If SRC represents a heap variable, then do not save an
		// access path from SRC.
		if (g_ap.is_heap_node (ap_nid))
		{
			DEBUG ("\nSkipping heap ap_nid=%d->l=%d", ap_nid, l);
			continue;
		}

		if (ap_nid == g_ap.stack.get_node_id () && program.heap_var (l))
		{
			DEBUG ("\nSkipping heap name ap_nid=%d->l=%d", ap_nid, l);
			continue;
		}
#endif

		ap_nids.insert (ap_nid);

	}

	RETURN_VOID ();
}

/**
 *  Over-approximate cyclic edges in THIS. For each ap_node ap1 in THIS, add
 *  ap1->ap2 if ap1->ap2 is a cyclic edge in g_ap
 */

#if OVER_APPROX_CYCLIC_EDGES
void access_name::
over_approx_cyclic_edges (ap_fi_graph & g_ap)
{
	set<ap_node_index>::iterator api;
	for (api = ap_nodes.begin (); api != ap_nodes.end (); api++)
	{
		ap_node_index ap_nid = *api;
		ap_fi_node * ap_n = g_ap.nodes[ap_nid];
		
		ap_n->add_out_cyclic_node_ids (cyclic_edges);
	}
	if (cyclic_edges.size ())
		ap_unbounded = true;
}
#endif

bool access_name::
is_same (access_name & an)
{
	if (ap_unbounded != an.ap_unbounded)
		return false;
	if (node_name_type != an.node_name_type)
		return false;
	if (ap_nodes != an.ap_nodes)
		return false;

#if gAP_CYCLIC && SUMM_TYPE_K
	if (cyclic_edges != an.cyclic_edges)
		return false;
#endif
#if SUMM_POINTED_TO_BY
	if (is_var_reachable != an.is_var_reachable)
		return false;
#endif
	return true;
}

bool access_name::
is_subset (access_name & an)
{
	if (ap_unbounded > an.ap_unbounded)
		return false;
	if (node_name_type != an.node_name_type)
		return false;
	set<ap_node_index>::iterator ai;
	for (ai = ap_nodes.begin (); ai != ap_nodes.end (); ai++)
	{
		ap_node_index aid = *ai;
		if (an.ap_nodes.find (aid) == an.ap_nodes.end ())
			return false;
	}

#if gAP_CYCLIC && SUMM_TYPE_K
	g_ap_cyclic_edges::iterator ei;
	for (ei = cyclic_edges.begin (); ei != cyclic_edges.end (); ei++)
	{
		ap_node_index apsrc = ei->first;
		if (an.cyclic_edges.find (apsrc) == an.cyclic_edges.end ())
			return false;

		set<ap_node_index> an_ce_dests = an.cyclic_edges[apsrc];
		set<ap_node_index> apdests = ei->second;
		set<ap_node_index>::iterator di;
		for (di = apdests.begin (); di != apdests.end (); di++)
		{
			ap_node_index dest = *di;
			if (an_ce_dests.find (dest) == an_ce_dests.end ())
				return false;
		}
	}
#endif

#if SUMM_POINTED_TO_BY
	if (is_var_reachable == true && an.is_var_reachable ==  false)
		return false;
#endif

	return true;
}

bool
operator< (const access_name & an1, const access_name & an2) 
{
	if (an1.ap_unbounded != an2.ap_unbounded)
		return an1.ap_unbounded < an2.ap_unbounded;
	if (an1.node_name_type != an2.node_name_type)
		return an1.node_name_type < an2.node_name_type;
	if (an1.ap_nodes != an2.ap_nodes)
		return an1.ap_nodes < an2.ap_nodes;

#if gAP_CYCLIC && SUMM_TYPE_K
	return an1.cyclic_edges < an2.cyclic_edges;	
#elif SUMM_POINTED_TO_BY
	return an1.is_var_reachable < an2.is_var_reachable;
#else
	return false;
#endif
}

void access_name::
add_ap_nodes (set<ap_node_index> & new_ap_nodes)
{
	#if CHECK_CONTAINER
	if (new_ap_nodes.find (0) != new_ap_nodes.end ())
	{
		RESULT ("\nError: Dont insert set with ap nid=0");
		return;
	}
	#endif
	// ap_nodes.insert (new_ap_nodes.begin (), new_ap_nodes.end ());
	merge_set (new_ap_nodes, ap_nodes);
}

void access_name::
add_ap_nodes (ap_node_index new_ap_nodes)
{
	if (new_ap_nodes == 0)
	{
		RESULT ("\nError: Dont insert ap nid=0");
		return;
	}
	ap_nodes.insert (new_ap_nodes);
}

#if gAP_CYCLIC && SUMM_TYPE_K
void access_name::
add_cyclic_edges (access_name & dest_access_name)
{
	FUNBEGIN ();

	dest_access_name.add_cyclic_edges (cyclic_edges);

	RETURN_VOID ();
}
#endif

#if gAP_CYCLIC && SUMM_TYPE_K
void access_name::
add_cyclic_edges (g_ap_cyclic_edges & new_cyclic_edges)
{
	FUNBEGIN ();
#if gAP_CYCLIC_EDGES == 0
	return;
#endif

	// Add new_cyclic_edge aps->apd only if aps and apd are ancestors of THIS access_name.
	g_ap_cyclic_edges::iterator ei;
	for (ei = new_cyclic_edges.begin (); ei != new_cyclic_edges.end (); ei++)
	{
		ap_node_index apsrc = ei->first;
		set<ap_node_index> apdests = ei->second;
		cyclic_edges[apsrc].insert (apdests.begin (), apdests.end ());
	}

	RETURN_VOID ();
}
#endif

void access_name::
add_ap_unbounded (bool new_ap_unbounded)
{
	ap_unbounded |= new_ap_unbounded;
}

void access_name::
add_node_name_type (label new_node_name_type)
{
	#if CHECK_CONTAINER
	if (node_name_type && node_name_type != new_node_name_type)
	{
		RESULT ("\nError: Old-heap-type=%d is being set again to new-heap-type=%d",
			node_name_type, new_node_name_type);
		return;
	}
	#endif
	node_name_type = new_node_name_type;
}

#if SUMM_POINTED_TO_BY
void access_name::
add_is_var_reachable (bool new_is_var_reachable)
{
	is_var_reachable |= new_is_var_reachable;
}
#endif

void access_name::
add_access_name (access_name & an)
{
	add_ap_nodes (an.ap_nodes);
	add_ap_unbounded (an.ap_unbounded);
	add_node_name_type (an.node_name_type);
#if gAP_CYCLIC && SUMM_TYPE_K
	add_cyclic_edges (an.cyclic_edges);
#endif
#if SUMM_POINTED_TO_BY
	add_is_var_reachable (an.is_var_reachable);
#endif
}

void access_name::
set_ap_nodes (set<ap_node_index> & new_ap_nodes)
{
	ap_nodes.clear ();
	// ap_nodes.insert (new_ap_nodes.begin (), new_ap_nodes.end ());
	merge_set (new_ap_nodes, ap_nodes);
}

#if SUMM_POINTED_TO_BY
void access_name::
set_is_var_reachable (bool new_is_var_reachable)
{
	is_var_reachable = new_is_var_reachable;
}
#endif

void access_name::
print_ap_nodes (ap_fi_graph * g_ap)
{
	set<ap_node_index>::iterator api;
	for (api = ap_nodes.begin (); api != ap_nodes.end (); api++)
	{
		ap_node_index ap_nid = *api;
		if (!g_ap)
		{	
			RESULT ("%d,", ap_nid);
			continue;
		}
#if SUMM_STMT_CLOSURE
		list<pair<label, def_stmt_set> > ap;
#else
		list<label> ap;
#endif
		g_ap->get_access_paths (ap_nid, ap);
		RESULT ("\n\t%d=", ap_nid);
		g_ap->print_access_path (ap);
	}
}

#if SUMM_TYPE_K && gAP_CYCLIC
void access_name::
print_cyclic_edges ()
{
	g_ap_cyclic_edges::iterator cei;
	for (cei = cyclic_edges.begin (); cei != cyclic_edges.end (); cei++)
	{
		ap_node_index apsrc = cei->first;
		set<ap_node_index>  apdests = cei->second;
		set<ap_node_index>::iterator di;
		for (di = apdests.begin (); di != apdests.end (); di++)
			RESULT ("\n%d -> %d", apsrc, *di);
	}
}
#endif

void access_name::
print (ap_fi_graph * g_ap)
{
	RESULT (",node_name_type=%d", node_name_type);
	RESULT (",ap_unbounded=%d", ap_unbounded);
	if (!g_ap)
	{
		RESULT (",ap={");
		print_ap_nodes (NULL);
		RESULT ("}");
	}

#if gAP_CYCLIC && SUMM_TYPE_K
#if gAP_CYCLIC_EDGES == 1
        if (ap_unbounded && !cyclic_edges.size ())
                RESULT ("\nError: access name has ap_unbounded=%d, zero cyclic_edges",
                        ap_unbounded);
        if (cyclic_edges.size () && !ap_unbounded)
                RESULT ("\nError: access name has ap_unbounded=%d, non-zero cyclic_edges",
                        ap_unbounded);
#endif

        if (ap_unbounded)
        {
                RESULT (",cyclic_edges={");
                g_ap_cyclic_edges::iterator cei;
                for (cei = cyclic_edges.begin (); cei != cyclic_edges.end (); cei++)
                {
                        ap_node_index apsrc = cei->first;
			set<ap_node_index> apdests = cei->second;
			set<ap_node_index>::iterator di;
			for (di = apdests.begin (); di != apdests.end (); di++)
                                RESULT ("(%d->%d),", apsrc, *di);
                }
                RESULT ("}");
        }
#endif

#if SUMM_POINTED_TO_BY
	RESULT (",is_var_reachable=%d", is_var_reachable);
#endif

	if (g_ap)
	{
		set<ap_node_index> ap_src = get_ap_nodes ();
		set<ap_node_index>::iterator api;
		for (api = ap_src.begin (); api != ap_src.end (); api++)
		{
#if SUMM_STMT_CLOSURE
			list<pair<label, def_stmt_set> > ap;
#else
			list<label> ap;
#endif
			ap_node_index ap_nid = *api;
			g_ap->get_access_paths (ap_nid, ap);
			RESULT ("\n\t%d=", ap_nid);
			g_ap->print_access_path (ap);
		}
	}
}

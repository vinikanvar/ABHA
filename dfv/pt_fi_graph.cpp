
/************************
 * @author Vini Kanvar
************************/

#include "pt_fi_graph.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

pt_fi_graph::
pt_fi_graph () : stack (nodes)
{
#if SUMM_TYPE_K
	tot_weak_nodes = 0;
	max_weak_nodes_at_pp = 0;
	po_calls = 0;
#endif
}

pt_fi_graph::
~pt_fi_graph ()
{
	// TODO: Check and call this function
	map<pt_node_index, pt_fi_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); )
	{
		pt_fi_node * n = ni->second;
		if (n == &stack)
		{
			ni++;
			continue;
		}
		nodes.erase (ni++);
		delete n;
	}
}

int pt_fi_graph::
get_max_node_id ()
{
	return nodes.end ()->first;
}

void pt_fi_graph::
get_nodes_names (set<pt_node_index> & s, set<label> & names)
{
	pt_node_index stack_id = stack.get_node_id ();

	set<pt_node_index>::iterator ni;
	for (ni = s.begin (); ni != s.end (); ni++)
	{
		if (*ni == stack_id)
			continue;
		DEBUG ("\nget_node_name () of %d", *ni);
		pt_fi_node * n = nodes[*ni];
		label name = n->get_node_name (stack_id);
		// GET_NODE_NAME() returns 0 for STACK or NULL list of nodes.
		// Ignore it.
		if (name)
			names.insert (name);
	}
#if DEBUG_CONTAINER
	set<label>::iterator vi;
	DEBUG ("\nNodes-names: ");
	for (vi = names.begin (); vi != names.end (); vi ++)
		DEBUG ("%d,", *vi);
#endif
}

label pt_fi_graph::
get_node_name (pt_node_index nid)
{
	pt_node_index stack_id = stack.get_node_id ();
	pt_fi_node * n = nodes[nid];
	label name = n->get_node_name (stack_id);
	return name;
}

#if SUMM_K_CONSISTENT
void pt_fi_graph::
get_all_names (set<pt_node_index> & s, set<label> & names)
{
	pt_node_index stack_id = stack.get_node_id ();

	set<pt_node_index>::iterator ni;
	for (ni = s.begin (); ni != s.end (); ni++)
	{
		if (*ni == stack_id)
			continue;
		DEBUG ("\nget_all_names () of %d", *ni);
		pt_fi_node * n = nodes[*ni];
		n->get_all_names (stack_id, names);
	}
#if DEBUG_CONTAINER
	set<label>::iterator vi;
	DEBUG ("\nAll names: ");
	for (vi = names.begin (); vi != names.end (); vi ++)
		DEBUG ("%d,", *vi);
#endif
}
#endif

void pt_fi_graph::
get_nodes (set<label> & vars, set<pt_node_index> & valid_nodes, set<pt_node_index> & var_nodes)
{
	FUNBEGIN ();

	pt_node_index stack_id = stack.get_node_id ();

	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
		get_out_nodes (stack_id, *vi, var_nodes, valid_nodes);
 
	RETURN_VOID ();
}

set<pt_node_index> pt_fi_graph::
get_generated_nodes (int old_max_node_id)
{
	set<pt_node_index> new_pt_nodes;
	// set<pt_node_index> fresh_heap;
	DEBUG ("\nget_generated_nodes(old_max_node_id=%d)=", old_max_node_id);
	map<pt_node_index, pt_fi_node *>::reverse_iterator rit;
	for (rit = nodes.rbegin (); rit != nodes.rend (); rit++)
	{
		pt_node_index rnid = rit->first;
		if (rnid > old_max_node_id)
		{
			DEBUG ("%d,", rnid);
			new_pt_nodes.insert (rnid);
		}
		else
			break;
	} 

	return new_pt_nodes;
}

void pt_fi_graph::
get_fresh_named_nodes (set<pt_node_index> & var_nodes)
{
	set<pt_node_index>::iterator pni;
	for (pni = var_nodes.begin (); pni != var_nodes.end (); )
	{
		pt_node_index nid = *pni;
		DEBUG ("\nIs node=%d fresh?", nid);
		if (fresh_named_nodes.find (nid) == fresh_named_nodes.end ())
		{
			DEBUG ("=No");
			var_nodes.erase (pni++);
		}
		else
		{
			DEBUG ("=Yes");
			pni++;
		}
	}
}

bool pt_fi_graph::
is_fresh_named_node (pt_node_index pnid)
{
	return (fresh_named_nodes.find (pnid) != fresh_named_nodes.end ());
}

bool pt_fi_graph::
is_fresh_heap_node (pt_node_index pnid)
{
	return (fresh_heap_nodes.find (pnid) != fresh_heap_nodes.end ());
}

bool pt_fi_graph::
is_heap_node (pt_node_index pnid)
{
	pt_fi_node * n = nodes[pnid];
	// A summary node is not a heap node (it may be a summary of stack nodes).
	label name = n->get_node_name (stack.get_node_id ());
	DEBUG ("\npnid=%d name=%d is_heap_node=%d", pnid, name, program.heap_var (name));
	return program.heap_var (name);
}

/**
 * input: pointee
 * output: in_nodes
 */

void pt_fi_graph::
get_in_nodes (pt_node_index pointee, set<pt_node_index> & in_nodes)
{
	pt_fi_node * n = nodes[pointee];
	map<label, set<pt_node_index> > in_edges = n->get_in_edge_list ();
	map<label, set<pt_node_index> >::iterator ei;
	for (ei = in_edges.begin (); ei != in_edges.end (); ei++)
	{
		set<pt_node_index> n_in_nodes = ei->second;
		// in_nodes.insert (n_in_nodes.begin (), n_in_nodes.end ());
		merge_set (n_in_nodes, in_nodes);
	}
}

void pt_fi_graph::
get_in_nodes (pt_node_index dest_nid, 
	label l, 
	set<pt_node_index> & in_nodes,
	set<pt_node_index> & valid_nodes)
{
	pt_fi_node * dest_n = nodes[dest_nid];
	set<pt_node_index> in_nodes_temp = dest_n->get_in_nodes (l);
	pt_fi_node::get_nodes_valid_at_point (in_nodes_temp, valid_nodes);
	in_nodes.insert (in_nodes_temp.begin (), in_nodes_temp.end ());
}

void pt_fi_graph::
get_out_nodes (pt_node_index src_nid, 
	label l, 
	set<pt_node_index> & out_nodes,
	set<pt_node_index> & valid_nodes)
{
	pt_fi_node * src_n = nodes[src_nid];
	set<pt_node_index> out_nodes_temp = src_n->get_out_nodes (l);
	pt_fi_node::get_nodes_valid_at_point (out_nodes_temp, valid_nodes);
	out_nodes.insert (out_nodes_temp.begin (), out_nodes_temp.end ());
}

/**
 * @returns true if source is null/undef/readonly node; in which case, out-edge
 * is missing i.e. the destination is undef.
 */

bool pt_fi_graph::
get_destination_nodes (set<pt_node_index> & src_nids, label l, set<pt_node_index> & dest_nodes)
{
	set<pt_node_index> empty_nodes;
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
	return get_destination_nodes (src_nids, l, dest_nodes,
		empty_nodes, empty_edges, empty_edges);
}

/**
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: dest_nodes
 * @returns true if source is null/undef/readonly node; in which case, out-edge
 * is missing i.e. the destination is undef.
 */

bool pt_fi_graph::
get_destination_nodes (set<pt_node_index> & src_nids, label l, set<pt_node_index> & dest_nodes,
	set<pt_node_index> & value_excl_out_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	bool out_edge_missing = false;

	set<pt_node_index>::iterator ni;
	for (ni = src_nids.begin (); ni != src_nids.end (); ni++)
	{
		DEBUG ("\nget_dest_nodes (node=%d,field=%d)", *ni, l);
		pt_fi_node * n = nodes[*ni];
		set<pt_node_index> dest_nodes_temp;
		out_edge_missing += n->get_destination_nodes (l, stack.get_node_id (), dest_nodes_temp,
			value_excl_out_edges, incl_in_edges, incl_out_edges);

		#if DEBUG_CONTAINER
		// Check if DESTINATION_NODES are the dests of S
		set<pt_node_index>::iterator di;
		DEBUG ("\ndest_nodes_temp: ");
		for (di = dest_nodes_temp.begin (); di != dest_nodes_temp.end (); di++)
		{
			pt_fi_node * dest = nodes[*di];
			#if !SUMM_K_CONSISTENT 
			map<label, set<pt_node_index> > dest_in_edges = dest->get_in_edge_list ();
			set<pt_node_index> s = dest_in_edges[l];
			#if CHECK_CONTAINER
			if (s.find (n->get_node_id ()) == s.end ())
				RESULT ("\nError: did not get correct dest nodes");
			#endif
			#endif
			DEBUG ("%d,", *di);
		}
		#endif
		// dest_nodes.insert (dest_nodes_temp.begin (), dest_nodes_temp.end ());
		merge_set (dest_nodes_temp, dest_nodes);
	}

	#if DEBUG_CONTAINER
	DEBUG ("\nFetched dest nodes for l %d: ", l);
	for (ni = dest_nodes.begin (); ni != dest_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
	#endif

	DEBUG ("\nout_edge_missing=%d", out_edge_missing);
	return out_edge_missing;
}

void pt_fi_graph::
get_destination_nodes (pt_node_index src_nid, 
	label l, 
	set<pt_node_index> & dest_nodes,
	set<pt_node_index> & valid_nodes)
{
	pt_fi_node * src_n = nodes[src_nid];
	pt_node_index stack_id = stack.get_node_id ();
	src_n->get_destination_nodes (l, stack_id, dest_nodes);
	pt_fi_node::get_nodes_valid_at_point (dest_nodes, valid_nodes);
}

void pt_fi_graph::
get_destination_nodes (set<pt_node_index> & src_nids, 
	label l, 
	set<pt_node_index> & dest_nodes,
	set<pt_node_index> & valid_nodes)
{
	get_destination_nodes (src_nids, l, dest_nodes);
	pt_fi_node::get_nodes_valid_at_point (dest_nodes, valid_nodes);
}

bool pt_fi_graph::
get_destination_nodes (set<pt_node_index> & src_nids, 
	label l, 
	set<pt_node_index> & dest_nodes,
	set<pt_node_index> & valid_nodes,
	set<pt_node_index> & value_excl_out_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	get_destination_nodes (src_nids, l, dest_nodes,
		value_excl_out_edges, incl_in_edges, incl_out_edges);
	pt_fi_node::get_nodes_valid_at_point (dest_nodes, valid_nodes);
}

/** 
 * This function returns the successor nodes of PT_NIDS using out-edges and
 * Egen (LPTR to RPTR new edges) and invis_in_edges that are present in VALUE.
 */

void pt_fi_graph::
get_out_adj_nodes (set<pt_node_index> pt_nids,
	set<pt_node_index> & lptr,
	set<pt_node_index> & rptr,
	map<pt_node_index, map<label, set<pt_node_index> > > & invis_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & invis_out_edges,
	set<pt_node_index> & out_adj_nodes,
	set<pt_node_index> & valid_nodes)
{
	FUNBEGIN ();

	bool rptr_merged = false;

	// Consider pre-existing out edges of PT_NIDS.
	// Here we do not exclude Ekill edges because the out-nodes reachable
	// via Ekill edges are anyway included by default by the caller of this
	// function get_out_adj_nodes() i.e. find_ans_and_affected_region().
	set<pt_node_index>::iterator pni;
	for (pni = pt_nids.begin (); pni != pt_nids.end (); pni++)
	{
		pt_node_index pt_nid = *pni;
		pt_fi_node * pt_n = nodes[pt_nid];

		pt_n->get_out_adj_nodes (out_adj_nodes, valid_nodes);

		// Consider Egen
		if (!rptr_merged && lptr.find (pt_nid) != lptr.end ())
		{
			// out_adj_nodes.insert (rptr.begin (), rptr.end ());
			merge_set (rptr, out_adj_nodes);
			rptr_merged = true;
		}

#if PULL_ACCESS_NAMES == 0
		// Consider invis_out_edges
		map<label, set<pt_node_index> > invis_nid_out_edges;
		if (invis_out_edges.find (pt_nid) != invis_out_edges.end ())
			invis_nid_out_edges = invis_out_edges[pt_nid];
		for (ei = invis_nid_out_edges.begin (); ei != invis_nid_out_edges.end (); ei++)
		{
			set<pt_node_index> invis_out_nodes = ei->second;
			merge_set (invis_out_nodes, out_adj_nodes);
		}
#endif
	}

#if PULL_ACCESS_NAMES
	// Consider invis_in_edges
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator inei;
	for (inei = invis_in_edges.begin (); inei != invis_in_edges.end (); inei++)
	{
		pt_node_index dest = inei->first;
		bool dest_merged = false;
		map<label, set<pt_node_index> > ine = inei->second;
		map<label, set<pt_node_index> >::iterator ei;
		for (ei = ine.begin (); ei != ine.end (); ei++)
		{
			set<pt_node_index> src = ei->second;
			set<pt_node_index>::iterator si;
			for (si = src.begin (); si != src.end (); si++)
			{
				if (pt_nids.find (*si) != pt_nids.end ())
				{
					out_adj_nodes.insert (dest);
					dest_merged = true;
					break;
				}
			}
			if (dest_merged)
				break;
		}
	}
#endif

	RETURN_VOID ();
}

/**
 * This function stores all the adjoining nodes of NVISIT in NVISIT. A
 * node is adjoining to a node in NVISIT if it is adjoining in (E-Ekill)UEgen
 * edges or INVIS_IN_EDGES of THIS graph and it is in VALUE.
 */

void pt_fi_graph::
get_in_out_adj_nodes (set<pt_node_index> & nvisit,
	set<pt_node_index> & valid_nodes,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	FUNBEGIN ();

	DEBUG ("\nget_adjoining_nodes()");

	set<pt_node_index> adjoining_nodes;
	set<pt_node_index>::iterator ni;
	for (ni = nvisit.begin (); ni != nvisit.end (); ni++)
	{
		pt_node_index nid = *ni;
		pt_fi_node * n = nodes[nid];
		n->get_in_out_adj_nodes (lptr, must_lptr, l, rpte, incl_in_edges, incl_out_edges,
			adjoining_nodes, valid_nodes);
	}

	RETURN_VOID ();
}

#if SUMM_TYPE_CLOSURE == 0 && FILTER_EXISTING_EDGES
void pt_fi_graph::
keep_new_edges (set<pt_node_index> & valid_nodes,
	set<pt_node_index> & must_lptr,
	set<pt_node_index> & lptr,
	label l,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	// Check whether an edge lptr->l->rpte already exists
	set<pt_node_index>::iterator li;
	for (li = lptr.begin (); li != lptr.end (); li++)
	{	
		pt_node_index new_src_node = *li;
		// Do not filter out an edge if it is in must node
		if (l == ASTERISK && must_lptr.find (new_src_node) != must_lptr.end ())
			continue;

		set<pt_node_index> old_dest_nodes;
		get_out_nodes (new_src_node, l, old_dest_nodes, valid_nodes);
		if (!old_dest_nodes.size ())
			continue;
		set<pt_node_index>::iterator ri;
		for (ri = rpte.begin (); ri != rpte.end (); )
		{
			pt_node_index new_dest_node = *ri;
			if (old_dest_nodes.find (new_dest_node) != old_dest_nodes.end ())
			{
				RESULT ("\nFilter edge %d->%d->%d", new_src_node, l, new_dest_node);
				rpte.erase (ri++);
			}
			else
				ri++;
		}
	}
	if (!rpte.size ())
		lptr.clear ();

#if PULL_ACCESS_NAMES
	// Check whether an edge incl_in_edges already exists
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator iei;
	for (iei = incl_in_edges.begin (); iei != incl_in_edges.end (); iei++)
	{
		pt_node_index new_dest_node = iei->first;
		map<label, set<pt_node_index> > in_edges = iei->second;
		map<label, set<pt_node_index> >::iterator ei;
		for (ei = in_edges.begin (); ei != in_edges.end (); ei++)
		{
			label new_l = ei->first;
			set<pt_node_index> new_src_nodes = ei->second;

			set<pt_node_index> old_src_nodes;
			get_in_nodes (new_dest_node, new_l, old_src_nodes, valid_nodes);
			if (!old_src_nodes.size ())
				continue;

			set<pt_node_index>::iterator ni;
			for (ni = new_src_nodes.begin (); ni != new_src_nodes.end (); ni++)
			{
				pt_node_index new_src_node = *ni;

				// Do not filter out an edge if it is in must node
				if (new_l == ASTERISK && must_lptr.find (new_src_node) != must_lptr.end ())
					continue;

				if (old_src_nodes.find (new_src_node) != old_src_nodes.end ())
				{
					RESULT ("\nFilter incl_in_edge %d->%d->%d", new_src_node, new_l, new_dest_node);
					incl_in_edges[new_dest_node][new_l].erase (new_src_node);
				}
			}
			if (!incl_in_edges[new_dest_node][new_l].size ())
				incl_in_edges[new_dest_node].erase (new_l);
		}
		if (!incl_in_edges[new_dest_node].size ())
			incl_in_edges.erase (new_dest_node);
	}

#else
	// Check whether an edge incl_out_edges already exists
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator oei;
	for (oei = incl_out_edges.begin (); oei != incl_out_edges.end (); oei++)
	{
		pt_node_index new_src_node = oei->first;
		map<label, set<pt_node_index> > out_edges = oei->second;
		map<label, set<pt_node_index> >::iterator ei;
		for (ei = out_edges.begin (); ei != out_edges.end (); ei++)
		{
			label new_l = ei->first;
			set<pt_node_index> new_dest_nodes = ei->second;

			// Do not filter out an edge if it is in must node
			if (new_l == ASTERISK && must_lptr.find (new_src_node) != must_lptr.end ())
				continue;

			set<pt_node_index> old_dest_nodes;
			get_out_nodes (new_src_node, new_l, old_dest_nodes, valid_nodes);
			if (!old_dest_nodes.size ())
				continue;
			
			set<pt_node_index>::iterator ni;
			for (ni = new_dest_nodes.begin (); ni != new_dest_nodes.end (); ni++)
			{
				pt_node_index new_dest_node = *ni;
				if (old_dest_nodes.find (new_dest_node) != old_dest_nodes.end ())
				{
					RESULT ("\nFilter incl_out_edge %d->%d->%d", new_src_node, new_l, new_dest_node);
					incl_out_edges[new_src_node][new_l].erase (new_dest_node);
				}
			}
			if (!incl_out_edges[new_src_node][new_l].size ())
				incl_out_edges[new_src_node].erase (new_l);
		}
		if (!incl_out_edges[new_src_node].size ())
			incl_out_edges.erase (new_src_node);
	}
#endif
}
#endif


/**
 * This function computes the destination nodes of Egen, Ekill, incl_in_edges.
 *
 */

set<pt_node_index> pt_fi_graph::
find_visit_nodes (set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<pt_node_index> & valid_nodes)
{
	FUNBEGIN ();

	set<pt_node_index> nvisit;

	// Add destination nodes of Egen
	// nvisit.insert (rpte.begin (), rpte.end ());
	merge_set (rpte, nvisit);
	// Add destination nodes of Ekill
	get_destination_nodes (must_lptr, l, nvisit, valid_nodes);

#if PULL_ACCESS_NAMES
	// Add destination nodes of invisible edges to be restored
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator inei;
	for (inei = incl_in_edges.begin (); inei != incl_in_edges.end (); inei++)
		nvisit.insert (inei->first);
#else
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator outei;
	for (outei = incl_out_edges.begin (); outei != incl_out_edges.end (); outei++)
	{
		map<label, set<pt_node_index> > outn_e = outei->second;
		map<label, set<pt_node_index> >::iterator outn_ei;
		for (outn_ei = outn_e.begin (); outn_ei != outn_e.end (); outn_ei++)
		{
			set<pt_node_index> outn = outn_ei->second;
			merge_set (outn, nvisit);
		}
	}
#endif

#if SUMM_K_CONSISTENT
	// Add nodes in lptr that are summary nodes
	set<pt_node_index>::iterator li;
	for (li = lptr.begin (); li != lptr.end (); li++)
	{
		pt_node_index lid = *li;
		pt_fi_node * ln = nodes[lid];
		if (ln->get_is_summary_node ())
			nvisit.insert (lid);
	}
#endif

#if DEBUG_CONTAINER
	DEBUG ("\nnvisit=");
	set<pt_node_index>::iterator vni;
	for (vni = nvisit.begin (); vni != nvisit.end (); vni++)
		DEBUG ("%d,", *vni);
#endif

	RETURN (nvisit);
	// return nvisit;
}

/**
 * Fetches node(s) pointed by VAR.
 */

void pt_fi_graph::
get_addressof_nodes (label var, set<pt_node_index> & addr_nodes)
{
	// Get &VAR
	stack.get_destination_nodes (var, stack.get_node_id (), addr_nodes);

#if DEBUG_CONTAINER
	set<pt_node_index>::iterator ni;
	DEBUG ("\nFetched addr nodes for var %d: ", var);
	for (ni = addr_nodes.begin (); ni != addr_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif
}

void pt_fi_graph::
generate_addressof_nodes (set<label> & vars,
	set<pt_node_index> & var_nodes)
{
	set<label>::iterator vi; 
	for (vi = vars.begin (); vi != vars.end (); vi++) 
	{ 
		// Create var node 
		label v = *vi; 
		DEBUG ("\ngenerate v=%d", v);
		set<pt_node_index> var_nodes_temp;
		generate_addressof_nodes (v, var_nodes_temp);
		// var_nodes.insert (var_nodes_temp.begin (), var_nodes_temp.end ());
		merge_set (var_nodes_temp, var_nodes);
	} 
}

/**
 * Fetches node(s) pointed by VAR.  Generates a node if such a node is not
 * already present.
 * input: VAR
 * output: ADDR_NODES (containing node corresponding to VAR)
 */

void pt_fi_graph::
generate_addressof_nodes (label var, set<pt_node_index> & addr_nodes)
{
	DEBUG ("\ngenerate_addressof_nodes (%d)", var);

#if UNDEF_LOCATION == 0
	if (var == undef_id)
		return;
#endif

#if NULL_LOCATION == 0
	if (var == null_id)
		return;
#endif

#if READONLY_LOCATION == 0
	if (var == readonly_id)
		return;
#endif

	set<pt_node_index> addr_nodes_temp;
	get_addressof_nodes (var, addr_nodes_temp);

	if (addr_nodes_temp.size ())
	{
		// addr_nodes.insert (addr_nodes_temp.begin (), addr_nodes_temp.end ());
		merge_set (addr_nodes_temp, addr_nodes);
		return;
	}

	pt_fi_node * addr_node = new pt_fi_node (nodes);
	pt_node_index addr_id = addr_node->get_node_id ();
	DEBUG ("\nInserting edge for var %d in stack node", var);
	pt_node_index stack_id = stack.get_node_id ();
	stack.insert_edge (var, *addr_node, stack_id);

	addr_nodes.insert (addr_id);

#if DEBUG_CONTAINER
	set<pt_node_index>::iterator ni;
	DEBUG ("\ngenerated addr node: ");
	for (ni = addr_nodes.begin (); ni != addr_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif

	// Connect V.FIELD to V via FIELD if V node exists here in the graph. 
	// Example: struct node1 { struct node1 * F1; struct node2 F2; }; 
	//	  struct node2 { int * F3; int * F4; }
	// If H is of node1 type, then following variables exist: H=H.F1,
	// H.F2=H.F2.F3, H.F2.F4. These variables are connected via NEXT.
	// However, we need to connect node H to H.F2.F3 via 32 and H to
	// H.F2.F4 via 64; here NEXT has no role to play. Illustrated below.
	// (a) p1=&H; p1->F2.F3=&p2; Statement 2 has offset 32 from p1. Node
	//     p1->F2.F3 (= H.F2.F3) can be reached from p1 via 32 (F2) + 0 (F3).
	//     Therefore, a connection from H to H.F2.F3 via 32 should exist.
	// (b) p1=&H; p1->F2.F4=&p2; Statement 2 has offset 32+32 from p1. Node
	//     p1->F2.F4 (= H.F2.F4) can be reached from p1 via 32 (F2) + 32 (F4).
	//     Therefore, a connection from H to H.F2.F4 via 64 (=32+32) should
	//     also exist.

	generate_addressof_field_nodes (var, addr_nodes);
}

void pt_fi_graph::
generate_fresh_addressof_nodes (label var, set<pt_node_index> & addr_nodes)
{
	// For malloc() (i.e. say &heap.5) on rhsi (var) also, this function
	// fetches all already existing heap.5 nodes. We do not create a new
	// heap.5 everytime. Otherwise we would end up generating too many
	// unused heap.5.
	generate_addressof_nodes (var, addr_nodes);

	// If var is heap (i.e. malloc()), find the node in addr_nodes from
	// g_pt.fresh_named_nodes i.e. node that has not been pointed by any
	// stack node.
	if (!program.heap_var (var))
	{
		RESULT ("\nError: generate_fresh_addressof_nodes(var=%d) called for non-heap", var);
		return;
	}

	pt_node_index fresh_heap_nid = 0;
	set<pt_node_index>::iterator ri;
	for (ri = addr_nodes.begin (); ri != addr_nodes.end (); ri++)
	{
		if (is_fresh_heap_node (*ri))
		{
			fresh_heap_nid = *ri;
			addr_nodes.clear ();
			addr_nodes.insert (fresh_heap_nid);
			return;
		}
	}

	if (!fresh_heap_nid)
		RESULT ("\nError: Fresh heap=%d not found", var);
}

/**
 * Given VAR whose nodes are in ADDR_NODES, this function generates all
 * (recursively nested) field nodes inside structure VAR and connects them
 * via field offset difference.
 * input: VAR, ADDR_NODES
 * output: 0
 */

void pt_fi_graph::
generate_addressof_field_nodes (label var, set<pt_node_index> & addr_nodes)
{
	csvarinfo_t var_info = VEC_index (csvarinfo_t, program.variable_data, var);
	// Return if var has no fields.
	if (!var_info->offset && !var_info->next)
		return;
	// Return if var is function. (NEXT field of function csvarinfo_t
	// is connected to its function parameter).
	if (program.function_var (var_info))
		return;
	// Return if var is function parameter. (OFFSET field of parameter
	// csvarinfo_t is set to the position of the parameter with respect to
	// other parameters).
	if (program.parameter_var (var_info))
		return;

	// Generate field nodes nested inside VAR and connect them with an edge
	// labeled with offset difference. 
	insert_field_edges (addr_nodes, var_info);

	// Generate the root variable, which has 0 offset. This will
	// recursively generate and connect all field nodes of this var.
	// This is redundant if VAR is already at offset 0 but not otherwise.
	if (!var_info->decl)
	{
		RESULT ("\n!var_info->decl");
		return;
	}
	// If original_root of this field has been typecasted, then
	// cs_lookup_vi_for_tree() returns the typecasted root. Therefore, we
	// need to call insert_field_edges() from the original_root too. This
	// has been done in generate_heap_field_nodes().
	csvarinfo_t var_root = program.cs_lookup_vi_for_tree (var_info->decl);
	if (!var_root)
	{
		// This is not an error. For example, main.varags does not have
		// var_root.
		DEBUG ("\n!var_root id=%s(%d)", var_info->name, var_info->id);
		return;
	}
	DEBUG ("\nvar=%s(%d), var_root=%s(%d)", var_info->name, var_info->id, 
		var_root->name, var_root->id);
	set<pt_node_index> var_root_nodes;
	generate_addressof_nodes (var_root->id, var_root_nodes);

	// If var_root is a heap node and its field nodes have been created
	// on-the-fly in this function, then var_root_nodes (0 offset variable)
	// was already in existence; in which case field edges from var_root do
	// not get created by generate_addressof_nodes() because the function
	// returns from get_addressof_nodes() itself. Create them here.
	if (var_root->is_heap_var)
	{
		// There may be more than one var_root_nodes. All need to be
		// connected to the field nodes.
		insert_field_edges (var_root_nodes, var_root);
		// If there are more than one var_root_nodes, then we should
		// generate as many field nodes as are the number of
		// var_root_nodes.
		if (var_root_nodes.size () > 1)
			RESULT ("\nError:? Approximation with field nodes of %s(%d)",
				var_root->name, var_root->id);
	}
}

/**
 * This function fetches nodes pointed by VAR.*.FIELD.
 *
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: pointer_nodes
 * @returns true if the destination node needs to be added to THIS graph.
 */

bool pt_fi_graph::
get_pointer_nodes (label var, list<label> * field_sequence, set<pt_node_index> & pointer_nodes,
	set<pt_node_index> & value_excl_out_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	FUNBEGIN ();

	DEBUG ("\nget_pointer_nodes()");

	// Get VAR
	set<pt_node_index> addr_nodes;
	get_addressof_nodes (var, addr_nodes);

	// Get VAR.*
	set<pt_node_index> dest_nodes;
	bool new_node_needed = get_destination_nodes (addr_nodes, ASTERISK, dest_nodes,
		value_excl_out_edges, incl_in_edges, incl_out_edges);
	DEBUG ("\ndest_nodes.size()=%d", dest_nodes.size ());

	// Get VAR.*.FIELD
	if (!field_sequence)
	{
		pointer_nodes = dest_nodes;
		RETURN (new_node_needed);
		// return new_node_needed;
	}

	csvarinfo_t var_info = VEC_index (csvarinfo_t, program.variable_data, var);
	list<label>::iterator fi;
	for (fi = field_sequence->begin (); fi != field_sequence->end (); fi++)
	{
		DEBUG ("\nField %d", *fi);
		pointer_nodes.clear ();
		// VAR_INFO->decl passed to typecast dest_nodes to the type
		// used in the statement.
		get_field_nodes (dest_nodes, var_info->decl, *fi, pointer_nodes,
			value_excl_out_edges, incl_in_edges, incl_out_edges);
		// get_field_nodes() fetches VAR.*.FIELD nodes if found, else
		// leaves VAR.* in DEST_NODES
		new_node_needed |= dest_nodes.size ();
		dest_nodes = pointer_nodes;
	}
	DEBUG ("\npointer_nodes.size()=%d", pointer_nodes.size ());
	DEBUG ("\ndone get_pointer_nodes()");

	RETURN (new_node_needed);
	// return new_node_needed;
}

/**
 * Fetches nodes pointed by VAR.*.FIELD.*. 
 * 
 * @returns true if the destination is undef and UNDEF node does not exist in
 * THIS graph.
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: destination_nodes
 */

bool pt_fi_graph::
get_deref_nodes (label var, list<label> * field_sequence, set<pt_node_index> & destination_nodes,
	set<pt_node_index> & value_excl_out_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	FUNBEGIN ();

	DEBUG ("\nget_deref_nodes (%d)", var);
	set<pt_node_index> pointer_nodes;
	set<pt_node_index> heap_nodes;

	// Get VAR.*.FIELD nodes in POINTER_NODES.
	// If new_node_needed is true, then either UNDEF node is missing or
	// V.FIELD node is missing. In both cases, the destination of
	// get_deref_nodes() is undef.
	bool new_node_needed = get_pointer_nodes (var, field_sequence, pointer_nodes,
		value_excl_out_edges, incl_in_edges, incl_out_edges);

	// Get VAR.*.FIELD.* from POINTER_NODES 
	// If out_edge_missing is true, then the destination of
	// get_deref_nodes() is undef.
	bool out_edge_missing = get_destination_nodes (pointer_nodes, ASTERISK, destination_nodes,
		value_excl_out_edges, incl_in_edges, incl_out_edges);

#if UNDEF_LOCATION
	if (new_node_needed || out_edge_missing)
	{
		set<pt_node_index> undef_nodes;
		get_addressof_nodes (undef_id, undef_nodes);
		// destination_nodes.insert (undef_nodes.begin (), undef_nodes.end ());
		merge_set (undef_nodes, destination_nodes);
		if (undef_nodes.size ())
			RETURN (false);
			// return false;
	}
#endif
	RETURN (true);
	// return true;
}

/**
 * Fetches nodes pointed by VAR.*.FIELD.*. If the destination is undef and
 * an UNDEF node is missing, this function generates an UNDEF node.
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: destination_nodes
 */

void pt_fi_graph::
generate_deref_nodes (label var, list<label> * field_sequence, set<pt_node_index> & destination_nodes,
	set<pt_node_index> & value_excl_out_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	FUNBEGIN ();

	DEBUG ("\ngenerate_deref_nodes (%d)", var);
	bool new_undef_node_needed = 
		get_deref_nodes (var, field_sequence, destination_nodes,
			value_excl_out_edges, incl_in_edges, incl_out_edges);
#if UNDEF_LOCATION
	if (new_undef_node_needed)
		generate_addressof_nodes (undef_id, destination_nodes);
#endif

	RETURN_VOID ();
}


/**
 * Fetches nodes that are must pointed by VAR.*.FIELD.
 *
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: destination_nodes 
 */

void pt_fi_graph::
get_must_pointer_nodes (label var, 
	list<label> * field_sequence, 
	set<pt_node_index> & destination_nodes,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<pt_node_index> & valid_nodes)
{
	FUNBEGIN ();

	DEBUG ("\nget_must_pointer_nodes (%d.offset)", var);
	// Get VAR
	set<pt_node_index> addr_nodes;
	get_addressof_nodes (var, addr_nodes);
#if DEBUG_CONTAINER
	set<pt_node_index>::iterator ni;
	DEBUG ("\naddr_nodes=");
	for (ni = addr_nodes.begin (); ni != addr_nodes.end (); ni++)
		DEBUG ("%d,", *ni); 
#endif

	// Get VAR.*
	set<pt_node_index> dest_nodes;
	get_destination_nodes (addr_nodes, ASTERISK, dest_nodes, valid_nodes,
		value_excl_out_edges, incl_in_edges, incl_out_edges);

#if DEBUG_CONTAINER
	DEBUG ("\ndest_nodes=");
	for (ni = dest_nodes.begin (); ni != dest_nodes.end (); ni++)
		DEBUG ("%d,", *ni); 
#endif

	// Find nodes that have must points-to relation with VAR.*.
	// Here if all the DEST_NODES have the same non-heap name, then the
	// relation is must. 
	set<label> dest_nodes_names;
	get_nodes_names (dest_nodes, dest_nodes_names);
#if DEBUG_CONTAINER
	set<label>::iterator li;
	DEBUG ("\ndest_node_names=");
	for (li = dest_nodes_names.begin (); li != dest_nodes_names.end (); li++)
		DEBUG ("%d,", *li); 
#endif

	// If there are more than one names. 
	if (dest_nodes_names.size () != 1)
		RETURN_VOID ();
		// return;

	// Get the only destination node name
	label v = *(dest_nodes_names.begin ());

	// If the destination is undef
	if (v == undef_id)
		RETURN_VOID ();
		// return;

#if SUMM_K_CONSISTENT
	if (v == wild_card_id)
		RETURN_VOID ();
		// return;
#endif

	// Return empty FIELD_NODES if the only name in DEST_NODES_NAMES is a
	// heap name.
	csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, v);
	if (v_info->is_heap_var)
		RETURN_VOID ();
		// return;

	// Get all nodes with the name DEST_NODES_NAMES. Do not use the
	// DEST_NODES produced above. This is required in access-based
	// abstraction where more than one nodes have the same name.
	dest_nodes.clear ();
	get_addressof_nodes (v, dest_nodes);
#if DEBUG_CONTAINER
	DEBUG ("\ndest_nodes 2=");
	for (ni = dest_nodes.begin (); ni != dest_nodes.end (); ni++)
		DEBUG ("%d,", *ni); 
#endif

	if (!field_sequence)
	{
		destination_nodes = dest_nodes;
		return;
	}

	// Get VAR.*.FIELD nodes. 
	csvarinfo_t var_info = VEC_index (csvarinfo_t, program.variable_data, var);
	set<pt_node_index> field_nodes;
	bool new_node_needed = false;
	list<label>::iterator fi;
	for (fi = field_sequence->begin (); fi != field_sequence->end (); fi++)
	{
		field_nodes.clear ();
		// VAR_INFO->decl passed to typecast dest_nodes to the type
		// used in the statement. Although for this function,
		// dest_nodes are all stack variables (not heap); therefore
		// dest_nodes would already be in TREE_TYPE(VAR_INFO->decl)
		// type.
		get_field_nodes (dest_nodes, var_info->decl, *fi, field_nodes,
			value_excl_out_edges, incl_in_edges, incl_out_edges);
		pt_fi_node::get_nodes_valid_at_point (field_nodes, valid_nodes);
		new_node_needed |= dest_nodes.size ();
		// If the destination is undef
		if (new_node_needed)
			return;

		// FIXME: Since connection with field_nodes is created by
		// struct definitions of the program, there can never be two
		// names or undef FIELD_NODES. Either remove the following
		// checks or at least move them outside this loop.

		// Find nodes that have must points-to relation with
		// VAR.*.FIELD.  Here if all the FIELD_NODES have the same
		// name (which will obviously be non-heap), then the relation
		// is must.
		set<label> field_nodes_names;
		get_nodes_names (field_nodes, field_nodes_names);
		// If there are more than one names.
		if (field_nodes_names.size () != 1)
			RETURN_VOID ();
			// return;

		// Get the only destination node name
		v = *(field_nodes_names.begin ());

		// If the destination is undef
		if (v == undef_id)
			RETURN_VOID ();
			// return;

#if SUMM_K_CONSISTENT
		if (v == wild_card_id)
			RETURN_VOID ();
			// return;
#endif

		dest_nodes = field_nodes;
	}

	destination_nodes = field_nodes;
		
	RETURN_VOID ();
}

/**
 * Note that this function leaves in SRC_NIDS only those remaining nodes which
 * do not have an out-edge labeled FIELD and whose corresponding V.FIELD node
 * is not found.
 *
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: field_nodes 
 */

void pt_fi_graph::
get_field_nodes (set<pt_node_index> & src_nids, 
	label field, 
	set<pt_node_index> & field_nodes,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	DEBUG ("\nget_field_nodes() of field %d", field);

	set<pt_node_index>::iterator ni;
	for (ni = src_nids.begin (); ni != src_nids.end (); )
	{
		DEBUG ("\nNode %d", *ni);
		if (get_field_nodes (*ni, field, field_nodes,
			value_excl_out_edges, incl_in_edges, incl_out_edges))
			src_nids.erase (ni++);
		else
			ni++;
	}

#if DEBUG_CONTAINER
	DEBUG ("\nget_field_nodes() with field %d: ", field);
	for (ni = field_nodes.begin (); ni != field_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif
}
 /**
 * Note that this function leaves in SRC_NIDS only those remaining nodes which
 * do not have an out-edge labeled FIELD and whose corresponding V.FIELD node
 * is not found.
 *
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: field_nodes 
 */

void pt_fi_graph::
get_field_nodes (set<pt_node_index> & src_nids, 
	tree src_pointer_type,
	label field, 
	set<pt_node_index> & field_nodes,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	DEBUG ("\nget_field_nodes() of field %d", field);
 
	set<pt_node_index>::iterator ni;
	for (ni = src_nids.begin (); ni != src_nids.end (); )
	{
		DEBUG ("\nNode %d", *ni);
		if (get_field_nodes (*ni, src_pointer_type, field, field_nodes,
			value_excl_out_edges, incl_in_edges, incl_out_edges))
			src_nids.erase (ni++);
		else
			ni++;
	}
 
#if DEBUG_CONTAINER
	DEBUG ("\nget_field_nodes() with field %d: ", field);
	for (ni = field_nodes.begin (); ni != field_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif
}

/**
 * This function generates the out-nodes via FIELD from every node in SRC_NIDS.
 *
 * output: field_nodes
 * output: incl_in_field_edges: new field edges from heap_nid to the field
 * nodes of its typecasted type (stored in the form of in-edges).
 */

void pt_fi_graph::
generate_field_nodes (set<pt_node_index> & src_nids, 
	tree src_pointer_type, 
	label field, 
	set<pt_node_index> & field_nodes,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_field_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_field_edges)
{
	DEBUG ("\ngenerate_field_nodes() of field %d", field);

	set<pt_node_index>::iterator ni;
	for (ni = src_nids.begin (); ni != src_nids.end (); ni++)
	{
		pt_node_index src_nid = *ni;
		DEBUG ("\nNode %d", src_nid);

		generate_field_nodes (src_nid, src_pointer_type, field, 
			field_nodes, incl_in_field_edges, incl_out_field_edges);
	}

#if DEBUG_CONTAINER
	DEBUG ("\ngenerate_field_nodes() with field %d: ", field);
	for (ni = field_nodes.begin (); ni != field_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif
}

/**
 * This function fetches the out-nodes via FIELD from SRC_NID.  It is more
 * than what GET_DESTINATION_NODES() does, in the sense that it additionally
 * deals with heap and UNDEF nodes in a special way if they do not have an
 * out-edge labeled FIELD. 
 *
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: field_nodes
 * @returns false if out-edge labeled FIELD does not exist or if corresponding
 * V.FIELD node is not found.
 */

bool pt_fi_graph::
get_field_nodes (pt_node_index src_nid, 
	label field, 
	set<pt_node_index> & field_nodes,
	set<pt_node_index> & value_excl_out_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	DEBUG ("\nget_field_nodes(src_nid=%d,field=%d)", src_nid, field);

	DEBUG ("\nNode %d", src_nid);
	pt_node_index stack_id = stack.get_node_id ();
	pt_fi_node * srcn = nodes[src_nid];
	if (!srcn)
	{
		RESULT ("\nError: srcn for src_nid=%d not found", src_nid);
		return false;
	}
	label src_name = srcn->get_node_name (stack_id);

	// SRC_NID is undef/null/readonly. 
	// Note that FIELD is absent in x=y statements. Here y could be
	// pointing to NULL and get_field_nodes() is called on NULL
	// node with FIELD=0.  Precisely, we should add NULL node to
	// FIELD_NODES in such a case; but we cannot differentiate
	// between x=y and x=&(y->f).  Therefore, for a safe analysis,
	// we assume it is x=&(y->f) and we add UNDEF to FIELD_NODES.
	// FIXME: Use types or field_sequence to find if rhs is y or &(y->f).

	// SUMM_K_CONSISTENT: node with is_summary_node has
	// node_name=wild_card_id which is representing a var and does not
	/// pass the following if-condition.

	if (!program.is_repr_var (src_name))
	{
		DEBUG ("\nNode %d being dereferenced", src_nid);
#if UNDEF_LOCATION
		set<pt_node_index> undef_nodes;
		get_addressof_nodes (undef_id, undef_nodes);
		// field_nodes.insert (undef_nodes.begin (), undef_nodes.end ());
		merge_set (undef_nodes, field_nodes);
		if (undef_nodes.size ())
			return true;
#endif
		return false;

		//#else
		// If there is no UNDEF node, then this is a
		// may-points-to analysis and we can safely say that
		// null is the pointee.
		//set<pt_node_index> null_nodes;
		//get_addressof_nodes (null_id, null_nodes);
		//field_nodes.insert (null_nodes.begin (), null_nodes.end ());
		//if (null_nodes.size ())
		//	return true;
		//return false;
		//#endif
	}

	// If FIELD is the first member of SRC_NID, then SRC_NID itself is
	// added to FIELD_NODES.
	if (!field)
	{
		DEBUG ("\nField %d == 0", field);
		field_nodes.insert (src_nid);
		return true;
	}

	// If FIELD is a subsequent member of SRC_NID, then check if out-node
	// via FIELD already exists.
	set<pt_node_index> out_nodes;
	srcn->get_destination_nodes (field, stack_id, out_nodes,
		value_excl_out_edges, incl_in_edges, incl_out_edges);
	if (!out_nodes.size ())
	{
		// V may or may not be connected to V.FIELD. Therefore, in addition to
		// finding connected V.FIELD (as done above), return false in order to
		// connect V to V.FIELD nodes. The need is demonstrated in test31g.c
		return false;
	}

	// For field/=0,
	// From out_nodes, extract only those field nodes that are
	// fields of the required type (i.e. decl of src_name is same as decl
	// of root to which the field belongs).

	csvarinfo_t src_info = VEC_index (csvarinfo_t, program.variable_data, src_name);
	csvarinfo_t required_field_info = program.cs_first_vi_for_offset (src_info, field);
	if (!required_field_info)
	{
		if (src_info->is_heap_var)
		{
			RESULT ("\nError: required_field_info for src_name=%d,field=%d not found", src_name, field);
		}
		// This may not be error: Actually in static analysis VAR may be
	        // wrongly made to point to a different type of heap which should not
	        // be typecasted, or VAR may be pointing to heap.n.64+64 (field heap
	        // node) but field typecasting has not been handled.
		else
		{
			RESULT ("\nError:! required_field_info for src_name=%d,field=%d not found", src_name, field);
		}
		RESULT ("\nFields of src_name=%s(%d)=", src_info->name, src_info->id);
		csvarinfo_t temp;
		for (temp = src_info->next; temp; temp = temp->next)
			RESULT ("%s(%d),", temp->name, temp->id);

		print_node (dump_file, 0, src_info->decl, 0); 
		return false;
	}
	bool matching_field_found = false;
	set<pt_node_index>::iterator fi;
	for (fi = out_nodes.begin (); fi != out_nodes.end (); fi++)
	{
		pt_node_index fid = *fi;
		DEBUG ("\nOut-nodes from node %d via field %d via field=%d", src_nid, field, fid);
		pt_fi_node * fnode = nodes[fid];
		if (!fnode)
		{
			RESULT ("\nError: fnode for fid=%d not found", fid);
			continue;
		}
		label field_id = fnode->get_node_name (stack_id);
		DEBUG ("\nout-node pt-id=%d,var-id=%d", fid, field_id);
		if (field_id == required_field_info->id)
		{
			field_nodes.insert (fid);
			matching_field_found = true;
			DEBUG ("\nout-node pt-id=%d,var-id=%d matches out-field type", fid, field_id);
		}
	}
	return matching_field_found;
}

/**
 * This function sets the typecasted type in decl of src_nid and then fetches
 * the out-nodes via FIELD (of typecasted type) from SRC_NID.
 *
 * Note that misc/parser::generate_heap_field_vars() fetches dest vars
 * connected via field from src vars of src_pointer_type in
 * parser::variable_data. However, we want to fetch only those dest nodes that
 * are connected via field edge from src_nids of src_pointer_type in gPT.
 * Therefore, generate_heap_field_vars() is called before calling
 * get_field_nodes(). 
 *
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: field_nodes
 */

bool pt_fi_graph::
get_field_nodes (pt_node_index src_nid, 
	tree src_pointer_type, 
	label field, 
	set<pt_node_index> & field_nodes,
	set<pt_node_index> & value_excl_out_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	pt_node_index stack_id = stack.get_node_id ();
	pt_fi_node * srcn = nodes[src_nid];
	if (!srcn)
	{
		RESULT ("\nError: srcn for src_nid=%d not found", src_nid);
		return false;
	}
	label src_name = srcn->get_node_name (stack_id);

	// This changes the decl type of src_name to
	// TREE_TYPE(src_pointer_type) -- if non-null heap. Else retains the
	// original type.
	csvarinfo_t field_info = NULL;
	if (program.heap_var (src_name))
	{
		field_info = program.generate_heap_field_vars (src_name, src_pointer_type, field);
		if (!field_info)
		{
			RESULT ("\nError: field_info for pt=%d,src_name=%d,field=%d not found", 
				src_nid, src_name, field);
			return false;
		}
	}

	// Get the field nodes connected from the original src node.  If
	// original src/heap node was already connected to typecasted field
	// node, return the desired typecasted field node. No need to pass the
	// typecasted type since now the type of original heap (heap_nid) has
	// been transformed to the typecasted type.
	return get_field_nodes (src_nid, field, field_nodes,
		value_excl_out_edges, incl_in_edges, incl_out_edges);
}

/**
 * This function generates the out-nodes via FIELD from SRC_NID. It does not
 * call get_field_nodes() because it assumes that has already been done.
 *
 * Note that misc/parser::generate_heap_field_vars() fetches dest vars
 * connected via field from src vars of src_pointer_type in
 * parser::variable_data. However, we want to fetch only those dest nodes that
 * are connected via field edge from src_nids of src_pointer_type in gPT.
 * Therefore, generate_heap_field_vars() is called before calling
 * get_field_nodes(). 
 *
 * output: field_nodes
 * output: gen_incl_in_field_edges: new field edges from src_nid to the field
 * nodes of its typecasted type (stored in the form of in-edges).
 */

void pt_fi_graph::
generate_field_nodes (pt_node_index src_nid, 
	tree src_pointer_type, 
	label field, 
	set<pt_node_index> & field_nodes,
	map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_in_field_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_out_field_edges)
{
	DEBUG ("\ngenerate_field_nodes(src_nid=%d, field=%d)", src_nid, field);

	pt_node_index stack_id = stack.get_node_id ();
	pt_fi_node * srcn = nodes[src_nid];
	if (!srcn)
	{
		RESULT ("\nError: srcn for src_nid=%d not found", src_nid);
		return;
	}
	label src_name = srcn->get_node_name (stack_id);

	// This changes the decl type of src_name to
	// TREE_TYPE(src_pointer_type) -- if non-null heap. Else retains the
	// original type.
	csvarinfo_t field_info = NULL;
	if (program.heap_var (src_name))
	{
		field_info = program.generate_heap_field_vars (src_name, src_pointer_type, field);
		if (!field_info)
		{
			RESULT ("\nError: field_info for pt=%d,src_name=%d,field=%d not found", 
				src_nid, src_name, field);
			return;
		}
	}

	// Get the field nodes connected from the original src node.  If
	// original src/heap node was already connected to typecasted field
	// node, return the desired typecasted field node. No need to pass the
	// typecasted type since now the type of original heap (heap_nid) has
	// been transformed to the typecasted type.

	// if (get_field_nodes (src_nid, field, field_nodes))
	//	return;

	if (!field)
	{
		RESULT ("\nError: Field=0 of src_nid=%d is not found", src_nid);
		return;
	}

	// Generate out-nodes via FIELD from src_nid.

	// Node in set SRC_NIDS is undef/null/readonly. 
	// Note that FIELD is absent in x=y statements. Here y could be
	// pointing to NULL and get_field_nodes() is called on NULL node with
	// FIELD=0.  Precisely, we should add NULL node to FIELD_NODES in such
	// a case; but we cannot differentiate between x=y and x=&(y->f).
	// Therefore, for a safe analysis, we assume it is x=&(y->f) and we add
	// UNDEF to FIELD_NODES.
	// FIXME: Use types to find if rhs is y or &(y->f).

	// SUMM_K_CONSISTENT: node with is_summary_node has
	// node_name=wild_card_id which is representing a var and does not pass
	// the following if-condition.

	if (!program.is_repr_var (src_name))
	{
		DEBUG ("\nNode %d is being dereferenced", src_nid);
#if UNDEF_LOCATION
		generate_addressof_nodes (undef_id, field_nodes);
		//#else
		// If there is no UNDEF node, then this is a may-points-to
		// analysis and we can safely say that null is the pointee.
		// generate_addressof_nodes (null_id, field_nodes);
#endif

		return;
	}

	// If V_INFO is a stack, then field nodes already exist and will get
	// found by get_field_nodes() via get_destination_nodes(); therefore,
	// continue to the loop.
	#if SUMM_K_CONSISTENT
	if (!srcn->get_is_summary_node ())
	#endif

	if (!program.heap_var (src_name))
	{
		// This may not be an error if our static analysis makes wrong pointers.
		RESULT ("\nError:! Field of stack id=%d should have already been found", src_name);
		return;
	}

	// HEAP

	#if SUMM_K_CONSISTENT
	// A field is generated either on fresh nodes or on on-the-fly heap
	// nodes.  The former cannot be summary nodes (as they are pointed only
	// by stack_id node or via field edges (which do not increase value of
	// K)).  The latter could be summary nodes. This function generates H.F
	// in HEAP_FIELD_NODES. If H is a summary node, then H.F is not
	// connected by H. This could lead to unsafe results when H.F remains
	// unaliased with its H but is added to rhs nodes and forms alias with
	// lhs.  Therefore, we simply add wild_card_id edge on HEAP_NODE_ID as
	// the HEAP_FIELD_NODE.
	// FIXME: It should also be checked that N is not in SUMM_CMPTS i.e. a
	// newly created summary node.
	
	if (srcn->get_is_summary_node ())
	{
		srcn->insert_edge (wild_card_id, *srcn, stack_id);
		field_nodes.insert (src_nid);
		return;
	}
	#endif

	// Note field_nodes may not be empty here due to already existing nodes
	// in field_nodes when this function was called.

	#if DEBUG_CONTAINER
	csvarinfo_t src_info = VEC_index (csvarinfo_t, program.variable_data, src_name);
	DEBUG ("\nHeap node %d, name: %s(%d)", src_nid, src_info->name, src_info->id);
	DEBUG ("\nGenerate heap at offset %d from heap node %s", field, src_info->name);
	#endif

	// HEAP_NID has already been typecasted to the required type and it does
	// not have a field edge to FIELD_INFO. Now create node FIELD_INFO and
	// field edges from H to field nodes of root decl of FIELD_INFO in
	// NEW_IN_FIELD_EDGES.

	generate_heap_field_nodes (src_nid, field_info, field, gen_incl_in_field_edges, gen_incl_out_field_edges);
}

/**
 * This function is called when HEAP_NID has already been typecasted to the
 * require type and it does not have a field edge to FIELD_INFO. This function
 * creates node FIELD_INFO and field edges from H to field nodes of root decl
 * of FIELD_INFO.
 *
 * output: gen_incl_in_field_edges: new field edges from heap_nid to the field
 * nodes of FIELD_INFO->decl (here field_edges are stored in the form of
 * in-edges).
 */

void pt_fi_graph::
generate_heap_field_nodes (pt_node_index heap_nid, 
	csvarinfo_t field_info,
	label field, 
	map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_in_field_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_out_field_edges)
{
	DEBUG ("\ngenerate_heap_field_nodes(heap_nid=%d, field=%d)", heap_nid, field);

	if (!field)
	{
		RESULT ("\nError: Field=0 of heap_nid=%d is not found", heap_nid);
		return;
	}
	if (!field_info)
	{
		RESULT ("\nError: field_info for heap_nid=%d,field=%d is NULL", heap_nid, field);
		return;
	}
	if (!field_info->decl)
	{
		RESULT ("\nError: field_info->decl for heap_nid=%d,field=%d is NULL", heap_nid, field);
		return;
	}

	// Here field/=0,	
	// field_info is the typecasted heap and not original_root
	// (original heap). In generate_addressof_nodes(), field edges are
	// created on typecasted heap when cs_lookup_vi_for_tree() is called
	// (which returns the typecasted heap). Here field edges are not
	// created on the original heap. 

	// unsigned int old_max_node_id = get_max_node_id ();
	// Do not store in heap_field_nodes from the call to
	// generate_addressof_nodes() because we want to store only those field
	// nodes that are connected via gpt field edge from original heap node.
	set<pt_node_index> heap_field_nodes_temp;
	// The fresh on-the-fly field node is attached to the fresh root node
	// in the following function.
	generate_addressof_nodes (field_info->id, heap_field_nodes_temp);
	// unsigned int new_max_node_id = get_max_node_id ();

	// The following creates edges from fresh original_heap node to freshly
	// created field nodes. Do NOT do this. Otherwise, unnecesary
	// typecasted fields are generated whenever the fresh original_heap
	// node is used.

	//if (old_max_node_id < new_max_node_id)
	//{
	//	set<pt_node_index> original_fresh_root_nodes;
	//	pt_node_index stack_id = stack.get_node_id ();
	//	pt_fi_node * srcn = nodes[heap_nid];
	//	if (!srcn)
	//	{
	//		RESULT ("\nError: srcn for heap_nid=%d not found", heap_nid);
	//		return;
	//	}
	//	label heap_var = srcn->get_node_name (stack_id);
        //	csvarinfo_t original_root = VEC_index (csvarinfo_t, program.variable_data, heap_var);
	//	if (!original_root)
	//	{
	//		RESULT ("\nError: original_root for heap_var=%d not found", heap_var);
	//		return;
	//	}
	//	generate_fresh_addressof_nodes (original_root->id, original_fresh_root_nodes);

	//	if (original_fresh_root_nodes.size () != 1)
	//	{
	//		RESULT ("\nError: There can be only one fresh node for %s(%d)",
	//			original_root->name, original_root->id);
	//	}

	//	// The field nodes of typecasted type in original_root->decl
	//	// are referred.
	//	insert_field_edges (original_fresh_root_nodes, original_root);
	//}

	// We need to connect the original heap root node with the clones of
	// fresh on-the-fly (typecasted) field nodes (i.e. fields of
	// field_info->decl). Note that here CLONES should be used. This is
	// important because the APs reaching the fresh field nodes and their
	// clones are different.  Otherwise, we will end up generating at each
	// program point the on-the-fly field nodes (attached to original root
	// heap with program point specific APs).
	// This produces spurious alias APs at each program point -- test20.c
	// generates APs with x.7(25) due to its reachability to on-the-fly
	// heap.T2.64 etc.

	// In order to keep fresh on-the-fly field nodes separate from those
	// for original root, we compute the new-field-edges and pass them to
	// clone_and_update_subgraph() which clones the fresh on-the-fly field
	// nodes. Until then we do not have the desired typecasted fresh field
	// node attached to original root node.

	compute_new_field_edges (heap_nid, field_info->decl, gen_incl_in_field_edges, gen_incl_out_field_edges);
}

/**
 * This function fetches all the field nodes reachable (recursively) from
 * src_nid that have the same type as the typecasted type of src_nid.
 *
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: field_nodes 
 */

void pt_fi_graph::
get_field_nodes (pt_node_index src_nid,
	set<pt_node_index> & field_nodes,
	set<pt_node_index> & value_excl_out_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	pt_node_index stack_id = stack.get_node_id ();
	pt_fi_node * srcn = nodes[src_nid];
	if (!srcn)
	{
		RESULT ("\nError: srcn for src_nid=%d not found", src_nid);
		return;
	}
	label src_name = srcn->get_node_name (stack_id);
	csvarinfo_t src_info = VEC_index (csvarinfo_t, program.variable_data, src_name);
	DEBUG ("\nget_field_nodes(src_nid=%s(%d))", src_info->name, src_nid);

	// Find immediate field labels of src_info->decl (typecasted type)
	set<unsigned int> field_varids;
	program.get_reachable_fields (src_info, field_varids);
	set<unsigned int>::iterator fvi;
#if DEBUG_CONTAINER
	DEBUG ("\nfields=");
	for (fvi = field_varids.begin (); fvi != field_varids.end (); fvi++)
	{
		unsigned int fvid = *fvi;
		csvarinfo_t linfo = VEC_index (csvarinfo_t, program.variable_data, fvid);
		label l = linfo->offset;
		DEBUG ("%d,", l);
	}
#endif
	for (fvi = field_varids.begin (); fvi != field_varids.end (); fvi++)
	{
		unsigned int fvid = *fvi;
		csvarinfo_t linfo = VEC_index (csvarinfo_t, program.variable_data, fvid);
		// linfo->offset is offset from base and not from src_info,
		// which may be non-zero.
		label l = linfo->offset - src_info->offset;
		DEBUG ("\nfield_var=%s(%d), offset=%d", linfo->name, linfo->id, l);

		// Field=0 corresponds to src_nid
		if (!l)
			continue;

		set<pt_node_index> field_nodes_temp;

		// Find fields of source node
		get_field_nodes (src_nid, l, field_nodes_temp,
			value_excl_out_edges, incl_in_edges, incl_out_edges);
		if (field_nodes_temp.size () != 1)
		{
			RESULT ("\nError: Fresh node's clone=src_nid=%s(%d) has field_nodes.size=%d (!=1) for field=%d",
				src_info->name, src_nid, field_nodes_temp.size (), l);
			set<pt_node_index>::iterator si;
			RESULT ("\nError: Field nodes of src=%s(%d) for field=%d=", 
				src_info->name, src_info->id, l);
			for (si = field_nodes_temp.begin (); si != field_nodes_temp.end (); si++)
				RESULT ("%d,", *si);
			
		}
		// field_nodes.insert (field_nodes_temp.begin (), field_nodes_temp.end ());
		merge_set (field_nodes_temp, field_nodes);

		// Find fields of fields
		set<pt_node_index>::iterator si;
#if DEBUG_CONTAINER
		DEBUG ("\nField nodes of src=%s(%d)=", src_info->name, src_info->id);
		for (si = field_nodes_temp.begin (); si != field_nodes_temp.end (); si++)
			DEBUG ("%d,", *si);
#endif
		for (si = field_nodes_temp.begin (); si != field_nodes_temp.end (); si++)
		{
			pt_node_index sfnid = *si;
			get_field_nodes (sfnid, field_nodes,
				value_excl_out_edges, incl_in_edges, incl_out_edges);
		}
	}
}

/**
 * Given a heap node HEAP_NODE_ID which has been typecasted to HEAP_DECL, this
 * function computes NEW_IN_FIELD_EDGES which is the new field edges from
 * HEAP_NODE_ID to fresh field nodes of HEAP_DECL (edges are stored in the form
 * of in-field-edges).
 * This function is called only when HEAP_NODE_ID does not already have gpt
 * field edges to field nodes of HEAP_DECL type.
 */

void pt_fi_graph::
compute_new_field_edges (pt_node_index heap_nid, 
	tree heap_decl,
	map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_in_field_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & gen_incl_out_field_edges)
{
	if (!heap_decl)
	{
		RESULT ("\nError: compute_new_field_edges() called for heap_decl=NULL");
		return;
	}

	// Find csvarinfo_t root of HEAP_DECL
	csvarinfo_t root = program.cs_lookup_vi_for_tree (heap_decl);
	if (!root)
	{
		RESULT ("\nError: csvarinfo_t of heap_decl (typecast of heap_nid=%d) not found. heap_decl=",
			heap_nid);
		print_node (dump_file, 0, heap_decl, 0);
		return;
	}

	// Find fresh heap node for ROOT. However, note that till now
	// on-the-fly (newly) generated nodes have not been added to fresh
	// nodes. So first fetch all nodes with name ROOT. Then filter out
	// fresh nodes if more than one such nodes are found.
	set<pt_node_index> fresh_root_nodes;

	generate_addressof_nodes (root->id, fresh_root_nodes);
	if (!fresh_root_nodes.size ())
	{
		RESULT ("\nError: Root nodes for root=%s(%d) not found", root->name, root->id);
		return;
	}
	if (fresh_root_nodes.size () > 1)
		generate_fresh_addressof_nodes (root->id, fresh_root_nodes);
	if (fresh_root_nodes.size () != 1)
	{
		RESULT ("\nError: fresh_root_nodes.size=%d for root=%s(%d)", 
			fresh_root_nodes.size (), root->name, root->id);
		return;
	}
	pt_node_index fresh_root_nid = *(fresh_root_nodes.begin ());

	// For each out-node fresh_field_node via field f of FRESH_ROOT_NODE
	pt_fi_node * fresh_root_node = nodes[fresh_root_nid];
	if (!fresh_root_node)
	{
		RESULT ("\nError: fresh_root_node for fresh_root_nid=%d not found", fresh_root_nid);
		return;
	}
	map<label, set<pt_node_index> > oute = fresh_root_node->get_out_edge_list ();
	map<label, set<pt_node_index> >::iterator ei;
	for (ei = oute.begin (); ei != oute.end (); ei++)
	{
		label field = ei->first;
		set<pt_node_index> outn = ei->second;
		if (outn.size () != 1)
		{
			RESULT ("\nError: outn.size=%d of fresh node=%d via field=%d",
				outn.size (), fresh_root_nid, field);
			return;
		}
		pt_node_index fresh_field_node = *(outn.begin ());

		// If fresh_field_node is not in fresh_nodes, it may not be an
		// error because till now on-the-fly (newly) generated field
		// nodes have not been added to fresh nodes.
		// if (!is_fresh_heap_node (fresh_field_node))
		// {
		// 	RESULT ("\nError: field_node=%d of fresh root node=%d is not fresh",
		//		fresh_field_node, fresh_root_nid);
		// }

#if PULL_ACCESS_NAMES
		// Store gen_incl_in_edges += <fresh_field_node, <f, heap_nid>>.
		gen_incl_in_field_edges[fresh_field_node][field].insert (heap_nid);
#else
		gen_incl_out_field_edges[heap_nid][field].insert (fresh_field_node);
#endif
	}
}

set<label> pt_fi_graph::
get_pointees (label pointer, set<pt_node_index> & valid_nodes)
{
	set<pt_node_index> addr_nodes;
	get_addressof_nodes (pointer, addr_nodes);
	set<pt_node_index> pointee_nodes;
	get_destination_nodes (addr_nodes, ASTERISK, pointee_nodes, valid_nodes);

	set<pt_node_index> pointee_names;
#if SUMM_K_CONSISTENT
	// In this case due to merging of nodes beyond k edges, a node may have
	// more than one name.
	get_all_names (pointee_nodes, pointee_names);
#else
	get_nodes_names (pointee_nodes, pointee_names);
#endif
	return pointee_names;
}

/**
 * This function fetches nodes reachable from VARS. It excludes fields that are
 * unreachable.
 */

set<pt_node_index> pt_fi_graph::
get_reachable_nodes (set<label> & vars, set<pt_node_index> & valid_nodes)
{
	FUNBEGIN ();

	DEBUG ("\nget_reachable_nodes()");

	// Nodes reachable via function arguments are REACHABLE_NODES
	// Nodes reachable to REACHABLE_NODES are also REACHABLE_NODES

	set<pt_node_index> reachable_nodes;
	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
		get_reachable_nodes (*vi, reachable_nodes, valid_nodes);

	pt_node_index stack_id = stack.get_node_id ();
	DEBUG ("\nInserting stack=%d to reachable_nodes", stack_id);
	reachable_nodes.insert (stack_id);

	RETURN (reachable_nodes);
	// return reachable_nodes;
}

void pt_fi_graph::
get_reachable_nodes (label var, set<pt_node_index> & reachable_nodes, set<pt_node_index> & valid_nodes)
{
	DEBUG ("\nget_reachable_nodes()");
	pt_node_index stack_id = stack.get_node_id ();

	set<pt_node_index> empty_set;
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;

	// Nodes reachable via function arguments are REACHABLE_NODES
	// Nodes reachable to REACHABLE_NODES are also REACHABLE_NODES
	set<pt_node_index> conn_n;
	get_out_nodes (stack_id, var, conn_n, valid_nodes);

	set<pt_node_index>::iterator ni;
	for (ni = conn_n.begin (); ni != conn_n.end (); ni++)
	{
		pt_node_index nid = *ni;
		DEBUG ("\nmark_reachable_nodes from pt=%d", nid);
		pt_fi_node * n = nodes[*ni];
		// We do not find nodes reachable to null/readonly/undef nodes
		// because these nodes do not indicate alias relationship.
		n->mark_reachable_nodes (nodes, empty_set, empty_set, empty_edges, empty_edges,
			reachable_nodes, valid_nodes);
	}
}

/**
 * Here we do not exclude Ekill edges (reachable from must_lptr) because the
 * out-nodes reachable via Ekill edges are already included in NVISIT. 
 */

set<pt_node_index> pt_fi_graph::
get_reachable_nodes (set<pt_node_index> & nvisit,
	set<pt_node_index> & lptr,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<pt_node_index> & valid_nodes)
{
	FUNBEGIN ();

	set<pt_node_index> reachable_nodes;

	set<pt_node_index>::iterator ni;
	for (ni = nvisit.begin (); ni != nvisit.end (); ni++)
	{
		pt_node_index nid = *ni;
		pt_fi_node * n = nodes[nid];
		n->mark_reachable_nodes (nodes, lptr, rpte, incl_in_edges, incl_out_edges,
			reachable_nodes, valid_nodes);
	}

	RETURN (reachable_nodes);
	// return reachable_nodes;
}

/**
 * INT_BNDRY_NODES: Nodes from INSIDE_NODES whose predecessor nodes are not in
 * INSIDE_NODES and are in VALID_NODES. These are the nodes whose APs will
 * change.
 * EXT_BNDRY_NODES: Predecessor nodes of INSIDE_NODES which are not in
 * INSIDE_NODES and are in VALID_NODES. These are the nodes whose APs will not
 * change. So this set includes the stack node also.
 */

void pt_fi_graph::
get_int_ext_bndry_nodes (set<pt_node_index> & inside_nodes,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<pt_node_index> & int_bndry_nodes,
	set<pt_node_index> & ext_bndry_nodes,
	set<pt_node_index> & valid_nodes)
{
	FUNBEGIN ();

	pt_node_index stack_id = stack.get_node_id ();

	set<pt_node_index>::iterator ni;
	for (ni = inside_nodes.begin (); ni != inside_nodes.end (); ni++)
	{
		pt_node_index nid = *ni;
		pt_fi_node * n = nodes[nid];

		// Get IN_ADJ_NODES that are in VALID_NODES
		set<pt_node_index> in_adj_nodes;
		n->get_in_adj_nodes (lptr, must_lptr, l, rpte, incl_in_edges, incl_out_edges,
			in_adj_nodes, valid_nodes);

		set<pt_node_index>::iterator ini;
		for (ini = in_adj_nodes.begin (); ini != in_adj_nodes.end (); ini++)
		{
			pt_node_index inid = *ini;

			// If INID is not in INSIDE_NODES, then NID is an
			// int_bndry node and INID is an ext_bndry node.
			if (inside_nodes.find (inid) == inside_nodes.end ())
			{
				int_bndry_nodes.insert (nid);
				ext_bndry_nodes.insert (inid);
			}
		}
	}
	// Access paths of stack node never change. So this set should include
	// the stack node.
	if (pt_fi_node::is_node_valid_at_point (stack.get_node_id (), valid_nodes))
		ext_bndry_nodes.insert (stack.get_node_id ());

	RETURN_VOID ();
}

set<pt_node_index> pt_fi_graph::
get_int_bndry_nodes (set<pt_node_index> & inside_nodes,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<pt_node_index> & valid_nodes)
{
	FUNBEGIN ();

	set<pt_node_index> int_bndry;
	set<pt_node_index> ext_bndry;
	get_int_ext_bndry_nodes (inside_nodes,
		lptr, must_lptr, l, rpte, incl_in_edges, incl_out_edges,
		int_bndry, ext_bndry, valid_nodes);

	RETURN (int_bndry);
	// return int_bndry;
}

set<pt_node_index> pt_fi_graph::
get_ext_bndry_nodes (set<pt_node_index> & inside_nodes,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<pt_node_index> & valid_nodes)
{
	set<pt_node_index> int_bndry;
	set<pt_node_index> ext_bndry;
	get_int_ext_bndry_nodes (inside_nodes,
		lptr, must_lptr, l, rpte, incl_in_edges, incl_out_edges,
		int_bndry, ext_bndry, valid_nodes);

	return ext_bndry;
}

void pt_fi_graph::
insert_fresh_nodes (map<pt_node_index, bool> & new_nodes)
{
	map<pt_node_index, bool>::iterator ni;
	for (ni = new_nodes.begin (); ni != new_nodes.end (); ni++)
	{
		pt_node_index nid = ni->first;

		DEBUG ("\nFresh node=%d", nid);

#if SUMM_K_CONSISTENT
		// An on-the-fly heap field node may be a summary node in which
		// case it is not marked as heap. NEW_NODES which are summary
		// nodes can only be on-the-fly generated heap nodes; therefore
		// they are added to fresh_heap_nodes below.
		pt_fi_node * n = nodes[nid];
		if (n->get_is_summary_node ())
		{
			DEBUG ("=heap");
			fresh_heap_nodes.insert (nid);
			continue;
		}
#endif
		if (is_heap_node (nid))
		{
			DEBUG ("=heap");
			fresh_heap_nodes.insert (nid);
		}
		else 
		{
			DEBUG ("=named");
			fresh_named_nodes.insert (nid);
		}
	}
}

/**
 * Generate field edges from SRC_NIDS to the field nodes inside structure
 * SRC_VAR.
 */

void pt_fi_graph::
insert_field_edges (set<pt_node_index> & src_nids, csvarinfo_t src_var)
{
	DEBUG ("\ninsert_field_edges (%s(%d))", src_var->name, src_var->id);
	// Get all the field variables inside structure SRC_VAR->decl
	set<label> reachable_field_vars;
	program.get_reachable_fields (src_var, reachable_field_vars);

	set<label>::iterator fi;
	for (fi = reachable_field_vars.begin (); fi != reachable_field_vars.end (); fi++)
	{
		label field_var = *fi;
		if (!program.is_repr_var (field_var))
			continue;

		csvarinfo_t field_info = VEC_index (csvarinfo_t, program.variable_data, field_var);
		label field_edge = field_info->offset - src_var->offset;
		// Do not create a field edge if source and destination nodes are same. e.g.
		// struct type1 { int * p; struct type2 f; }; struct type2 { struct type2 *g; };
		// For x of type1, x.f (source node) reaches x.f.g (destination
		// node) via field edge 0; however, both x.f and x.f.g are
		// represented by the same node.
		if (!field_edge)
			continue;
		if (field_edge < 0)
		{
			RESULT ("\nError: Negative field edge");
			continue;
		}

		set<pt_node_index> field_nodes;
		generate_addressof_nodes (field_var, field_nodes);
		if (field_nodes.size () != 1)
		{
			RESULT ("\nError: Only one field node should have been generated.");
			set<pt_node_index>::iterator ni;
			RESULT ("\nField=%s(%d), gpt field nodes=", field_info->name, field_info->id);
			for (ni = field_nodes.begin (); ni != field_nodes.end (); ni++)
				RESULT ("%d,", *ni);
			return;
		}

		DEBUG ("\ninsert_field_edges: %s(%d) -> %d -> %s(%d)",
			src_var->name, src_var->id, field_edge, field_info->name, field_info->id);
		insert_edges (src_nids, field_nodes, field_edge);
	}
	DEBUG ("\ninsert_field_edges done");
}

/**
 * This function inserts an edge from lhs_nodes to rhs_nodes via l without
 * checking whether the new name of rhs_nodes (due to this new edge) is already
 * present or not. The function calling this function should do this check.
 */

void pt_fi_graph::
insert_edges (set<pt_node_index> lhs_nodes, set<pt_node_index> rhs_nodes, label l)
{
	DEBUG ("\ninsert_edges ()");
	pt_node_index stack_id = stack.get_node_id ();

	// Inserting edge from all lhs to all rhs
	set<pt_node_index>::iterator lhsi;
	for (lhsi = lhs_nodes.begin (); lhsi != lhs_nodes.end (); lhsi++)
	{
		pt_node_index lhs_id = *lhsi;
		pt_fi_node * lhs_dest = nodes[*lhsi];
		DEBUG ("\nlhs_dest = %d", lhs_dest->get_node_id ());

		// If LHS_ID is not stack node and LHS_ID is an improper node,
		// then do not insert edge.
		label lhs_name = lhs_dest->get_node_name (stack_id);

		// SUMM_K_CONSISTENT: node with is_summary_node has
		// lhs_name=wild_card_id which is representing a var and does not
		// pass the following if-condition.
		if (stack_id != lhs_id && !program.is_repr_var (lhs_name))
			continue;

		set<pt_node_index>::iterator rhsi;
		for (rhsi = rhs_nodes.begin (); rhsi != rhs_nodes.end (); rhsi++)
		{
			pt_fi_node * rhs_dest;
			rhs_dest = nodes[*rhsi];

#if DEBUG_CONTAINER
			map<label, set<pt_node_index> >::iterator outei;
			map<label, set<pt_node_index> > out_edges = lhs_dest->get_out_edge_list ();
			outei = out_edges.find (l);
			if (outei != out_edges.end ())
			{
				set<pt_node_index> out_nodes = outei->second;
				if (out_nodes.find (*rhsi) == out_nodes.end ())
				{
					DEBUG ("\nlhs %d -> %d -> rhs %d did not exist",
						*lhsi, l, *rhsi);
				}
			}
			else if (outei == out_edges.end ())
			{
				DEBUG ("\nlhs %d -> %d -> rhs %d did not exist",
					*lhsi, l, *rhsi);
			}

			DEBUG ("\nrhs_dest = %d", rhs_dest->get_node_id ());
#endif
			lhs_dest->insert_edge (l, *rhs_dest, stack.get_node_id ());
		}
	}
}

pt_fi_node * pt_fi_graph::
get_clone (pt_node_index nid,
	map<pt_node_index, pt_node_index> & clone)
{
	if (clone.find (nid) != clone.end ())
	{
		pt_node_index clone_nid = clone[nid];
		pt_fi_node * clone_n = nodes[clone_nid];
		return clone_n;		
	}

	// If the clone of nid is not found, then it means the node is not
	// cloned.
	pt_fi_node * clone_n = nodes[nid];
	return clone_n;
}

/**
 * This function clones the out-edges of NID and stores them in
 * cloned_in_edges.
 *
 * @returns: transitive_call_clone
 * @returns: cloned_in_edges, cloned_out_edges
 * @returns: cloned_nodes
 */

void pt_fi_graph::
clone_out_edges (pt_node_index nid,
	set<pt_node_index> & int_bndry_nodes,
	map<pt_node_index, set<pt_node_index> > & caller_callee_clone,
	set<pt_node_index> & valid_nodes,
	map<pt_node_index, set<pt_node_index> > & transitive_call_clone,
	map<pt_node_index, map<label, set<pt_node_index> > > & cloned_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & cloned_out_edges)
{
	FUNBEGIN ();

	DEBUG ("\nclone_out_edges (nid=%d)", nid);
	pt_fi_node * n = nodes[nid];
	map<label, set<pt_node_index> > out_edges = n->get_out_edge_list ();
	map<label, set<pt_node_index> >::iterator outei;
	for (outei = out_edges.begin (); outei != out_edges.end (); outei++)
	{
		label out_label = outei->first;
		set<pt_node_index> out_nodes = outei->second;
		set<pt_node_index>::iterator outni;
		for (outni = out_nodes.begin (); outni != out_nodes.end (); outni++)
		{
			pt_node_index out_nid = *outni;
			DEBUG ("\nout-edge %d->%d->%d", nid, out_label, out_nid);
			if (int_bndry_nodes.find (out_nid) == int_bndry_nodes.end ())
				continue;
			DEBUG ("\nout-node=%d is boundary", out_nid);

			// Find transitive_clones of out-nodes of NID
			set<pt_node_index> transitive_clones;
			set<pt_node_index> visited_nodes;
			get_transitive_clones (out_nid, caller_callee_clone, valid_nodes, 
				transitive_clones, visited_nodes);

			if (transitive_clones.size ())
			{
				// transitive_call_clone[out_nid].insert (transitive_clones.begin (), transitive_clones.end ());
				merge_set (transitive_clones, transitive_call_clone[out_nid]);
			}
#if INTERMEDIATE_RESULT
			RESULT ("\nTransitive clones of %d=", out_nid);
			set<pt_node_index>::iterator ti;
			for (ti = transitive_clones.begin (); ti != transitive_clones.end (); ti++)
				RESULT ("%d,", *ti);
#endif

			// Clone the out-edges of NID
			set<pt_node_index>::iterator ci;
			for (ci = transitive_clones.begin (); ci != transitive_clones.end (); ci++)
			{
				pt_node_index out_cid = *ci;
				// Even if OUT_CID is a summary node, OUT_LABEL
				// will be converted to wild_card_id when the
				// edge is actually inserted into gPt.
#if PULL_ACCESS_NAMES
				cloned_in_edges[out_cid][out_label].insert (nid);
#else
				cloned_out_edges[nid][out_label].insert (out_cid);
#endif
				DEBUG ("\ncloned-edge %d->%d->%d", nid, out_label, out_cid);
			}
		}
	}

	RETURN_VOID ();
}

/**
 * Apply CALLEE_CLONE transitively on NID to reach a node in TRANSFORMED_VALUE.
 */

void pt_fi_graph::
get_transitive_clones (pt_node_index nid, 
	map<pt_node_index, set<pt_node_index> > & callee_clone, 
	set<pt_node_index> & transformed_value, 
	set<pt_node_index> & transitive_clones,
	set<pt_node_index> & visited_nodes)
{
	FUNBEGIN ();

	DEBUG ("\nget_transitive_clones (%d)", nid);

	// If NID already visited (whether or not added to TRANSITIVE_CLONES)
	if (visited_nodes.find (nid) != visited_nodes.end ())
		RETURN_VOID ();
		//return;
	visited_nodes.insert (nid);

	// NID is the cloned form
	if (transformed_value.find (nid) != transformed_value.end ())
		transitive_clones.insert (nid);

	// Find the clones transitively
	set<pt_node_index> clones;
	if (callee_clone.find (nid) != callee_clone.end ())
		clones = callee_clone[nid];
	set<pt_node_index>::iterator ci;
	for (ci = clones.begin (); ci != clones.end (); ci++)
		get_transitive_clones (*ci, callee_clone, transformed_value, transitive_clones, visited_nodes);
		
	RETURN_VOID ();
}

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
void pt_fi_graph::
clear_partial_order_info ()
{
	strictly_stronger_nodes.clear ();
	strictly_stronger_edges.clear ();
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
set<pt_node_index> pt_fi_graph::
get_strictly_stronger_nodes (pt_node_index n)
{
	if (strictly_stronger_nodes.find (n) == strictly_stronger_nodes.end ())
	{
		// This is not an error. Even when strictly stronger nodes of n
		// have been already computed, it could be the case that no
		// strictly strong node was found for n.
		set<pt_node_index> empty;
		return empty;
	}
	return strictly_stronger_nodes[n];
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
bool pt_fi_graph::
is_node_strictly_stronger (pt_node_index n1, pt_node_index n2)
{
	if (n1 == n2)
		return false;

	if (strictly_stronger_nodes.find (n1) == strictly_stronger_nodes.end ())
		return false;

	set<pt_node_index> ssn = strictly_stronger_nodes[n1];
	if (ssn.find (n2) != ssn.end ())
		return true;

	return false;
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
void pt_fi_graph::
add_strictly_stronger_node (pt_node_index n1, pt_node_index n2)
{
	strictly_stronger_nodes[n1].insert (n2);
	program_strictly_stronger_nodes[n1].insert (n2);
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
void pt_fi_graph::
record_weak_nodes_statistics (unsigned int weak_nodes_count_pp, unsigned int weak_strong_nodes_count_pp)
{
	tot_avg_weak_nodes += (float) weak_nodes_count_pp / weak_strong_nodes_count_pp;
	tot_weak_nodes += weak_nodes_count_pp;
	tot_weak_strong_nodes += weak_strong_nodes_count_pp;
	if (max_weak_nodes_at_pp < weak_nodes_count_pp)
		max_weak_nodes_at_pp = weak_nodes_count_pp;

	po_calls++;
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
bool pt_fi_graph::
is_edge_strictly_stronger (g_pt_edge e1, g_pt_edge e2)
{
	if (e1 == e2)
		return false;

	if (strictly_stronger_edges.find (e1) == strictly_stronger_edges.end ())
		return false;

	set<g_pt_edge> sse = strictly_stronger_edges[e1];
	if (sse.find (e2) != sse.end ())
		return true;

	return false;
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
void pt_fi_graph::
add_strictly_stronger_edge (g_pt_edge e1, g_pt_edge e2)
{
	strictly_stronger_edges[e1].insert (e2);
}
#endif

void pt_fi_graph::
count_clones (unsigned int & tot_stack_clones,
	unsigned int & tot_heap_clones,
	unsigned int & max_stack_clones,
	unsigned int & max_heap_clones,
	unsigned int & tot_repeating_stack_vars,
	unsigned int & tot_repeating_heap_vars,
	bool all_valid)
{
	set<pt_node_index> valid_nodes;
	count_clones (tot_stack_clones, tot_heap_clones, max_stack_clones, max_heap_clones, 
		tot_repeating_stack_vars, tot_repeating_heap_vars, valid_nodes, all_valid);
}

void pt_fi_graph::
count_clones (unsigned int & tot_stack_clones,
	unsigned int & tot_heap_clones,
	unsigned int & max_stack_clones,
	unsigned int & max_heap_clones,
	unsigned int & tot_repeating_stack_vars,
	unsigned int & tot_repeating_heap_vars,
	set<pt_node_index> & valid_nodes,
	bool all_valid)
{
	map<label, set<pt_node_index> > oute = stack.get_out_edge_list ();
	map<label, set<pt_node_index> >::iterator ei;
	for (ei = oute.begin (); ei != oute.end (); ei++)
	{
		label v = ei->first;
		set<pt_node_index> cloned_nodes = ei->second;
		if (!all_valid)
			pt_fi_node::get_nodes_valid_at_point (cloned_nodes, valid_nodes);
		if (!cloned_nodes.size ())
			continue;

		if (program.heap_var (v))
		{
			tot_repeating_heap_vars++;
			tot_heap_clones += cloned_nodes.size ();
			if (max_heap_clones < cloned_nodes.size ())
				max_heap_clones = cloned_nodes.size ();
		}
		else
		{
			tot_repeating_stack_vars++;
			tot_stack_clones += cloned_nodes.size ();
			if (max_stack_clones < cloned_nodes.size ())
				max_stack_clones = cloned_nodes.size ();
		}
	}
}

unsigned int pt_fi_graph::
count_graph_edges (set<pt_node_index> & valid_nodes)
{
	unsigned int edge_count = 0;

	set<pt_node_index>::iterator ni;
	for (ni = valid_nodes.begin (); ni != valid_nodes.end (); ni++)
	{
		pt_node_index nid = *ni;
		pt_fi_node * n = nodes[nid];
		map<label, set<pt_node_index> > oute = n->get_out_edge_list ();
		map<label, set<pt_node_index> >::iterator ei;
		for (ei = oute.begin (); ei != oute.end (); ei++)
		{
			set<pt_node_index> outn = ei->second;
			pt_fi_node::get_nodes_valid_at_point (outn, valid_nodes);
			edge_count += outn.size ();
		}
	}
	return edge_count;
}

void pt_fi_graph::
print_statistics ()
{
	unsigned int edge_count = 0;

	map<pt_node_index, pt_fi_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		pt_fi_node * n = ni->second;
		map<label, set<pt_node_index> > oute = n->get_out_edge_list ();
		map<label, set<pt_node_index> >::iterator ei;
		for (ei = oute.begin (); ei != oute.end (); ei++)
		{
			set<pt_node_index> outn = ei->second;
			edge_count += outn.size ();
		}
	}

	float avg_stack_clones = 0;
	float avg_heap_clones = 0;
	unsigned int max_stack_clones = 0;
	unsigned int max_heap_clones = 0;
	unsigned int tot_stack_clones = 0;
	unsigned int tot_repeating_stack_vars = 0;
	unsigned int tot_heap_clones = 0;
	unsigned int tot_repeating_heap_vars = 0;
	bool all_valid = true;
	count_clones (tot_stack_clones, tot_heap_clones, max_stack_clones, max_heap_clones,
		tot_repeating_stack_vars, tot_repeating_heap_vars, all_valid);

	if (tot_repeating_stack_vars)
		avg_stack_clones = (float) tot_stack_clones / tot_repeating_stack_vars;
	if (tot_repeating_heap_vars)
		avg_heap_clones = (float) tot_heap_clones / tot_repeating_heap_vars;

	RESULT ("\ng_pt, nodes=%d", nodes.size ());
	RESULT ("\ng_pt, edges=%d", edge_count);
	RESULT ("\ng_pt, tot_repeating_stack_vars=%d", tot_repeating_stack_vars);
	RESULT ("\ng_pt, tot_stack_clones=%d", tot_stack_clones);
	RESULT ("\ng_pt, avg_stack_clones=%f", avg_stack_clones);
	RESULT ("\ng_pt, tot_repeating_heap_vars=%d", tot_repeating_heap_vars);
	RESULT ("\ng_pt, tot_heap_clones=%d", tot_heap_clones);
	RESULT ("\ng_pt, avg_heap_clones=%f", avg_heap_clones);
	RESULT ("\ng_pt, max_stack_clones=%d", max_stack_clones);
	RESULT ("\ng_pt, max_heap_clones=%d", max_heap_clones);

	FILE * stat_file = fopen (STAT_FILE, "a");
	if (!stat_file)
	{
		RESULT ("\nError: cannot open STAT_FILE=%d", STAT_FILE);
		return;
	}
	fprintf (stat_file, "\ng_pt, nodes=%d", nodes.size ());
	fprintf (stat_file, "\ng_pt, edges=%d", edge_count);
	fprintf (stat_file, "\ng_pt, tot_repeating_stack_vars=%d", tot_repeating_stack_vars);
	fprintf (stat_file, "\ng_pt, tot_stack_clones=%d", tot_stack_clones);
	fprintf (stat_file, "\ng_pt, avg_stack_clones=%f", avg_stack_clones);
	fprintf (stat_file, "\ng_pt, tot_repeating_heap_vars=%d", tot_repeating_heap_vars);
	fprintf (stat_file, "\ng_pt, tot_heap_clones=%d", tot_heap_clones);
	fprintf (stat_file, "\ng_pt, avg_heap_clones=%f", avg_heap_clones);
	fprintf (stat_file, "\ng_pt, max_stack_clones=%d", max_stack_clones);
	fprintf (stat_file, "\ng_pt, max_heap_clones=%d", max_heap_clones);

	fclose (stat_file);
}

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
void pt_fi_graph::
print_partial_order_statistics ()
{
	unsigned int count_po = 0;
	unsigned int count_weak_nodes = program_strictly_stronger_nodes.size ();
	map<pt_node_index, set<pt_node_index> >::iterator poi;
	for (poi = program_strictly_stronger_nodes.begin (); 
		poi != program_strictly_stronger_nodes.end ();
		poi++)
	{
		count_po += poi->second.size ();
	}

	RESULT ("\nNumber of unique partial orders=%d", count_po); 
	RESULT ("\nweak_nodes=%d", count_weak_nodes);
	RESULT ("\ntot_weak_nodes=%d", tot_weak_nodes);
	RESULT ("\ntot_weak_strong_nodes=%d", tot_weak_strong_nodes);
	RESULT ("\navg weak_nodes=%f", (float) tot_weak_nodes / tot_weak_strong_nodes);
	RESULT ("\nmax_weak_nodes_at_pp=%d", max_weak_nodes_at_pp);
	RESULT ("\ntot of avg_weak_nodes=%f", tot_avg_weak_nodes);
	RESULT ("\ncalls for weak_nodes=%d", po_calls);
	RESULT ("\navg of avg_weak_nodes=%f", tot_avg_weak_nodes / po_calls);

	FILE * stat_file = fopen (STAT_FILE, "a");
	if (!stat_file)
	{
		RESULT ("\nError: cannot open STAT_FILE=%d", STAT_FILE);
		return;
	}
	fprintf (stat_file, "\nNumber of unique partial orders=%d", count_po); 
	fprintf (stat_file, "\nweak_nodes=%d", count_weak_nodes);
	fprintf (stat_file, "\ntot_weak_nodes=%d", tot_weak_nodes);
	fprintf (stat_file, "\ntot_weak_strong_nodes=%d", tot_weak_strong_nodes);
	fprintf (stat_file, "\navg weak_nodes=%f", (float) tot_weak_nodes / tot_weak_strong_nodes);
	fprintf (stat_file, "\nTotal repeating weak_nodes=%d", tot_weak_nodes);
	fprintf (stat_file, "\nmax_weak_nodes_at_pp=%d", max_weak_nodes_at_pp);
	fprintf (stat_file, "\ntot of avg_weak_nodes=%f", tot_avg_weak_nodes);
	fprintf (stat_file, "\ncalls for weak_nodes=%d", po_calls);
	fprintf (stat_file, "\navg of avg_weak_nodes=%f", tot_avg_weak_nodes / po_calls);

	fclose (stat_file);
}
#endif

void pt_fi_graph::
get_points_to_pairs (set<pt_node_index> & pt_nodes, 
	map<label, set<label> > & points_to_pairs,
	map<label, set<label> > & summ_stack_to_stack_pointers)
{
	set<pt_node_index>::iterator ni;
	pt_node_index stack_id = stack.get_node_id ();

	for (ni = pt_nodes.begin (); ni != pt_nodes.end (); ni++)
	{
		pt_fi_node * n = nodes[*ni];
		n->get_points_to_pairs (pt_nodes, points_to_pairs, summ_stack_to_stack_pointers, nodes, stack_id);
	}
}

unsigned int pt_fi_graph::
print_points_to_pairs (map<label, set<label> > & points_to_pairs, bool one_line, set<label> & heap_to_stack_pointees)
{
	unsigned int heap_to_stack_pointers = 0;
	map<label, set<label> >::iterator pi;
	for (pi = points_to_pairs.begin (); pi != points_to_pairs.end (); pi++)
	{
		label ptr_id = pi->first;
		csvarinfo_t ptr = VEC_index (csvarinfo_t, program.variable_data, ptr_id);
		set<label> ptes = pi->second;
		set<label>::iterator ptei;
		for (ptei = ptes.begin (); ptei != ptes.end (); ptei++)
		{
			label pte_id = *ptei;
			csvarinfo_t pte = VEC_index (csvarinfo_t, program.variable_data, pte_id);
			if (one_line)
			{
				RESULT (", %s(%d) -> %s(%d), ", ptr->name, ptr_id, pte->name, pte_id);
			}
#if SUMM_K_CONSISTENT
			else if (program.heap_var (ptr_id) && program.is_stack_pointer (pte))
			{
				RESULT ("\n\t\t!!!%s(%d) -> %s(%d)", ptr->name, ptr_id, pte->name, pte_id);
				heap_to_stack_pointees.insert (pte_id);
				heap_to_stack_pointers++;
			}
#endif
			else
			{
				RESULT ("\n\t\t%s(%d) -> %s(%d)", ptr->name, ptr_id, pte->name, pte_id);
			}
		}
	}
	return heap_to_stack_pointers;
}

void pt_fi_graph::
print_node_fields (FILE * file, 
	map<pt_node_index, set<pair<label, pt_node_index> > > & field_edges, 
	map<pt_node_index, pt_fi_node *> & nodes, 
	pt_node_index stack_id)
{
#if INTERMEDIATE_RESULT
	DEBUG ("\nprint_node_fields=");
	if (field_edges.size ())
		RESULT ("\nFields=");
	map<pt_node_index, set<pair<label, pt_node_index> > >::iterator ei;
	for (ei = field_edges.begin (); ei != field_edges.end (); ei++)
	{
		pt_node_index src = ei->first;
		set<pair<label, pt_node_index> > out_edges = ei->second;
		set<pair<label, pt_node_index> >::iterator oei;
		for (oei = out_edges.begin (); oei != out_edges.end (); oei++)
		{
			label l = oei->first;
			pt_node_index dest = oei->second;
			RESULT ("(%d,%d,%d),", src, l, dest);
		}
	}
#endif
}

#if SUMM_K_CONSISTENT
void pt_fi_graph::
print_summary_nodes ()
{
	RESULT ("\nSummary nodes=");
	map<pt_node_index, pt_fi_node *>::iterator mi;
	for (mi = nodes.begin (); mi != nodes.end (); mi++)
	{
		pt_node_index nid = mi->first;
		pt_fi_node * n = mi->second;
		if (n->get_is_summary_node ())
			RESULT ("%d,", nid);
	}
}
#endif

set<pt_node_index> pt_fi_graph::
print_subgraph (FILE * file, set<pt_node_index> & pt_nodes)
{
	DEBUG ("\npt_fi_graph::print_subgraph ()");
	DEBUG ("\nNumber of nodes=%d", pt_nodes.size ());

	set<pt_node_index> ptr_pte;

	if (file)
		fprintf (file, "\ndigraph pt_fi_graph {");

	set<pt_node_index>::iterator ni;
#if DEBUG_CONTAINER
	DEBUG ("\nNodes: ");
	for (ni = pt_nodes.begin (); ni != pt_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif

	pt_node_index stack_id = stack.get_node_id ();
	map<pt_node_index, set<pair<label, pt_node_index> > > field_edges;

	for (ni = pt_nodes.begin (); ni != pt_nodes.end (); ni++)
	{
		DEBUG ("\nprinting node %d", *ni);
		pt_fi_node * n = nodes[*ni];
		n->print_node (file, nodes, false);
		set<pt_node_index> pt = n->print_node_pointers (NULL, pt_nodes, nodes, stack_id);
		// ptr_pte.insert (pt.begin (), pt.end ());
		merge_set (pt, ptr_pte);
		n->get_node_fields (pt_nodes, field_edges);
	}

	print_node_fields (NULL, field_edges, nodes, stack_id);
 
#if DEBUG_CONTAINER
	DEBUG ("\nForward edges done");

	for (ni = pt_nodes.begin (); ni != pt_nodes.end (); ni++)
	{
		pt_fi_node * n = nodes[*ni]; 
		n->print_node_reverse (file);
	}

	DEBUG ("\nBackward edges done");
#endif

	if (file)
		fprintf (file, "}");

#if CHECK_CONTAINER
	// VARIABLE_DATA is passed by analysis only when THIS graph is in okay
	// state
	// is_graph_okay ();
#endif

	return ptr_pte;
}

void pt_fi_graph::
print_graph (FILE * file)
{
	DEBUG ("\npt_fi_graph::print_graph ()");
	DEBUG ("\nRoot node %d", stack.get_node_id ());
	DEBUG ("\nNumber of nodes=%d", nodes.size ());
	if (file)
		fprintf (file, "\ndigraph pt_fi_graph {");

	map<pt_node_index, pt_fi_node *>::iterator ni;
#if DEBUG_CONTAINER
	DEBUG ("\nNodes: ");
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		pt_fi_node * n = ni->second;
		DEBUG ("%d,", n->get_node_id ());
	}
#endif

	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		DEBUG ("\nprinting node %d", ni->first);
		pt_fi_node * n = ni->second;
		n->print_node (file, nodes);
	}
#if DEBUG_CONTAINER
	DEBUG ("\nForward edges done");

	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		pt_fi_node * n = ni->second;
		n->print_node_reverse (file);
	}

	DEBUG ("\nBackward edges done");
#endif

	if (file)
		fprintf (file, "}");

#if SUMM_K_CONSISTENT
	print_summary_nodes ();
#endif

#if CHECK_CONTAINER
	// VARIABLE_DATA is passed by analysis only when THIS graph is in okay
	// state
	// is_graph_okay ();
#endif
}


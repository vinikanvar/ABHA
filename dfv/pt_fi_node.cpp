
/************************
 * @author Vini Kanvar
************************/

#include "pt_fi_node.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

// We assume that node index 0 does not exist
unsigned int pt_fi_node::
number_of_nodes = 1;

pt_fi_node::
pt_fi_node ()
{
	RESULT ("\nError: pt_fi_node constructor should be called with nodes");
}

pt_fi_node::
pt_fi_node (map<pt_node_index, pt_fi_node *> & nodes)
{
	node_id = number_of_nodes;
	nodes[node_id] = this;
	number_of_nodes++;
#if SUMM_K_CONSISTENT
	is_summary_node = false;
#endif
	DEBUG ("\npt_fi_node %d,%x", node_id, this);
}

pt_fi_node::
~pt_fi_node ()
{
	DEBUG ("\nDeleting pt_fi_node %d,%x", node_id, this);
}

pt_node_index pt_fi_node::
get_node_id ()
{
	return node_id;
}

map<label, set<pt_node_index> > pt_fi_node::
get_in_edge_list ()
{
	return in_edge_list;
}

map<label, set<pt_node_index> > pt_fi_node::
get_out_edge_list ()
{
	return out_edge_list;
}

set<pt_node_index> pt_fi_node::
get_in_nodes (label l)
{
	if (in_edge_list.find (l) != in_edge_list.end ())
		return in_edge_list[l];
	set<pt_node_index> empty_set;
	return empty_set;
}

set<pt_node_index> pt_fi_node::
get_out_nodes (label l)
{
	if (out_edge_list.find (l) != out_edge_list.end ())
		return out_edge_list[l];
	set<pt_node_index> empty_set;
	return empty_set;
}


#if SUMM_K_CONSISTENT
bool pt_fi_node::
get_is_summary_node ()
{
	return is_summary_node;
}
#endif

#if SUMM_K_CONSISTENT
void pt_fi_node::
set_is_summary_node ()
{
	is_summary_node = true;
}
#endif

/** 
 * This function retains in PT_NODES those nodes that are in THIS VALUE, which
 * includes nodes coming from predecessor program points, and free/fresh heap
 * locations (including on-the-fly created heap field nodes). or 
 
 * Earlier I was not including the following in VALUE_IN: newly created (i.e.
 * nodes whose id is greater than OLD_MAX_NODE_ID) or unused heap (and field)
 * nodes (i.e. those belonging to G_PT.FRESH_NODES).  Therefore, the following
 * checks were additionally required to check if a node is valid at a program
 * point:
 * (i)
 * Note that the formulations retain those nodes that are in either VALUE_IN or
 * RPTE. We cannot use RPTE because, if x (newly generated) although present in
 * RPTE, its field nodes x.f,x.g,... (newly generated) are present neither in
 * VALUE_IN nor RPTE. But we want to mark the field nodes also as valid. 
 * (ii)
 * Note that we tried fetching all the nodes generated by
 * generated_addressof_nodes(). However, this was not sufficient since heap
 * field nodes are also generated on-the-fly by generate_pointer_nodes(). Out
 * of all the gen/get nodes by generate_pointer_nodes() we cannot differentiate
 * which have been newly generated and which not. So we resorted to the use of
 * OLD_MAX_NODE_ID and FRESH_NODES to find this. 
 */ 
 
bool pt_fi_node::
is_node_valid_at_point (pt_node_index nid,
	set<pt_node_index> & valid_nodes)
{
	FUNBEGIN ();

	RETURN (valid_nodes.find (nid) != valid_nodes.end ());
	//return valid_nodes.find (nid) != valid_nodes.end ();
}

/** 
 * Since newly generated field nodes are added to set of valid nodes, we do not
 * need to consider incl_edges while calling get_nodes_valid_at_point() or
 * is_node_valid_at_point().
 */

void pt_fi_node::
get_nodes_valid_at_point (set<pt_node_index> & pt_nodes,
	set<pt_node_index> & valid_nodes)
{
	FUNBEGIN ();

        // For all n in PT_NODES, 
        set<pt_node_index>::iterator ni;
	for (ni = pt_nodes.begin (); ni != pt_nodes.end (); ) 
        {  
		pt_node_index nid = *ni;
		if (is_node_valid_at_point (nid, valid_nodes))
			ni++;
		else 
			pt_nodes.erase (ni++);

	} 

	RETURN_VOID ();
}

/**
 * This function returns the name (in-label) of THIS node. Each node has only
 * one name which is labeled on the in-edge from STACK node, unless
 * SUMM_K_CONSISTENT (in which case due to summarization beyond k sequences of
 * edges nodes are merged).
 */

label pt_fi_node::
get_node_name (pt_node_index stack_id)
{
#if SUMM_K_CONSISTENT
	if (is_summary_node)
		return wild_card_id;
#endif

	map<label, set<pt_node_index> >::iterator ei;
	for (ei = in_edge_list.begin (); ei != in_edge_list.end (); ei++)
	{
		set<pt_node_index> in_nodes = ei->second;
		if (in_nodes.find (stack_id) != in_nodes.end ())
		{
			if (ei->first == stack_deref)
				RESULT ("\nError: Node=%d has no variable name", node_id);
			return ei->first;
		}
	}
	return 0;
}

/**
 * This function returns all the names (in-labels) of THIS node. A node may
 * have more than one name which is labeled on the in-edges from STACK node in
 * SUMM_K_CONSISTENT (where due to summarization beyond k sequences of edges
 * nodes are merged).
 */

#if SUMM_K_CONSISTENT
void pt_fi_node::
get_all_names (pt_node_index stack_id, set<label> & names)
{
	map<label, set<pt_node_index> >::iterator ei;
	for (ei = in_edge_list.begin (); ei != in_edge_list.end (); ei++)
	{
		set<pt_node_index> in_nodes = ei->second;
		if (in_nodes.find (stack_id) != in_nodes.end ())
		{
			if (ei->first == stack_deref)
				RESULT ("\nError: Node=%d has no variable name", node_id);
			if (!program.is_proper_var (ei->first))
				continue;
			names.insert (ei->first);
		}
	}
}
#endif

/**
 * This function gets the destination nodes of THIS node through label L.
 *
 * @return true if THIS node is not proper variable node (undef/null/readonly)
 * i.e. the out-edge is missing i.e. the destination is undef. 
 */

bool pt_fi_node::
get_destination_nodes (label l, pt_node_index stack_id, set<pt_node_index> & dest_nodes)
{
#if SUMM_K_CONSISTENT
	if (l != wild_card_id && is_summary_node)
		return get_destination_nodes (wild_card_id, stack_id, dest_nodes);
#endif

	set<pt_node_index> empty_nodes;
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
	return get_destination_nodes (l, stack_id, dest_nodes,
		empty_nodes, empty_edges, empty_edges);
}

#if SUMM_TYPE_CLOSURE == 0 
/**
 * This function gets the destination nodes of THIS node through label L.
 *
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: dest_nodes
 * @return true if THIS node is not proper variable node (undef/null/readonly)
 * i.e. the out-edge is missing i.e. the destination is undef. 
 */

bool pt_fi_node::
get_destination_nodes (label l, pt_node_index stack_id, set<pt_node_index> & dest_nodes,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	DEBUG ("\nnode=%d -> get_destination_node (l=%d)", node_id, l);

	label computed_offset = 0;
	if (compute_offset (l, stack_id, dest_nodes, computed_offset))
		return true;
	l = computed_offset;
	DEBUG ("\nnode=%d -> get_destination_node (new-l=%d)", node_id, l);

	set<pt_node_index> dest_nodes_temp;

	if (l == ASTERISK && value_excl_out_edges.find (node_id) != value_excl_out_edges.end ())
		; // All out-edges of THIS node are killed in VALUE
	else if (out_edge_list.find (l) != out_edge_list.end ())
		// dest_nodes.insert (out_edge_list[l].begin (), out_edge_list[l].end ());
		merge_set (out_edge_list[l], dest_nodes);

#if PULL_ACCESS_NAMES
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator iei;
	for (iei = incl_in_edges.begin (); iei != incl_in_edges.end (); iei++)
	{
		pt_node_index dest_nid = iei->first;
		DEBUG ("\nincl_in_edges: dest=%d", dest_nid);
		map<label, set<pt_node_index> > in_edges = iei->second;
		if (in_edges.find (l) == in_edges.end ())
			continue;
		set<pt_node_index> in_nodes = in_edges[l];
		if (in_nodes.find (node_id) != in_nodes.end ())
			dest_nodes.insert (dest_nid);
	}
#else
	if (incl_out_edges.find (node_id) != incl_out_edges.end ())
	{
		map<label, set<pt_node_index> > out_edges = incl_out_edges[node_id];
		if (out_edges.find (l) != out_edges.end ())
			merge_set (out_edges[l], dest_nodes);
	}
#endif

	#if DEBUG_CONTAINER
	DEBUG ("\nFound destinations: ");
	set<pt_node_index>::iterator ni;
	for (ni = out_edge_list[l].begin (); ni != out_edge_list[l].end (); ni++)
		DEBUG ("%d,", *ni);
	#endif

	return !dest_nodes_temp.size ();
}
#endif

/**
 * input: l, stack_id
 * output: dest_nodes, computed_offset
 * @return true if THIS node is not proper variable node (undef/null/readonly)
 * i.e. the out-edge is missing i.e. the destination is undef. 
 */

bool pt_fi_node::
compute_offset (label l, 
	pt_node_index stack_id,
	set<pt_node_index> & dest_nodes,
	label & computed_offset)
{
	computed_offset = l;

	// If THIS is not stack node, then either THIS node represents improper
	// variable or L is a field of THIS node.
	if (node_id != stack_id)
	{
		// Get name of THIS node.
		label node_name = get_node_name (stack_id);
		DEBUG ("\nnode_name=%d", node_name);

		// SUMM_K_CONSISTENT: node with is_summary_node has
		// node_name=wild_card_id which is representing a var and does not
		// pass the following if-condition.
		if (!program.is_repr_var (node_name))
		{
			DEBUG ("\nget_destination_nodes() of node=%d is undef", node_name);
			return true;
		}

		// Set L to the difference of offset of the variable returned
		// by cs_first_vi_for_offset (THIS node's name, l) and the
		// offset of THIS node's variable.
#if SUMM_K_CONSISTENT
		// If L is not WILD_CARD_ID then actually it implies that
		// NODE_NAME is not WILD_CARD_ID and vice versa.
		if (l && l != wild_card_id && node_name != wild_card_id)
#else
		if (l)
#endif
		{
			csvarinfo_t var_info = VEC_index (csvarinfo_t, program.variable_data, node_name);
			DEBUG ("\nvar_info=%s(%d) is at offset %lld",
				var_info->name, var_info->id, var_info->offset);
			csvarinfo_t var_offset_info = program.cs_first_vi_for_offset (var_info, l);
			if (var_offset_info)
			{
				DEBUG ("\nvar_offset_info=%s(%d) is found at offset %lld for l=%d",
					var_offset_info->name, var_offset_info->id, var_offset_info->offset, l);
				if (var_info->offset + l != var_offset_info->offset)
					RESULT ("\nError:! Check: Exact offset not found: var=%lld+l=%d != var_offset=%lld",
						var_info->offset, l, var_offset_info->offset);
				computed_offset = var_offset_info->offset - var_info->offset;
				// If L label was not already 0 and has become
				// 0 (after using cs_first_vi_for_offset()),
				// then THIS node is the destination.
				if (!computed_offset)
				{
					DEBUG ("\nFound destination: %d", node_id);
					dest_nodes.insert (node_id);
					return true;
				}
			}
		}
	}
	return false;
}

/**
 * output: IN_OUT_ADJ_NODES
 */

void pt_fi_node::
get_in_out_adj_nodes (set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & invis_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & invis_out_edges,
	set<pt_node_index> & in_out_adj_nodes,
	set<pt_node_index> & valid_nodes)
{
	map<label, set<pt_node_index> >::iterator ei;
	map<label, set<pt_node_index> > ine;

#if PULL_ACCESS_NAMES
	// Get in nodes of NID due to INVIS_IN_EDGES
	if (invis_in_edges.find (node_id) != invis_in_edges.end ())
		ine = invis_in_edges[node_id];
	for (ei = ine.begin (); ei != ine.end (); ei++)
	{
		// No need to check whether or not INN is valid. This
		// has already been done while computing
		// INVIS_IN_EDGES.
		set<pt_node_index> inn = ei->second;
		// in_out_adj_nodes.insert (inn.begin (), inn.end ());
		merge_set (inn, in_out_adj_nodes);
	}
#else
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator outei;
	for (outei = invis_out_edges.begin (); outei != invis_out_edges.end (); outei++)
	{
		pt_node_index inn = ei->first;
		map<label, set<pt_node_index> > outn_e = outei->second;
		if (outn_e.find (node_id) != outn_e.end ())
			in_out_adj_nodes.insert (inn);
	}
#endif

	// Get in nodes (excluding due to Ekill) of NID
	for (ei = in_edge_list.begin (); ei != in_edge_list.end (); ei++)
	{
		label inl = ei->first;
		set<pt_node_index> inn = ei->second;
		set<pt_node_index>::iterator ni;
		for (ni = inn.begin (); ni != inn.end (); ni++)
		{
			pt_node_index innid = *ni;

			// Ekill
			if (must_lptr.find (innid) != must_lptr.end ()
				&& l == inl)
#if SUMM_K_CONSISTENT
				// We cannot kill on wild_card_id
				if (l != wild_card_id)
#endif
					continue;

			if (!is_node_valid_at_point (innid, valid_nodes))
				continue;
			in_out_adj_nodes.insert (innid);
		}
	}

	// Get out nodes (excluding due to Ekill) of NID
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		label outl = ei->first;

		// Ekill
		if (must_lptr.find (node_id) != must_lptr.end ()
			&& l == outl)
#if SUMM_K_CONSISTENT
			// We cannot kill on wild_card_id
			if (l != wild_card_id)
#endif
				continue;

		set<pt_node_index> outn = ei->second;
		set<pt_node_index>::iterator ni;
		for (ni = outn.begin (); ni != outn.end (); ni++)
		{
			pt_node_index outnid = *ni;
			if (!is_node_valid_at_point (outnid, valid_nodes))
				continue;
			in_out_adj_nodes.insert (outnid);
		}
	}

	// If NID is in LPTR, then add RPTE to AFFECTED_NODES
	if (lptr.find (node_id) != lptr.end ())
	{
		// in_out_adj_nodes.insert (rpte.begin (), rpte.end ());
		merge_set (rpte, in_out_adj_nodes);
	}

	// If NID is in RPTE, then add LPTR to AFFECTED_NODES
	if (rpte.find (node_id) != rpte.end ())
	{
		// in_out_adj_nodes.insert (lptr.begin (), lptr.end ());
		merge_set (lptr, in_out_adj_nodes);
	}
}

/** 
 * This function returns the successor nodes of THIS node using out-edges and
 * Egen (LPTR to RPTR new edges) and invis_in_edges that are present in VALUE.
 */

void pt_fi_node::
get_out_adj_nodes (set<pt_node_index> & lptr,
	set<pt_node_index> & rptr,
	map<pt_node_index, map<label, set<pt_node_index> > > & invis_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & invis_out_edges,
	set<pt_node_index> & out_adj_nodes,
	set<pt_node_index> & valid_nodes)
{
	FUNBEGIN ();

	DEBUG ("\nget_out_adj_nodes()");

	// Consider pre-existing out edges of THIS node
	// Here we do not exclude Ekill edges because the out-nodes reachable
	// via Ekill edges are anyway included by default by the caller of this
	// function get_out_adj_nodes() i.e. find_ans_and_affected_region().
	map<label, set<pt_node_index> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		set<pt_node_index> outn = ei->second;
		get_nodes_valid_at_point (outn, valid_nodes);
		// out_adj_nodes.insert (outn.begin (), outn.end ());
		merge_set (outn, out_adj_nodes);
	}

	// Consider Egen
	if (lptr.find (node_id) != lptr.end ())
	{
		// out_adj_nodes.insert (rptr.begin (), rptr.end ());
		merge_set (rptr, out_adj_nodes);
	}

#if PULL_ACCESS_NAMES
	// Consider invis_in_edges
	DEBUG ("\ninvis_in_edges");
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator inei;
	for (inei = invis_in_edges.begin (); inei != invis_in_edges.end (); inei++)
	{
		pt_node_index dest = inei->first;
		map<label, set<pt_node_index> > ine = inei->second;
		map<label, set<pt_node_index> >::iterator ei;
		for (ei = ine.begin (); ei != ine.end (); ei++)
		{
			set<pt_node_index> src = ei->second;
			if (src.find (node_id) != src.end ())
			{
				out_adj_nodes.insert (dest);
				break;
			}
		}
	}
#else
	// Consider invis_out_edges
	map<label, set<pt_node_index> > invis_nid_out_edges;
	if (invis_out_edges.find (node_id) != invis_out_edges.end ())
		invis_nid_out_edges = invis_out_edges[node_id];
	for (ei = invis_nid_out_edges.begin (); ei != invis_nid_out_edges.end (); ei++)
	{
		set<pt_node_index> invis_out_nodes = ei->second;
		merge_set (invis_out_nodes, out_adj_nodes);
	}
#endif

	RETURN_VOID ();
}

void pt_fi_node::
get_out_adj_nodes (set<pt_node_index> & out_adj_nodes,
	set<pt_node_index> & valid_nodes)
{
	map<label, set<pt_node_index> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		set<pt_node_index> outn = ei->second;
		get_nodes_valid_at_point (outn, valid_nodes);
		// out_adj_nodes.insert (outn.begin (), outn.end ());
		merge_set (outn, out_adj_nodes);
	}
}

/**
 * output: IN_ADJ_NODES
 */

void pt_fi_node::
get_in_adj_nodes (set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & invis_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & invis_out_edges,
	set<pt_node_index> & in_adj_nodes,
	set<pt_node_index> & valid_nodes)
{
	map<label, set<pt_node_index> >::iterator ei;
	map<label, set<pt_node_index> > ine;

#if PULL_ACCESS_NAMES
	// Get in nodes of NID due to INVIS_IN_EDGES
	if (invis_in_edges.find (node_id) != invis_in_edges.end ())
		ine = invis_in_edges[node_id];
	for (ei = ine.begin (); ei != ine.end (); ei++)
	{
		// No need to check whether or not INN is valid. This
		// has already been done while computing
		// INVIS_IN_EDGES.
		set<pt_node_index> inn = ei->second;
		// in_adj_nodes.insert (inn.begin (), inn.end ());
		merge_set (inn, in_adj_nodes);
	}
#else
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator outei;
	for (outei = invis_out_edges.begin (); outei != invis_out_edges.end (); outei++)
	{
		pt_node_index inn = outei->first;
		map<label, set<pt_node_index> > n_out_edges = outei->second;
		for (ei = n_out_edges.begin (); ei != n_out_edges.end (); ei++)
		{
			set<pt_node_index> outn = ei->second;
			if (outn.find (node_id) != outn.end ())
				in_adj_nodes.insert (inn);
		}
	}
#endif

	// Get in nodes (excluding due to Ekill) of NID
	for (ei = in_edge_list.begin (); ei != in_edge_list.end (); ei++)
	{
		label inl = ei->first;
		set<pt_node_index> inn = ei->second;
		set<pt_node_index>::iterator ni;
		for (ni = inn.begin (); ni != inn.end (); ni++)
		{
			pt_node_index innid = *ni;

			// Ekill
			if (must_lptr.find (innid) != must_lptr.end ()
				&& l == inl)
#if SUMM_K_CONSISTENT
				// We cannot kill on wild_card_id
				if (l != wild_card_id)
#endif
					continue;

			if (!is_node_valid_at_point (innid, valid_nodes))
				continue;
			in_adj_nodes.insert (innid);
		}
	}

	// Consider Egen
	// If NID is in RPTE, then add LPTR to AFFECTED_NODES
	if (rpte.find (node_id) != rpte.end ())
	{
		// in_adj_nodes.insert (lptr.begin (), lptr.end ());
		merge_set (lptr, in_adj_nodes);
	}
}

/**
 * This function finds the nodes reachable from THIS node. It also finds the
 * nodes reachable from the reachable fields of the variable that THIS node
 * represents. Note that it excludes unreachable fields.
 */

void pt_fi_node::
mark_reachable_nodes (map<pt_node_index, pt_fi_node *> & nodes_map, 
	set<pt_node_index> & lptr,
	set<pt_node_index> & rptr,
	map<pt_node_index, map<label, set<pt_node_index> > > & invis_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & invis_out_edges,
	set<pt_node_index> & reachable_nodes,
	set<pt_node_index> & valid_nodes)
{
	// No need to check this as get_out_adj_nodes() returns valid nodes only.
	// if (!is_node_valid_at_point (node_id, valid_nodes))
	// {
	// 	DEBUG ("\nDont consider node reachable from %d", node_id);
	//	return;
	// }

        // Return if this node has already been visited
        if (reachable_nodes.find (node_id) != reachable_nodes.end ())
        {
		DEBUG ("\nNodes reachable from %d are already marked", node_id);
		return;
        }

        DEBUG ("\nInserting node %d into par-glob-reachable-nodes", node_id);
        reachable_nodes.insert (node_id);

	// In access based abstraction, where structures are reachable from
	// their field nodes, we do not need to do anything special to insert
	// the field nodes in reachable_nodes; they will get inserted via
	// out_edge_list. 

	set<pt_node_index> out_adj_nodes;
	get_out_adj_nodes (lptr, rptr, invis_in_edges, invis_out_edges, out_adj_nodes, valid_nodes);

	set<pt_node_index>::iterator ni;
	for (ni = out_adj_nodes.begin (); ni != out_adj_nodes.end (); ni++)
	{
		pt_fi_node * n = nodes_map[*ni];
		n->mark_reachable_nodes (nodes_map, lptr, rptr, invis_in_edges, invis_out_edges,
	       		reachable_nodes, valid_nodes);
	}
}

/**     
 * This function inserts a new edge with label L to the node DEST from THIS node.
 * It may lead to making the graph non-deterministic in terms of the labels on
 * the edges.  It also updates the incoming edge list of the DEST node.
 * @returns true if edge is newly added (i.e. did not exist earlier).
 */

bool pt_fi_node::
insert_edge (label l, pt_fi_node & dest, pt_node_index stack_id)
{
#if SUMM_K_CONSISTENT
	if (l != wild_card_id && is_summary_node)
	{
		// A field (non-zero l) is generated either on fresh nodes or
		// on on-the-fly heap nodes. The former cannot be summary nodes
		// (as they are pointed only by stack_id node or via field
		// edges (which do not increase value of K)). The latter could
		// be summary nodes.  This function assumes that this function
		// is called when src=dest. We cannot call insert_edge
		// (wild_card_id, *this, stack_id); on our own because this could
		// lead to unsafe results when DEST remains unaliased with its
		// root heap node but is added to rhs nodes and forms alias
		// with lhs. 
		// if (l) insert_edge (wild_card_id, *this, stack_id);
		if (node_id != dest.node_id)
		{
			RESULT ("\nError: out-edge of summary node=%d is node=%d", 
				node_id, dest.node_id);
			return;
		}

		return insert_edge (wild_card_id, dest, stack_id);
	}
#endif

	DEBUG ("\nInserting edge from %d -> %d -> %d", node_id, l, dest.node_id);
	DEBUG ("\nStack id=%d", stack_id);
	
	// Do not add any out edge from an improper node
	label node_name = get_node_name (stack_id);
	// If THIS is not stack and THIS is improper variable node, then do not
	// insert edge.
	// The in-edges of THIS node may not have been created from its clone
	// as yet. Therefore, name may still not exist. Therefore, skip edge
	// creation only if node_name is non-zero.
	// SUMM_K_CONSISTENT: node with is_summary_node has node_name=wild_card_id
	// which represents a var and does not pass the following if-condition.
	if (node_name && stack_id != node_id && !program.is_repr_var (node_name))
	{
		DEBUG ("\nDo not insert edge from node=%d node_name=%d", node_id, node_name);
		return false;
	}

	bool is_edge_new = false;
	if (out_edge_list.find (l) == out_edge_list.end ())
		is_edge_new = true;
	else if (out_edge_list[l].find (dest.node_id) == out_edge_list[l].end ())
		is_edge_new = true;

	DEBUG ("\nOld out-edge-list from node=%d via l=%d, count=%d", node_id, l, out_edge_list[l].size ());
	out_edge_list[l].insert (dest.node_id);
	dest.in_edge_list[l].insert (node_id);
	DEBUG ("\nNew out-edge-list from node=%d via l=%d, count=%d", node_id, l, out_edge_list[l].size ());

	return is_edge_new;
}

int pt_fi_node::
count_in_edges ()
{
	int no_of_in_edges = 0;
	map<label, set<pt_node_index> >::iterator in_edge_i;
	for (in_edge_i = in_edge_list.begin(); in_edge_i != in_edge_list.end(); in_edge_i++)
	{
		no_of_in_edges += in_edge_i->second.size ();
	}
	return no_of_in_edges;
}

int pt_fi_node::
count_out_edges ()
{
	int no_of_out_edges = 0;
	map<label, set<pt_node_index> >::iterator out_edge_i;
	for (out_edge_i = out_edge_list.begin(); out_edge_i != out_edge_list.end(); out_edge_i++)
	{
		no_of_out_edges += out_edge_i->second.size ();
	}
	return no_of_out_edges;
}

void pt_fi_node::
get_points_to_pairs (set<pt_node_index> & pt_nodes, 
	map<label, set<label> > & points_to_pairs, 
	map<label, set<label> > & summ_stack_to_stack_pointers,
	map<pt_node_index, pt_fi_node *> & nodes, 
	pt_node_index stack_id)
{
#if SUMM_K_CONSISTENT
	set<label> ptr_ids;
	get_all_names (stack_id, ptr_ids);
#else
	label ptr_id = get_node_name (stack_id);
#endif

	map<label, set<pt_node_index> >::iterator out_edge_i;
	for (out_edge_i = out_edge_list.begin(); out_edge_i != out_edge_list.end(); out_edge_i++)
	{
		label l = out_edge_i->first;

#if SUMM_K_CONSISTENT
		if (l != stack_deref && l != wild_card_id)
			continue;
#else
		if (l != stack_deref)
			continue;
#endif

		set<pt_node_index>::iterator si;
		set<pt_node_index> out_nodes = out_edge_i->second;
		for (si = out_nodes.begin (); si != out_nodes.end (); si++)
		{
			pt_node_index pte_nid = *si;
			if (pt_nodes.find (pte_nid) == pt_nodes.end ())
				continue;

			pt_fi_node * pte_n = nodes[pte_nid];

#if SUMM_K_CONSISTENT
			set<label> pte_ids;
			pte_n->get_all_names (stack_id, pte_ids);
			set<label>::iterator pri;
			set<label>::iterator pei;
			for (pri = ptr_ids.begin (); pri != ptr_ids.end (); pri++)
				for (pei = pte_ids.begin (); pei != pte_ids.end (); pei++)
				{
					points_to_pairs[*pri].insert (*pei);
					if (is_summary_node && !program.heap_var (*pri) && !program.heap_var (*pei))
						summ_stack_to_stack_pointers[*pri].insert (*pei);
				}
#else
			label pte_id = pte_n->get_node_name (stack_id);
			points_to_pairs[ptr_id].insert (pte_id);
#endif
		}
	}
}

#if SUMM_K_CONSISTENT
void pt_fi_node::
get_all_varinfos (pt_node_index stack_index, set<csvarinfo_t> & ps)
{
	set<label> p_ids;
	get_all_names (stack_index, p_ids);
	if (node_id != stack_index && !p_ids.size ())
	{
		RESULT ("\nError: Pointer is stack_deref");
		return;
	}
	set<label>::iterator pi;
	for (pi = p_ids.begin (); pi != p_ids.end (); pi++)
	{
		csvarinfo_t p = VEC_index (csvarinfo_t, program.variable_data, *pi);
		if (!p)
			continue;
		ps.insert (p);
	}
}
#endif

void pt_fi_node::
get_node_varinfo (pt_node_index stack_index, csvarinfo_t & p)
{
	label p_id = get_node_name (stack_index);
	if (node_id != stack_index && p_id == stack_deref)
	{
		RESULT ("\nError: Pointer is stack_deref");
		return;
	}
	p = VEC_index (csvarinfo_t, program.variable_data, p_id);
	if (!p)
		return;
}

set<pt_node_index> pt_fi_node::
print_node_pointers (FILE * file, set<pt_node_index> & pt_nodes, map<pt_node_index, pt_fi_node *> & nodes, pt_node_index stack_index)
{
	DEBUG ("\npt_fi_node::print_node (), node %d", node_id);
	set<pt_node_index> ptr_pte;

#if SUMM_K_CONSISTENT
	set<csvarinfo_t> ptrs;
	get_all_varinfos (stack_index, ptrs);
	if (!ptrs.size ())
		return ptr_pte;
#else
	csvarinfo_t ptr = NULL;
	get_node_varinfo (stack_index, ptr);
	if (!ptr)
		return ptr_pte;
#endif

	map<label, set<pt_node_index> >::iterator out_edge_i;
	for (out_edge_i = out_edge_list.begin(); out_edge_i != out_edge_list.end(); out_edge_i++)
	{
		label l = out_edge_i->first;
		DEBUG ("\nout-edge l=%d", l);
		DEBUG ("\nnumber of out-nodes=%d", out_edge_i->second.size ());

#if SUMM_K_CONSISTENT
		if (l != stack_deref && l != wild_card_id)
			continue;
#else
		if (l != stack_deref)
			continue;
#endif

		set<pt_node_index>::iterator si;
		for (si = out_edge_i->second.begin (); si != out_edge_i->second.end (); si++)
		{
			DEBUG ("\nout-node %d", *si);
			pt_node_index pte_nid = *si;
			if (pt_nodes.find (pte_nid) == pt_nodes.end ())
				continue;

			RESULT ("\n");
			if (file)
				fprintf (file, "\n");

			pt_fi_node * pte_n = nodes[pte_nid];

#if SUMM_K_CONSISTENT
			set<csvarinfo_t> ptes;
			pte_n->get_all_varinfos (stack_index, ptes);
			if (!ptes.size ())
				continue;
			ptr_pte.insert (node_id);
			ptr_pte.insert (pte_nid);

			set<csvarinfo_t>::iterator pri;
			set<csvarinfo_t>::iterator pei;
			for (pri = ptrs.begin (); pri != ptrs.end (); pri++)
			{
				csvarinfo_t ptr = *pri;
				for (pei = ptes.begin (); pei != ptes.end (); pei++)
				{
					csvarinfo_t pte = *pei;
					if (file)
						fprintf (file, "\"%s\" -> \"%s\"", ptr->name, pte->name);
					RESULT ("\n%s(%d,%d) -> %s(%d,%d)", ptr->name, ptr->id, node_id,
						pte->name, pte->id, pte_n->node_id);
				}
			}

#else
			csvarinfo_t pte = NULL;
			pte_n->get_node_varinfo (stack_index, pte);
			if (!pte)
				continue;
			ptr_pte.insert (node_id);
			ptr_pte.insert (pte_nid);

			if (file)
				fprintf (file, "\"%s\" -> \"%s\"", ptr->name, pte->name);
			if (ptr->is_global_var)
			{
				RESULT ("# %s(%d,%d) -> %s(%d,%d)", ptr->name, ptr->id, node_id,
					pte->name, pte->id, pte_nid);
			}
			else
			{
				RESULT ("%s(%d,%d) -> %s(%d,%d)", ptr->name, ptr->id, node_id,
					pte->name, pte->id, pte_nid);
			}
#endif
		}
	}

	return ptr_pte;
}

void pt_fi_node::
get_node_fields (set<pt_node_index> & pt_nodes, 
	map<pt_node_index, set<pair<label, pt_node_index> > > & field_edges)
{
	DEBUG ("\npt_fi_node::get_node_fields (), node %d", node_id);

	map<label, set<pt_node_index> >::iterator out_edge_i;
	for (out_edge_i = out_edge_list.begin(); out_edge_i != out_edge_list.end(); out_edge_i++)
	{
		label l = out_edge_i->first;
		DEBUG ("\nout-edge l=%d", l);
		DEBUG ("\nnumber of out-nodes=%d", out_edge_i->second.size ());

		if (l == stack_deref)
			continue;

		set<pt_node_index>::iterator si;
		for (si = out_edge_i->second.begin (); si != out_edge_i->second.end (); si++)
		{
			DEBUG ("\nout-node %d", *si);
			pt_node_index pte_nid = *si;
			if (pt_nodes.find (pte_nid) == pt_nodes.end ())
				continue;

			field_edges[node_id].insert (make_pair (l, pte_nid));
		}
	}
}

void pt_fi_node::
print_node (FILE * file, map<pt_node_index, pt_fi_node *> & nodes, bool print_dump_file)
{
	DEBUG ("\npt_fi_node::print_node (), node %d", node_id);

	map<label, set<pt_node_index> >::iterator out_edge_i;
	for (out_edge_i = out_edge_list.begin(); out_edge_i != out_edge_list.end(); out_edge_i++)
	{
		label l = out_edge_i->first;
		DEBUG ("\nout-edge l=%d", l);
		DEBUG ("\nnumber of out-nodes=%d", out_edge_i->second.size ());

		set<pt_node_index>::iterator si;
		for (si = out_edge_i->second.begin (); si != out_edge_i->second.end (); si++)
		{
			DEBUG ("\nout-node %d", *si);
			if (print_dump_file)
				RESULT ("\n");
			if (file)
				fprintf (file, "\n");

			pt_fi_node * dest_node = NULL;
			if (nodes.find (*si) != nodes.end ())
				dest_node = nodes[*si];
			int no_of_in_edges = 0;
			int no_of_out_edges = 0;
			if (dest_node)
			{
				no_of_in_edges = dest_node->count_in_edges ();
				no_of_out_edges = dest_node->count_out_edges ();
			}

			// Do not extract name of edge label if THIS is stack node
			csvarinfo_t variable = NULL;
			if (!in_edge_list.size ())
				variable = VEC_index (csvarinfo_t, program.variable_data, l);
#if DEBUG_CONTAINER
			if (l != stack_deref && variable)
			{
				DEBUG ("%d(%x) -> %s (%d) -> %d(%x) \t#%d(in) \t#%d(out)",
					node_id, this, variable->name, l, *si, dest_node, no_of_in_edges, no_of_out_edges);
			}
			else
			{
				DEBUG ("%d(%x) -> %d -> %d(%x) \t#%d(in) \t#%d(out)",
					node_id, this, l, *si, dest_node, no_of_in_edges, no_of_out_edges);
			}
#endif

			if (l != stack_deref && variable)
			{
				if (file)
					fprintf (file, "\"%d\" -> \"%d\" [label=\"%s(%d)\"]",
					node_id, *si, variable->name, l);

				if (print_dump_file)
					RESULT ("%d -> %s (%d) -> %d \t#%d(in) \t#%d(out)",
					node_id, variable->name, l, *si, no_of_in_edges, no_of_out_edges);
			}
			else
			{
				if (file)
					fprintf (file, "\"%d\" -> \"%d\" [label=\"%d\"]",
					node_id, *si, l);
				if (print_dump_file)
					RESULT ("%d -> %d -> %d #%d",
					node_id, l, *si, no_of_in_edges);
			}
		}
	}
}

void pt_fi_node::
print_node_reverse (FILE * file)
{
//#if 0
	DEBUG ("\npt_fi_node::print_node_reverse () %d", node_id);
	map<label, set<pt_node_index> >::iterator in_edge_i;
	for (in_edge_i = in_edge_list.begin(); in_edge_i != in_edge_list.end(); in_edge_i++)
	{
		label l = in_edge_i->first;

		if (in_edge_i->second.begin () == in_edge_i->second.end ())
		{
			RESULT ("\nError: Node %d has in edge with label %d, but without any source node",
				node_id, l);
			RESULT ("--size=%d", in_edge_i->second.size ());
		}

		set<pt_node_index>::iterator si;
		for (si = in_edge_i->second.begin (); si != in_edge_i->second.end (); si++)
			// Do not extract name of edge label since it may be a member field.
			RESULT ("\n%d <- %d <- %d", node_id, l, *si);
	}
//#endif
}

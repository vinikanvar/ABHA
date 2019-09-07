
/************************
 * @author Vini Kanvar
************************/

#include "ap_fi_node.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

// We assume that node index 0 does not exist
unsigned int ap_fi_node::
number_of_nodes = 1;


ap_fi_node::
ap_fi_node ()
{
	RESULT ("\nError: ap_fi_node constructor should be called with nodes");
}

ap_fi_node::
ap_fi_node (map<ap_node_index, ap_fi_node *> & nodes)
{
	node_id = number_of_nodes;
	nodes[node_id] = this;
	number_of_nodes++;

	in_edge_label = 0;
	in_node_id = 0;

#if SUMM_K_FILTER || SUMM_K_PREFIX
	ap_len = 0;
#endif

	DEBUG ("\nAdded ap_fi_node %d,%x", node_id, this);
}

ap_fi_node::
~ap_fi_node ()
{
	DEBUG ("\nDeleting ap_fi_node %d(%x)", node_id, this);
}

unsigned int ap_fi_node::
get_node_id ()
{
	return node_id;
}

#if SUMM_STMT_CLOSURE
map<label, pair<def_stmt_set, ap_node_index> > ap_fi_node::
get_out_edge_list ()
{
	return out_edge_list;
}
#endif

#if SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
map<pair<label, type>, ap_node_index> ap_fi_node::
get_out_edge_list ()
{
	return out_edge_list;
}
#endif

#if gAP_CYCLIC && SUMM_TYPE_K
map<pair<label, type>, ap_node_index> ap_fi_node::
get_out_cyclic_edge_list ()
{
	return out_cyclic_edge_list;
}
#endif

#if SUMM_TYPE_CLOSURE || SUMM_K_CONSISTENT
map<label, ap_node_index> ap_fi_node::
get_out_edge_list ()
{
	return out_edge_list;
}
#endif

label ap_fi_node::
get_in_edge_label ()
{
	return in_edge_label;
}

ap_node_index ap_fi_node::
get_in_node_id ()
{
	return in_node_id;
}

#if gAP_CYCLIC && SUMM_TYPE_K
set<ap_node_index> ap_fi_node::
get_in_cyclic_node_ids ()
{
	return in_cyclic_node_ids;
}
#endif

#if SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
type ap_fi_node::
get_static_name ()
{
	return static_name;
}
#endif

#if SUMM_STMT_CLOSURE
def_stmt_set ap_fi_node::
get_def_stmt_set (label l)
{
	// This is not an error. We call this function for initialization of
	// newly created stack and global nodes. The edge may not exist also
	// when it has a stmt id repeating before.
	if (out_edge_list.find (l) == out_edge_list.end ())
	{
		DEBUG ("\nEdge ap-node=%d->l=%d not found", node_id, l);
		def_stmt_set ds;
		return ds;
	}
	return out_edge_list[l].first;
}
#endif

#if SUMM_TYPE_CLOSURE
set<label> ap_fi_node::
get_static_names ()
{
	return  static_names;
}
#endif

#if SUMM_K_FILTER || SUMM_K_PREFIX
unsigned int ap_fi_node::
get_ap_len ()
{
	return ap_len;
}
#endif

/** 
 * Get destination nodes via acyclic and cyclic out edges.
 */

#if SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
set<ap_node_index> ap_fi_node::
get_destination_nodes (label l)
{
	set<ap_node_index> dests;

	map<pair<label, type>, ap_node_index>::iterator oute;
	for (oute = out_edge_list.begin (); oute != out_edge_list.end (); oute++)
	{
		label el = oute->first.first;
		if (el != l)
			continue;
		ap_node_index dest = oute->second;
		dests.insert (dest);
	}

#if gAP_CYCLIC
	map<pair<label, type>, ap_node_index>::iterator outce;
	for (outce = out_cyclic_edge_list.begin (); outce != out_cyclic_edge_list.end (); outce++)
	{
		label el = outce->first.first;
		if (el != l)
			continue;
		ap_node_index dest = outce->second;
		dests.insert (dest);
	}
#endif

	return dests;
}
#endif

/** 
 * Get destination node via acyclic and cyclic out edges.
 */

#if SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
ap_node_index ap_fi_node::
get_destination_node (label l, type t)
{
	map<pair<label, type>, ap_node_index>::iterator oute;
	if (out_edge_list.find (make_pair (l, t)) != out_edge_list.end ())
	{
		ap_node_index dest = out_edge_list[make_pair (l, t)];
		return dest;
	}

#if gAP_CYCLIC
	map<pair<label, type>, ap_node_index>::iterator outce;
	if (out_cyclic_edge_list.find (make_pair (l, t)) != out_cyclic_edge_list.end ())
	{
		ap_node_index dest = out_cyclic_edge_list[make_pair (l, t)];
		return dest;
	}
#endif

	return 0;
}
#endif

/** 
 * Get destination node via acyclic out edges.
 */

#if SUMM_STMT_CLOSURE
ap_node_index ap_fi_node::
get_destination_node (label l)
{
	if (out_edge_list.find (l) == out_edge_list.end ())
		return 0;
	ap_node_index dest = out_edge_list[l].second;
	return dest;
}
#endif

/**
 * Get out node via acyclic out-edges.
 */

#if SUMM_STMT_CLOSURE
ap_node_index ap_fi_node::
get_destination_node (label l, def_stmt s)
{
	DEBUG ("\nget_edge (ap-node=%d, l=%d)", node_id, l);

	def_stmt_set ds;
	if (out_edge_list.find (l) == out_edge_list.end ())
		return 0;
	DEBUG ("\nlabel=%d exists", l);

	ds = out_edge_list[l].first;

	if (ds.find (s) == ds.end ())
		return 0;

	ap_node_index dest_nid = out_edge_list[l].second;
	DEBUG ("\nFound dest=%d", dest_nid);
	return dest_nid;
}
#endif

/** 
 * Get destination node via acyclic out edges.
 */

#if SUMM_TYPE_CLOSURE || SUMM_K_CONSISTENT 
ap_node_index ap_fi_node::
get_destination_node (label l)
{
	if (out_edge_list.find (l) == out_edge_list.end ())
		return 0;
	ap_node_index dest = out_edge_list[l];
	return dest;
}
#endif

/**
 * Get nodes reachable via acyclic out-edges.
 */

#if SUMM_K_CONSISTENT
void ap_fi_node::
get_reachable_nodes (set<ap_node_index> & reachable_nodes)
{
	map<label, ap_node_index>::iterator ei;

	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		ap_node_index outn = ei->second;
		reachable_nodes.insert (outn);
	}
}
#endif

#if SUMM_TYPE_CLOSURE
void ap_fi_node::
add_static_name (label static_name)
{
	static_names.insert (static_name);
}
#endif

#if gAP_CYCLIC && SUMM_TYPE_K
void ap_fi_node::
add_out_cyclic_node_ids (map<ap_node_index, set<ap_node_index> > & out_cyclic_edges)
{
	if (out_cyclic_node_ids.size ())
		out_cyclic_edges[node_id].insert (out_cyclic_node_ids.begin (), out_cyclic_node_ids.end ());
}
#endif

#if SUMM_STMT_CLOSURE
void ap_fi_node::
insert_edge (label l, def_stmt s, ap_fi_node & dest_node)
{
	ap_node_index dest_id = dest_node.node_id;
	DEBUG ("\nap insert_edge %d->l=%d,s=%d->%d", node_id, l, s, dest_id);

	pair<def_stmt_set, ap_node_index> old_sn_out = out_edge_list[l];
	DEBUG ("\nold edge %d->l=%d->%d", node_id, l, old_sn_out.second);

	ap_node_index old_dest_id = old_sn_out.second;
	if (old_dest_id && old_dest_id != dest_id)
	{
		RESULT ("\nError: ap-node %d->l=%d is non-deterministic to %d and %d", 
			node_id, l, old_dest_id, dest_id);
		return;
	}

	// if (s != DONT_CARE)
	old_sn_out.first.insert (s);
	old_sn_out.second = dest_id;
	out_edge_list[l] = old_sn_out;
	
	dest_node.in_edge_label = l;
	dest_node.in_node_id = node_id;
}
#endif

#if (SUMM_TYPE_K && !gAP_CYCLIC) || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
void ap_fi_node::
insert_edge (label l, type t, ap_fi_node & dest_node)
{
	ap_node_index dest_id = dest_node.node_id;
	DEBUG ("\nap insert_edge %d->l=%d,t=%d->%d", node_id, l, t, dest_id);

	ap_node_index old_dest_id = get_destination_node (l, t);
	DEBUG ("\nold edge %d->l=%d,t=%d->%d", node_id, l, t, old_dest_id);

	if (old_dest_id && old_dest_id != dest_id)
	{
		RESULT ("\nError: ap-node %d->l=%d,t=%d is non-deterministic to %d and %d", 
			node_id, l, t, old_dest_id, dest_id);
		return;
	}

	out_edge_list[make_pair (l, t)] = dest_id;
	dest_node.in_edge_label = l;
	dest_node.static_name = t;
	dest_node.in_node_id = node_id;

#if SUMM_K_FILTER || SUMM_K_PREFIX
#if K_FIELDS == 0
	// Increment count if it is a pointer i.e. the location accessible via
	// this access path can hold an address.
	if (!l)
		dest_node.ap_len = ap_len + 1;
	else
		dest_node.ap_len = ap_len;
#else
	dest_node.ap_len = ap_len + 1;
#endif
#endif
}
#endif

#if SUMM_TYPE_K && gAP_CYCLIC
void ap_fi_node::
insert_edge (label l, type t, ap_fi_node & dest_node, bool is_cyclic)
{
	ap_node_index dest_id = dest_node.node_id;
	DEBUG ("\nap insert_edge %d->l=%d,t=%d->%d", node_id, l, t, dest_id);

	ap_node_index old_dest_id = get_destination_node (l, t);
	DEBUG ("\nold edge %d->l=%d,t=%d->%d", node_id, l, t, old_dest_id);

	if (old_dest_id && old_dest_id != dest_id)
	{
		RESULT ("\nError: ap-node %d->l=%d,t=%d is non-deterministic to %d and %d", 
			node_id, l, t, old_dest_id, dest_id);
		return;
	}

	if (is_cyclic)
	{
		out_cyclic_edge_list[make_pair (l, t)] = dest_id;
		out_cyclic_node_ids.insert (dest_id);
	}
	else
		out_edge_list[make_pair (l, t)] = dest_id;

	// If dest_node already had an in-edge, check that old (l,t) in-edge is
	// same as the new (l,t).
	if (dest_node.in_node_id)
	{
		if (dest_node.in_edge_label != l)
			RESULT ("\nError: Dest=%d, old-in-l=%d, new-in-l=%d", 
				dest_id, dest_node.in_edge_label, l);
		if (dest_node.static_name != t)
			RESULT ("\nError: Dest=%d, old-t=%d, new-t=%d", 
				dest_id, dest_node.static_name, t);
	}

	dest_node.in_edge_label = l;
	dest_node.static_name = t;
	if (is_cyclic)
		dest_node.in_cyclic_node_ids.insert (node_id);
	else
		dest_node.in_node_id = node_id;
}
#endif

#if SUMM_TYPE_CLOSURE || SUMM_K_CONSISTENT
void ap_fi_node::
insert_edge (label l, ap_fi_node & dest_node)
{
	ap_node_index dest_id = dest_node.node_id;
	DEBUG ("\nap insert_edge %d->l=%d->%d", node_id, l, dest_id);

	ap_node_index old_dest_id = out_edge_list[l];
	DEBUG ("\nold edge %d->l=%d->%d", node_id, l, old_dest_id);

	if (old_dest_id && old_dest_id != dest_id)
	{
		RESULT ("\nError: ap-node %d->l=%d is non-deterministic to %d and %d", 
			node_id, l, old_dest_id, dest_id);
		return;
	}

	out_edge_list[l] = dest_id;
	dest_node.in_edge_label = l;
	dest_node.in_node_id = node_id;
}
#endif

#if gAP_CYCLIC && SUMM_TYPE_K
void ap_fi_node::
print_cyclic_edges ()
{
	map<pair<label, type>, ap_node_index>::iterator out_cedge_i;
	for (out_cedge_i = out_cyclic_edge_list.begin(); out_cedge_i != out_cyclic_edge_list.end(); out_cedge_i++)
	{
		label l = out_cedge_i->first.first;
		type t = out_cedge_i->first.second; 
		DEBUG ("\ncyclic edge label l=%d,t=%d", l, t);

		ap_node_index dest_nid = out_cedge_i->second;

		RESULT ("\n");
		RESULT ("%d -> %d,%d", node_id, l, t);
		RESULT (" -> %d", dest_nid);
	}
}
#endif

void ap_fi_node::
print_node (FILE * file)
{
	DEBUG ("\nap_fi_node::print_node (), node %d", node_id);

	DEBUG ("\nnode=%d,in_edge_label=%d", node_id, in_edge_label);
#if SUMM_STMT_CLOSURE
	map<label, pair<def_stmt_set, ap_node_index> >::iterator out_edge_i;
#elif SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
	map<pair<label, type>, ap_node_index>::iterator out_edge_i;
#else
	map<label, ap_node_index>::iterator out_edge_i;
#endif

	for (out_edge_i = out_edge_list.begin(); out_edge_i != out_edge_list.end(); out_edge_i++)
	{
#if SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
		label l = out_edge_i->first.first;
		type t = out_edge_i->first.second; 
#else
		label l = out_edge_i->first;
#endif
		DEBUG ("\nedge label l=%d", l);

#if SUMM_STMT_CLOSURE
		def_stmt_set ds = out_edge_i->second.first;	
		ap_node_index dest_nid = out_edge_i->second.second;
#else
		ap_node_index dest_nid = out_edge_i->second;
#endif

		RESULT ("\n");
		if (file)
			fprintf (file, "\n");

		// Extract name of edge label only if THIS is stack node
		csvarinfo_t variable = NULL;
		if (!in_edge_label)
		;//	variable = VEC_index (csvarinfo_t, program.variable_data, f);

		if (file)
			fprintf (file, "\"%d\" -> \"%d\" [label=\"", node_id, dest_nid);
		if (l != stack_deref && variable)
		{
#if SUMM_TYPE_K
			RESULT ("%d -> %s(%d),%d", node_id, variable->name, l, t);
#else
			RESULT ("%d -> %s(%d)", node_id, variable->name, l);
#endif
			if (file)
				fprintf (file, "%s(%d)", variable->name, l);
		}
		else
		{
#if SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
			RESULT ("%d -> %d,%d", node_id, l, t);
#else
			RESULT ("%d -> %d", node_id, l);
#endif
			if (file)
				fprintf (file, "%d", l);
		}

#if SUMM_STMT_CLOSURE
		DEBUG ("\nPrinting gimple");
		RESULT (",{");
		if (file)
			fprintf (file, ",{");

		def_stmt_set::iterator si;
		for (si = ds.begin (); si != ds.end (); si++)
		{
			RESULT ("%d,", *si);
			if (file)
				fprintf (file, "%d,", *si);
		}		

		RESULT ("}");
		if (file)
			fprintf (file, "}");
#endif
		RESULT (" -> %d", dest_nid);
		if (file)
			fprintf (file, "\"];");
	}

#if gAP_CYCLIC && SUMM_TYPE_K
	print_cyclic_edges ();
#endif

	// Printing in-edges

	if (!in_edge_label)
		return;

	if (file)
		fprintf (file, "\n\"%d\" -> \"%d\" [label=\"%d\"];", 
			in_node_id, node_id, in_edge_label);
}

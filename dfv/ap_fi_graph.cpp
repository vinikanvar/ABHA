
/************************
 * @author Vini Kanvar
************************/

#include "ap_fi_graph.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

ap_fi_graph::
ap_fi_graph () : stack (nodes)
{
	DEBUG ("\ngraph::nodes %x", &nodes);
}

ap_fi_graph::
~ap_fi_graph ()
{
	// TODO: Check and call this function

	map<ap_node_index, ap_fi_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); )
	{
		ap_fi_node * n = ni->second;
		if (n == &stack)
		{
			ni++;
			continue;
		}
		nodes.erase (ni++);
		delete n;
	}
}

bool ap_fi_graph::
is_variable_node (ap_node_index nid)
{
	if (nid == stack.get_node_id ())
		return false;

	ap_fi_node * n = nodes[nid];
	ap_node_index in_nid = n->get_in_node_id ();
	if (in_nid == stack.get_node_id ())
		return true;

	return false;
}

bool ap_fi_graph::
is_heap_node (ap_node_index nid)
{
	if (nid == stack.get_node_id ())
		return false;

	if (!is_variable_node (nid))
		return false;

	ap_fi_node * n = nodes[nid];
	label l = n->get_in_edge_label ();
	if (program.heap_var (l))
		return true;
	return false;	
}

#if SUMM_STMT_CLOSURE
def_stmt_set ap_fi_graph::
get_in_def_stmt_set (ap_fi_node & n)
{
	label in_edge_label = n.get_in_edge_label ();
	ap_node_index in_node_id = n.get_in_node_id ();
	ap_fi_node * in_n = nodes[in_node_id];
	// FIXME: replace the following two lines with get_in_def_stmt_set() for efficiency.
	map<label, pair<def_stmt_set, ap_node_index> > in_n_oute = in_n->get_out_edge_list ();
	def_stmt_set in_def_stmt_set = in_n_oute[in_edge_label].first;
	return in_def_stmt_set;
}
#endif

/**
 * Update THIS graph by inserting the edge <p,l,ds,dest_nid> where dest_nid
 * either already exists or is newly created by this function. 
 * output: DEST_AP_NODES, DEST_AP_UNBOUNDED
 */

#if SUMM_STMT_CLOSURE
void ap_fi_graph::
update (ap_node_index ap_nid, 
	label l, 
	def_stmt_set ds,
	ap_node_index & dest_ap_node,
	bool & dest_ap_unbounded)
{
	DEBUG ("\nupdate (pt-node=%d, l=%d)", ap_nid, l);

	// (1) If still DS is empty, it means that the edge pt_nid->l has been
	// created in gAP_c.
	// FIXME: (2) There could be a case where get_def_stmt_set() returns
	// non-empty DS, but destination of PT_NID->L was also an unbounded
	// access path (that is why it is not stored in gAP_c). Then
	// dest_access_name.ap_unbounded should be set to true.  
	// (3) There could also be a case where free unused heap node has
	// out-edge; therefore, the out-node of the free unused heap node will
	// not have AP via this edge.  However, when a variable points to the
	// free unused node, it will not be able to find DS on the edge to
	// reach the out-node. But this is not an error since a free unused
	// node should any way not have any out-edge.
	if (!ds.size ())
	{
		// If PT_NID is a fresh node (unused and should actually be
		// garbage collected), then destination node is not to be
		// considered unbounded. But since AP_NID has been found for
		// PT_NID, it means PT_NID is not a fresh node.
		#if INTERMEDIATE_RESULT
		RESULT ("\n(1)pnid_ap_unbounded=true of ap_nid=%d,l=%d", ap_nid, l);
		#endif
		dest_ap_node = 0;
		dest_ap_unbounded = true;
		return;
	}

	// if (!ds.size ())
	// {
	//	RESULT ("\nError: Defining statement id is empty for ap-node=%d->l=%d",
	//		ap_nid, l);
	//	return;
	// }

	ap_fi_node * p = nodes[ap_nid];
	if (!p)
	{
		RESULT ("\nError: Node index %d not found", ap_nid);
		dest_ap_node = 0;
		return;
	}

	def_stmt_set::iterator si;
	ap_node_index dest_nid = 0;
	// It is possible that s1 in ds, new_dest_nid is non-repeating node.
	// But on s2 in ds, new_dest_nid is 0 because the edge on s2 repeats.
	// We will create ap-edge from p to new_dest_nid via l on only s1.
	for (si = ds.begin (); si != ds.end (); si++)
	{
		def_stmt s = *si;
		ap_node_index new_dest_nid = update_edge (*p, l, s);

		// If dest nid is not found/created in g_ap, then p->l
		// access path creates an unbounded access path.
		// For SUMM_K_PREFIX: ap_unbounded is never true as destination
		// is always found. A destination representing an AP of K
		// length itself implies that ap_unbounded is true. But this is
		// not explicitly set.
		if (!new_dest_nid)
			dest_ap_unbounded = true;

		if (dest_nid && new_dest_nid && new_dest_nid != dest_nid)
		{
			RESULT ("\nError: ap_fi_graph is non-deterministic on ap-node=%d->l=%d",
				ap_nid, l);
			dest_ap_node = 0;
			return;
		}
		if (new_dest_nid)
		{
			dest_nid = new_dest_nid;
			DEBUG ("\nUpdated in-edge of node %d", dest_nid);
		}
	}
	dest_ap_node = dest_nid;
}
#endif

#if SUMM_TYPE_K && !gAP_CYCLIC
void ap_fi_graph::
update (ap_node_index ap_nid, 
	label l, 
	type t,
	ap_node_index & dest_ap_node,
	bool & dest_ap_unbounded)
{
	ap_fi_node * p = nodes[ap_nid];
	if (!p)
	{
		RESULT ("\nError: Node index %d not found", ap_nid);
		return;
	}

	dest_ap_node = update_edge (*p, l, t);
	if (!dest_ap_node)
		dest_ap_unbounded = true;
}
#endif

#if SUMM_TYPE_K && gAP_CYCLIC
void ap_fi_graph::
update (ap_node_index ap_nid, 
	label l, 
	type t,
	ap_node_index & dest_ap_node,
	bool & dest_ap_unbounded,
	g_ap_cyclic_edges & dest_cyclic_edges)
{
	FUNBEGIN ();

	DEBUG ("\nupdate(ap_nid=%d,l=%d,t=%d)", ap_nid, l, t);

	ap_fi_node * p = nodes[ap_nid];
	if (!p)
	{
		RESULT ("\nError: Node index %d not found", ap_nid);
		RETURN_VOID ();
		// return;
	}

	pair<ap_node_index, bool> dest_nid_ce;
	dest_nid_ce = update_edge (*p, l, t);
	dest_ap_node = dest_nid_ce.first;
	bool is_out_cyclic = dest_nid_ce.second;
	if (is_out_cyclic)
		dest_cyclic_edges[ap_nid].insert (dest_ap_node);

	// In gAP_CYCLIC, dest_ap_node is never 0.
	if (!dest_ap_node)
		RESULT ("\nError: src=%d->l=%d,t=%d->dest=0", ap_nid, l, t);
	// if (!dest_ap_node)
	//	dest_ap_unbounded = true;
	if (dest_cyclic_edges.size ())
		dest_ap_unbounded = true;

	RETURN_VOID ();
}
#endif

#if SUMM_TYPE_CLOSURE || SUMM_K_FILTER || SUMM_K_PREFIX || SUMM_K_CONSISTENT 
void ap_fi_graph::
update (ap_node_index ap_nid, 
	label l, 
	type t,
	ap_node_index & dest_ap_node,
	bool & dest_ap_unbounded)
{
	ap_fi_node * p = nodes[ap_nid];
	if (!p)
	{
		RESULT ("\nError: Node index %d not found", ap_nid);
		return;
	}

#if SUMM_TYPE_CLOSURE || SUMM_K_CONSISTENT 
	dest_ap_node = update_edge (*p, l);
#elif SUMM_K_FILTER || SUMM_K_PREFIX 
	dest_ap_node = update_edge (*p, l, t);
#endif
	if (!dest_ap_node)
		dest_ap_unbounded = true;
}
#endif

#if SUMM_POINTED_TO_BY
void ap_fi_graph::
update (ap_node_index ap_nid, 
	label l, 
	type t,
	ap_node_index & dest_ap_node)
{
	ap_fi_node * p = nodes[ap_nid];
	if (!p)
	{
		RESULT ("\nError: Node index %d not found", ap_nid);
		return;
	}

	DEBUG ("\nupdate (ap=%d,l=%d)", ap_nid, l);
	dest_ap_node = update_edge (*p, l, t);
}
#endif

/**
 * This function adds DS to any existing edge <THIS,l,old_s,dest_nid>. If such
 * an edge does not exist, it creates a new dest_n and inserts an edge. All
 * this is done only if (l,s) is not repeating.
 */

#if SUMM_STMT_CLOSURE
ap_node_index ap_fi_graph::
update_edge (ap_fi_node & p, label l, def_stmt s)
{
	ap_node_index p_nid = p.get_node_id ();
	DEBUG ("\nupdate_edge (ap-node=%d, l=%d)", p.get_node_id (), l);

	// Check whether p->l is already present with s. Then we need not check
	// whether or not s is repeating.
	ap_node_index dest_nid;
	if (dest_nid = p.get_destination_node (l, s))
	{
		#if CHECK_CONTAINER
		// If found but yet repeating, then results would be
		// different if we had not done this optimization. 
		if (is_stmt_repeating (p, l, s))
			RESULT ("\nDIFFERENT src_ap=%d,l=%d,dest_ap=%d", 
				p_nid, l, dest_nid);
		#endif

		return dest_nid;
	}

	if (is_stmt_repeating (p, l, s))
	{
		#if INTERMEDIATE_RESULT
		RESULT ("\nout-label of ap-node=%d is l=%d,s=%d", p_nid, l, s);
		DEBUG ("\nUpdategAP_cyclic() will do the rest");
		RESULT ("\n(3)pnid_ap_unbounded=true of gap node=%d,l=%d", p_nid, l);
		#endif

		return 0;
	}

	return insert_edge (p, l, s);
}
#endif

#if SUMM_TYPE_CLOSURE
ap_node_index ap_fi_graph::
update_edge (ap_fi_node & p, label l)
{
	ap_node_index p_nid = p.get_node_id ();
	/*
	// Optimization: Check whether p->l is already present. Then we need
	// not check whether or not the field edge is repeating.
	ap_fi_node * src_ap_node = g_ap.nodes[src_ap];
	ap_node_index dest_ap;
	if (dest_ap = src_ap_node->get_destination_node (l))
	{
		dest_access_name.add_ap_nodes (dest_ap);
		// ap_unbounded does not change.

		#if CHECK_CONTAINER
		// If found but yet repeating, then results would be
		// different if we had not done this optimization. 
		if (is_type_repeating (src_ap, l, g_ap))
			RESULT ("\nDIFFERENT src_ap=%d,l=%d,dest_ap=%d", 
				src_ap, l, dest_ap);
		#endif
		return 0;
	}
	*/

	// Check that l from any of the pt-nodes of src_ap is not repeating.
	// TODO: Try this commented line if precision not achieved.
	// This line is summarizing only ASTERISK edges.
	// if (!l && is_type_repeating (p, l))
	if (is_type_repeating (p, l))
	{
		#if INTERMEDIATE_RESULT
		RESULT ("\n(4)out-label of ap-node=%d is l=%d unbounded=true", p_nid, l);
		#endif
		return 0;
	}
	return insert_edge (p, l);
}
#endif

#if SUMM_TYPE_K && !gAP_CYCLIC
ap_node_index ap_fi_graph::
update_edge (ap_fi_node & p, label l, type t)
{
	ap_node_index p_nid = p.get_node_id ();

	// Check that l from any of the pt-nodes of src_ap is not repeating.
	// This line is summarizing only ASTERISK edges.

	if (!l && is_type_repeating (p, l, t))
	{
		#if INTERMEDIATE_RESULT
		RESULT ("\n(4)out-label of ap-node=%d is l=%d,t=%d unbounded=true", p_nid, l, t);
		#endif
		return 0;
	}

	return insert_edge (p, l, t);
}
#endif

#if SUMM_TYPE_K && gAP_CYCLIC
/** 
 * This function returns a pair of id of dest node and true if p->l,t->dest is
 * a cyclic edge.
 */

pair<ap_node_index, bool> ap_fi_graph::
update_edge (ap_fi_node & p, label l, type t)
{
	FUNBEGIN ();

	ap_node_index p_nid = p.get_node_id ();
	DEBUG ("\nupdate_edge (), src=%d->l=%d,t=%d", p_nid, l, t);

	// Check that l from any of the pt-nodes of src_ap is not repeating.
	// This line is summarizing only ASTERISK edges.
	// FIXME: For more precision, instead of checking repetition of only
	// (l,t), check repetition of two consecutive edges so that x.f.0.g.0
	// is not summarized with x.f.0. -- This happens in test44.c

	label l_field = p.get_in_edge_label ();
	type t_field = p.get_static_name ();
	ap_node_index dest_nid;
	if (!l && (dest_nid = get_type_repeating_node (p, l, t, l_field, t_field)))
	{
		#if INTERMEDIATE_RESULT
		RESULT ("\n(5)out-label of ap-node=%d is l*=%d,t*=%d,lf=%d,tf=%d cyclic edge", 
			p_nid, l, t, l_field, t_field);
		#endif
		ap_fi_node * dest_n = nodes[dest_nid];
		bool is_cyclic = true;
		p.insert_edge (l, t, *dest_n, is_cyclic);
		DEBUG ("\ncyclic-edge: ap-node=%d->l=%d->ap-node=%d", p_nid, l, dest_n->get_node_id ());
		RETURN (make_pair (dest_nid, is_cyclic));
		return (make_pair (dest_nid, is_cyclic));
	}

	dest_nid = insert_edge (p, l, t);
	DEBUG ("\nupdate_edge (), src=%d->l=%d,t=%d->dest=%d", p_nid, l, t, dest_nid);
	// If no repetition of edge (l,t) is found, then this edge is acyclic.
	bool is_cyclic = false;

	RETURN (make_pair (dest_nid, is_cyclic));
	// return make_pair (dest_nid, is_cyclic);
}
#endif

#if SUMM_K_FILTER || SUMM_K_PREFIX
ap_node_index ap_fi_graph::
update_edge (ap_fi_node & p, label l, type t)
{
	ap_node_index p_nid = p.get_node_id ();

	// SUMM_K_PRECISE is more precise than SUMM_K_FILTER since the former
	// does not merge two nodes with same unbounded APs with different K
	// prefix.
	// SUMM_K_FILTER is more efficient than SUMM_K_PRECISE since the latter
	// unnecessarily propagates k-prefix access paths even along cycles in
	// gPT.

	if (is_ap_long (p, l))
	{
		#if INTERMEDIATE_RESULT
		DEBUG ("\n(4)out-label of ap-node=%d is l=%d unbounded=true", p_nid, l);
		#endif
#if SUMM_K_FILTER
		// Store an access path only if it is max k long.
		return 0;
#elif SUMM_K_PREFIX
		// Store access path's prefix upto k length
		// TODO: For more precise summarization where xff is
		// differentiated from xff* (for K=2), we need to call
		// p.insert_edge (wild_card_label, s, dest);
		DEBUG ("\nReturning k-prefix ap_nid=%d", p_nid);
		return p_nid;
#endif
	}

	return insert_edge (p, l, t);
}
#endif

#if SUMM_K_CONSISTENT
ap_node_index ap_fi_graph::
update_edge (ap_fi_node & p, label l)
{
	ap_node_index p_nid = p.get_node_id ();
	if (is_ap_summarized (p))
	{
		DEBUG ("\npnid=%d is_ap_summarized", p_nid);
		#if DEBUG_CONTAINER
		// This is not an error since a new out-pointer-edge could be
		// added from summary node by the statement.
		if (l != wild_card_id)
		{
			DEBUG ("\nEgen contains summary path followed with non-wild_card_id:");
			DEBUG ("\n\tap_id=%d x l=%d", p_nid, l);
		}
		#endif

		// If ap contains wild_card_id in the end, then do not append anything else.
		return p_nid;
		// If ap does not contain wild_card_id, then append l below.
	}
	else
		DEBUG ("\npnid=%d NOT is_ap_summarized", p_nid);

	return insert_edge (p, l);
}
#endif

#if SUMM_POINTED_TO_BY
ap_node_index ap_fi_graph::
update_edge (ap_fi_node & p, label l, type t)
{
#if SUMM_FIELD_POINTED_TO_BY
	// If l is not ASTERISK, then simply append to P without worrying
	// whether P contains ASTERISK or not.
	if (l)
		return insert_edge (p, l, t);
#else
	// If p is stack node, insert l
	if (p.get_node_id () == stack.get_node_id ())
		return insert_edge (stack, l, t);
#endif

	// If l is ASTERISK, then append to P only if P is pure variable i.e.
	// it does not already contain ASTERISK.
	if (!l && is_var_path (p))
		return insert_edge (p, l, t);

#if SUMM_REACHABLE_BY
	// If P is x.* and L is * or field, then propagate P.
	if (!is_var_path (p))
		return p.get_node_id ();
#endif

	// If P contains ASTERISK and l is ASTERISK, do not save. We save only
	// pointed-to-by-var access paths.
	return 0;
}
#endif


#if SUMM_STMT_CLOSURE
ap_node_index ap_fi_graph::
insert_edge (ap_fi_node & p, label l, def_stmt s)
{
	// If the program reaches this point, it means the out-node on l,s does
	// not exist. But out-node on l could have existed.
	def_stmt_set ds;
	ap_fi_node * dest_n = NULL;
	// FIXME: replace get_out_edge_list() with  get_out_nodes() for efficiency.
	map<label, pair<def_stmt_set, ap_node_index> > p_oute = p.get_out_edge_list ();
	if (p_oute.find (l) != p_oute.end ())
	{
		DEBUG ("\nlabel=%d exists", l);
		ds = p_oute[l].first;
		ap_node_index dest_nid = p_oute[l].second;
		dest_n = nodes[dest_nid];
		DEBUG ("\nFound dest=%d", dest_nid);
	}
	else
	{
		DEBUG ("\nlabel=%d,s=%d does not exist before ap-node=%d", l, s, p_nid);
		dest_n = new ap_fi_node (nodes);
		DEBUG ("\np=%d->l=%d,s=%d, created dest=%d", p_nid, l, s, dest_n->get_node_id ());
	}

	p.insert_edge (l, s, *dest_n);
	DEBUG ("\nap-node=%d->l=%d,s=%d->ap-node=%d", p_nid, l, s, dest_n->get_node_id ());

	return dest_n->get_node_id ();
}
#endif

/** 
 * Insert edge from p->l,t to a new node. This edge can, therefore, not be a
 * cyclic edge.
 */

#if SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX 
ap_node_index ap_fi_graph::
insert_edge (ap_fi_node & p, label l, type t)
{
	ap_fi_node * dest_n = NULL;
	ap_node_index dest_nid;
	if (dest_nid = p.get_destination_node (l, t))
	{
		DEBUG ("\nlabel=%d,t=%d exists", l, t);
		DEBUG ("\nFound dest=%d", dest_nid);
		return dest_nid;
	}

	DEBUG ("\nlabel=%d,t=%d does not exist before ap-node=%d", l, t, p.get_node_id ());
	dest_n = new ap_fi_node (nodes);
	DEBUG ("\np=%d->l=%d,t=%d, created dest=%d", p.get_node_id (), l, t, dest_n->get_node_id ());

#if gAP_CYCLIC && !SUMM_POINTED_TO_BY && !SUMM_K_FILTER && !SUMM_K_PREFIX 
	// An edge to a new node cannot be cyclic
	bool is_cyclic = false;
	p.insert_edge (l, t, *dest_n, is_cyclic);
#else
	p.insert_edge (l, t, *dest_n);
#endif

	DEBUG ("\nap-node=%d->l=%d,t=%d->ap-node=%d", p.get_node_id (), l, t, dest_n->get_node_id ());

	return dest_n->get_node_id ();
}
#endif

#if SUMM_TYPE_CLOSURE || SUMM_K_CONSISTENT 
ap_node_index ap_fi_graph::
insert_edge (ap_fi_node & p, label l)
{
	ap_fi_node * dest_n = NULL;
	ap_node_index dest_nid;
	if (dest_nid = p.get_destination_node (l))
	{
		DEBUG ("\nlabel=%d exists", l);
		DEBUG ("\nFound dest=%d", dest_nid);
		return dest_nid;
	}

	DEBUG ("\nlabel=%d does not exist before ap-node=%d", l, p.get_node_id ());
	dest_n = new ap_fi_node (nodes);
	DEBUG ("\np=%d->l=%d, created dest=%d", p.get_node_id (), l, dest_n->get_node_id ());

	p.insert_edge (l, *dest_n);

	DEBUG ("\nap-node=%d->l=%d->ap-node=%d", p.get_node_id (), l, dest_n->get_node_id ());

	return dest_n->get_node_id ();
}
#endif

/**
 * This function is called only when summarization is based on statement ids
 * (i.e. SUMM_STMT_CLOSURE=1).
 *
 * A gPT node has only bounded access paths (i.e. paths with non-repeating stmt
 * ids) marked, e.g. xf, xfg. For paths with repeating stmt ids,
 * ap_unbounded=true is set. Therefore a gPT node with xff (repeating stmt ids)
 * and a gPT node with yff (repeating stmt ids) are both represented by the
 * same clone with ap_nodes(acyclic)=phi, ap_unbounded=true. This is imprecise.
 */

#if SUMM_STMT_CLOSURE
bool ap_fi_graph::
is_stmt_repeating (ap_fi_node & p, label l, def_stmt s)
{
	label in_edge_label = p.get_in_edge_label ();
	ap_node_index in_node_id = p.get_in_node_id ();

	// Do not return. s:x->f=&y creates STACK_DEREF edge with s id. If
	// STACK_DEREF edge with s id repeats, we need to return true.
	// if (in_edge_label == stack_deref)
	//	return false;

	if (s == DONT_CARE)
		return false;

	if (!in_node_id)
		return false;

	ap_fi_node * in_n = nodes[in_node_id];
	// FIXME: replace the following two lines with get_in_def_stmt_set() for efficiency.
	map<label, pair<def_stmt_set, ap_node_index> > in_n_oute = in_n->get_out_edge_list ();
	def_stmt_set in_def_stmt_set = in_n_oute[in_edge_label].first;

	if (l == in_edge_label && 
		in_def_stmt_set.find (s) != in_def_stmt_set.end ())
	{
		DEBUG ("\nin-label of ap-node=%d is l=%d,s=%d", p.get_node_id (), l, s);
		return true;
	}

	return is_stmt_repeating (*in_n, l, s);	
}
#endif

/**
 * A gPT node has only bounded access paths (i.e. paths with non-repeating
 * types) marked, e.g. xf, xfg. For paths with repeating types,
 * ap_unbounded=true is set. Therefore a gPT node with xff (repeating f) and a
 * gPT node with yff (repeating f) are both represented by the same clone with
 * ap_nodes(acyclic)=phi, ap_unbounded=true. This is imprecise.
 */

#if SUMM_TYPE_CLOSURE
bool ap_fi_graph::
is_type_repeating (ap_fi_node & p,
	label l)
{	
	DEBUG ("\nis_type_repeating (p=%d,l=%d)", p.get_node_id (), l);

	set<label> src_static_names = p.get_static_names ();

	// Find if there is repetition only if src_ap is a heap node
	if (!src_static_names.size ())
	{
		if (p.get_node_id () != stack.get_node_id ()) 
			DEBUG ("\nError: ap=%d has no gPT type", p.get_node_id ());
		return false;
	}

	#if DEBUG_CONTAINER
	DEBUG ("\nis_type_repeating(src_ap_node=%d,{", p.get_node_id ());
	set<label>::iterator ti;
	for (ti = src_static_names.begin (); ti != src_static_names.end (); ti++)
	{
		csvarinfo_t ht = VEC_index (csvarinfo_t, program.variable_data, *ti);
		DEBUG ("%s(%d),", ht->name, *ti);
	}
	DEBUG ("},l=%d)", l);
	#endif

	bool is_repeating = is_type_repeating (p, src_static_names, l);
	DEBUG ("\nis_repeating=%d", is_repeating);
	return is_repeating;
}
#endif

/** 
 * This function is called only when summarization is based on types (i.e.
 * SUMM_TYPE_CLOSURE=1). It finds if heap or stack field is repeating. Edge L is at an
 * offset=L from SRC_STATIC_NAMES of memory locations.  We check if in-edge of
 * node AP is equal to L and if in-node of node AP has a matching heap type or
 * stack variable name in SRC_STATIC_NAMES.  Heap types are required to find
 * unbounded creation of memory locations on heap. Stack names are required to
 * bound access paths (gAP) when there is a data structure cycle on stack in
 * gPT
 */

#if SUMM_TYPE_CLOSURE
bool ap_fi_graph::
is_type_repeating (ap_fi_node & p,
	set<label> & src_static_names, 
	label l)
{
	ap_node_index p_nid = p.get_node_id ();

	#if DEBUG_CONTAINER
	DEBUG ("\n\tis_type_repeating(ap_nid=%d,{", p_nid);
	set<label>::iterator hi;
	for (hi = src_static_names.begin (); hi != src_static_names.end (); hi++)
	{
		csvarinfo_t ht = VEC_index (csvarinfo_t, program.variable_data, *hi);
		DEBUG ("%s(%d),", ht->name, *hi);
	}
	DEBUG ("},l=%d)", l);
	#endif

	ap_node_index in_node_id = p.get_in_node_id ();
	DEBUG ("\n\tin_node_id=%d", in_node_id);

	if (!in_node_id)
		return false;

	label in_edge_label = p.get_in_edge_label ();
	DEBUG ("\n\tin_edge_label=%d", in_edge_label);

	ap_fi_node * in_n = nodes[in_node_id];

	if (l != in_edge_label)
	{
		// DEBUG ("\n\tl=%d != in_edge_label=%d", l, in_edge_label);
		return is_type_repeating (*in_n, src_static_names, l);
	}

	// Do not return. s:x->f=&y creates STACK_DEREF edge with s id. If
	// STACK_DEREF edge with s id repeats, we need to return true.
	// if (in_edge_label == stack_deref)
	//	return false;

	ap_fi_node * apn = nodes[in_node_id];
	set<label> in_ap_static_names = apn->get_static_names ();

	if (!in_ap_static_names.size ())
	{
		if (in_node_id != stack.get_node_id ()) 
			DEBUG ("\nError: ap=%d has no gPT type", in_node_id);
		return false; 
	}

	#if DEBUG_CONTAINER
	DEBUG ("\n\tap=%d, in_ap_static_names=", in_node_id);
	for (hi = in_ap_static_names.begin (); hi != in_ap_static_names.end (); hi++)
	{
		csvarinfo_t ht = VEC_index (csvarinfo_t, program.variable_data, *hi);
		DEBUG ("%s(%d),", ht->name, *hi);
	}
	#endif

	// If any of src_static_names is in ap_static_names, then it
	// means that label l and in_edge_label are fields/dereferences from
	// same type of heap node; therefore l is repeating.
	set<label>::iterator ti;
	for (ti = src_static_names.begin (); ti != src_static_names.end (); ti++)
		if (in_ap_static_names.find (*ti) != in_ap_static_names.end ())
			return true;

	return is_type_repeating (*in_n, src_static_names, l);
}
#endif

/**
 * A gPT node has only bounded access paths (i.e. paths with k-repeating types)
 * marked, e.g. xf, xfg. For paths with k-repeating types, ap_unbounded=true is
 * set. Therefore a gPT node with xff (k-repeating f) and a gPT node with yff
 * (k-repeating f) are both represented by the same clone with
 * ap_nodes(acyclic)=phi, ap_unbounded=true. This is imprecise.
 */

#if SUMM_TYPE_K
bool ap_fi_graph::
is_type_repeating (ap_fi_node & p,
	label l,
	type t,
	unsigned int num_repeating_edges)
{	
	FUNBEGIN ();

	label in_edge_label = p.get_in_edge_label ();
	type static_name = p.get_static_name ();

	if (in_edge_label == l && static_name == t)
	{
		num_repeating_edges++;
		DEBUG ("\np=%d,l=%d,t=%d,num_repeating_edges=%d", 
			p.get_node_id (), l, t, num_repeating_edges);
		if (num_repeating_edges == SUMM_TYPE_K)
			RETURN (true);
			// return true;
		if (num_repeating_edges > SUMM_TYPE_K)
		{
			RESULT ("\nError: gAP has >%d occurrences of l=%,t=%d", 
				SUMM_TYPE_K, l, t);
			RETURN (true);
			// return true;
		}
	}

	ap_node_index in_node_id = p.get_in_node_id ();

	if (!in_node_id)
		RETURN (false);
		// return false;

	ap_fi_node * in_n = nodes[in_node_id];

	RETURN (is_type_repeating (*in_n, l, t, num_repeating_edges));
	// return is_type_repeating (*in_n, l, t, num_repeating_edges);
}
#endif

#if SUMM_POINTED_TO_BY

/**
 * A gPT node has only pointed-to-by-var. Therefore, save the following access
 * paths: var itself or var.ASTERISK or if SUMM_FIELD_POINTED_TO_BY, then
 * var.ASTERISK.field(s) also i.e., allow max one ASTERISK in the access path.
 * @return true if P is a variable
 * @return false if P contains an ASTERISK
 */

bool ap_fi_graph::
is_var_path (ap_fi_node & p)
{	
	ap_node_index in_node_id = p.get_in_node_id ();
	if (!in_node_id)
	{
		DEBUG ("\nis_var_path(ap=%d)=true", p.get_node_id ());
		return true;
	}

	label in_edge_label = p.get_in_edge_label ();
	// If ASTERISK already exists in P, then P is not a variable
	if (!in_edge_label)
	{
		DEBUG ("\nis_var_path(ap=%d)=false", p.get_node_id ());
		return false;
	}

	ap_fi_node * in_n = nodes[in_node_id];

	return is_var_path (*in_n);
}
#endif


#if gAP_CYCLIC && SUMM_TYPE_K
bool ap_fi_graph::
is_in_field_label_same (ap_fi_node & p,
	label l_asterisk,
	type t_asterisk,
	label l_field,
	type t_field)
{
	FUNBEGIN ();

	// Check that l from any of the pt-nodes of src_ap is not repeating.
	// This line is summarizing only ASTERISK edges.
	if (is_in_label_same (p, l_asterisk, t_asterisk))
	{
#if SUMM_FIELD_POINTERS
		ap_node_index in_node_id = p.get_in_node_id ();
		if (!in_node_id)
			RETURN (false);
			// return false;
		ap_fi_node * in_n = nodes[in_node_id];

		// For more precision, instead of checking repetition of only
		// (l,t), check repetition of two consecutive edges so that x.f.0.g.0
		// is not summarized with x.f.0. -- This happens in test44.c.
		// If pointer is a field pointer, then check that the field is also repeating
		if (!l_field || is_in_label_same (*in_n, l_field, t_field))
#endif
			RETURN (true);
			// return true;
	}

	RETURN (false);
	// return false;
}
#endif

#if gAP_CYCLIC && SUMM_TYPE_K
bool ap_fi_graph::
is_in_label_same (ap_fi_node & p,
	label l,
	type t)
{
	label in_edge_label = p.get_in_edge_label ();
	type static_name = p.get_static_name ();

	if (in_edge_label == l && static_name == t)
		return true;

	return false;	
}
#endif

/**
 * A gPT node has both bounded access paths (i.e. paths with k-repeating types)
 * marked, e.g. xf, xfg and unbounded access paths (i.e. with kleene closure
 * gAP edges), e.g. xf(.f)*. Therefore a gPT node with xff (k-repeating f) and
 * a gPT node with yff (k-repeating f) are represented by different clones.
 * This is precise.
 * FIXME: This function is taking 4.68% of 560 seconds analysis time.
 * Accumulate <l,t> of ancestor nodes on each node so that we need to
 * recursively call ancestor nodes unnecessarily.
 */

#if gAP_CYCLIC && SUMM_TYPE_K
ap_node_index ap_fi_graph::
get_type_repeating_node (ap_fi_node & curr_p,
	label l_asterisk,
	type t_asterisk,
	label l_field,
	type t_field,
	unsigned int num_repeating_edges)
{	
	FUNBEGIN ();

	if (is_in_field_label_same (curr_p, l_asterisk, t_asterisk, l_field, t_field))
	{
		num_repeating_edges++;
		DEBUG ("\np=%d,l*=%d,t*=%d,lf=%d,tf=%d,num_repeating_edges=%d", 
			curr_p.get_node_id (), l_asterisk, t_asterisk, l_field, t_field, num_repeating_edges);
		if (num_repeating_edges == SUMM_TYPE_K)
			RETURN (curr_p.get_node_id ());
			// return curr_p.get_node_id ();
		if (num_repeating_edges > SUMM_TYPE_K)
		{
			RESULT ("\nError: gAP has >%d occurrences of l*=%d,t*=%d,lf=%d,tf=%d", 
				SUMM_TYPE_K, l_asterisk, t_asterisk, l_field, t_field);
			RETURN (curr_p.get_node_id ());
			// return curr_p.get_node_id ();
		}
	}

	ap_node_index in_node_id = curr_p.get_in_node_id ();
	if (!in_node_id)
		RETURN (0);
		// return 0;
	ap_fi_node * in_n = nodes[in_node_id];
	ap_node_index latest_repeating_nid = get_type_repeating_node (*in_n, 
		l_asterisk, t_asterisk, l_field, t_field, num_repeating_edges);
	// If (l,t) has repeated K times, and node P also has (l,t) in-edge,
	// then return P as the type-repeating-node.
	if (latest_repeating_nid)
	{
		if (is_in_field_label_same (curr_p, l_asterisk, t_asterisk, l_field, t_field))
			RETURN (curr_p.get_node_id ());
			// return curr_p.get_node_id ();
		RETURN (latest_repeating_nid);
		// return latest_repeating_nid;
	}

	RETURN (0);
	// return 0;
}
#endif


/**
 * A gPT node has only bounded access paths (i.e. paths with length<=K)
 * marked, e.g. xf, xff, for K=3. For longer paths, ap_unbounded=true is
 * set. Therefore a gPT node with xfff and a gPT node with yfff are both
 * represented by the same clone with ap_nodes(acyclic)=phi, ap_unbounded=true. This
 * is imprecise.
 */

#if SUMM_K_FILTER || SUMM_K_PREFIX
bool ap_fi_graph::
is_ap_long (ap_fi_node & p,
	label l)
{
	unsigned int max_len = 0;
	if (SUMM_K_FILTER)	max_len = SUMM_K_FILTER;
	else if (SUMM_K_PREFIX)	max_len = SUMM_K_PREFIX;
	else			RESULT ("\nK is not set");
	if (p.get_ap_len () > max_len)
	{
		RESULT ("\nError: Length of ap-nid=%d ap =%d, K=%d",
			p.get_node_id (), p.get_ap_len (), max_len);
		return true;
	}
	return (p.get_ap_len () == max_len);
}
#endif

#if SUMM_K_CONSISTENT
bool ap_fi_graph::
is_ap_summarized (ap_fi_node & p)
{
	return (p.get_in_edge_label () == wild_card_id);
}
#endif

void ap_fi_graph::
get_ap_nodes (list<label> & path,
	set<ap_node_index> & ap_nodes)
{
	DEBUG ("\nget_ap_nodes()");
	set<ap_fi_node *> ap_srcs;
	ap_srcs.insert (&stack);

	list<label>::iterator li;
	for (li = path.begin (); li != path.end (); li++)
	{
		label l = *li;
		set<ap_fi_node *> ap_dests;
		set<ap_fi_node *>::iterator srci;
		for (srci = ap_srcs.begin (); srci != ap_srcs.end (); srci++)
		{
			ap_fi_node * ap_src = *srci;
			DEBUG ("\nap_src=%d", ap_src->get_node_id ());
			set<ap_node_index> ap_dest_ids;
#if SUMM_TYPE_K || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
			ap_dest_ids = ap_src->get_destination_nodes (l);
#else
			ap_node_index ap_dest_id = ap_src->get_destination_node (l);
			if (ap_dest_id)
			{
				ap_dest_ids.insert (ap_dest_id);
				DEBUG ("\nap_dest_id=%d", ap_dest_id);
			}
#endif

			set<ap_node_index>::iterator desti;
			for (desti = ap_dest_ids.begin (); desti != ap_dest_ids.end (); desti++)
			{
				ap_node_index ap_dest_id = *desti;
				ap_fi_node * ap_dest = nodes[ap_dest_id];
				ap_dests.insert (ap_dest);
				ap_nodes.insert (ap_dest_id);
			}
		}
		ap_srcs = ap_dests;
	}
}

#if SUMM_K_CONSISTENT
void ap_fi_graph::
remove_wild_card_subsumed_aps (set<ap_node_index> & ap_nids)
{
	set<label> subsumed_aps;
	set<label>::iterator api;
        for (api = ap_nids.begin (); api != ap_nids.end (); api++)
        {       
                ap_node_index apid = *api;
                ap_fi_node * apn = nodes[apid];
                if (apn->get_in_edge_label () != wild_card_id)
                        continue;

                ap_node_index ap_in_id = apn->get_in_node_id ();

		set<label> subsumed_aps_temp;
		// Get AP nids that are subsumed by AP_IN_ID.WILD_CARD_ID
                get_reachable_nodes (ap_in_id, subsumed_aps_temp);
		// APID is itself the wild_card_id AP.
		subsumed_aps_temp.erase (apid);

		// subsumed_aps.insert (subsumed_aps_temp.begin (), subsumed_aps_temp.end ());
		merge_set (subsumed_aps_temp, subsumed_aps);
        }       

        set<label>::iterator sapi;
        for (sapi = subsumed_aps.begin (); sapi != subsumed_aps.end (); sapi++)
                ap_nids.erase (*sapi);
}
#endif

/**
 * Get nodes reachable via acyclic out-edges.
 */

#if SUMM_K_CONSISTENT
void ap_fi_graph::
get_reachable_nodes (ap_node_index apid, set<ap_node_index> & reachable_nodes)
{
	ap_fi_node * apn = nodes[apid];

	set<ap_node_index> curr_reachable_nodes;
	apn->get_reachable_nodes (curr_reachable_nodes);
	// reachable_nodes.insert (curr_reachable_nodes.begin (), curr_reachable_nodes.end ());
	merge_set (curr_reachable_nodes, reachable_nodes);

	set<ap_node_index>::iterator ri;
	for (ri = curr_reachable_nodes.begin (); ri != curr_reachable_nodes.end (); ri++)
		get_reachable_nodes (*ri, reachable_nodes);
}
#endif

void ap_fi_graph::
print_statistics ()
{
	unsigned int tot_acyclic_edge_count = 0;
	unsigned int tot_cyclic_edge_count = 0;
	unsigned int max_ap_len = 0;
	unsigned int avg_ap_len = 0;

	map<ap_node_index, ap_fi_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		ap_node_index ap_nid = ni->first;
		ap_fi_node * n = ni->second;
#if SUMM_STMT_CLOSURE
		map<label, pair<def_stmt_set, ap_node_index> > oute = n->get_out_edge_list ();
#elif SUMM_TYPE_K && gAP_CYCLIC
		map<pair<label, type>, ap_node_index> oute = n->get_out_edge_list ();
		map<pair<label, type>, ap_node_index> outce = n->get_out_cyclic_edge_list ();
		if (outce.size ())
			tot_cyclic_edge_count += outce.size ();
#elif (SUMM_TYPE_K && !gAP_CYCLIC) || SUMM_POINTED_TO_BY || SUMM_K_FILTER || SUMM_K_PREFIX
		map<pair<label, type>, ap_node_index> oute = n->get_out_edge_list ();
#else
		map<label, ap_node_index> oute = n->get_out_edge_list ();
#endif
		if (oute.size ())
			tot_acyclic_edge_count += oute.size ();

		list<label> ap;
		get_access_paths (ap_nid, ap);
		avg_ap_len += ap.size ();
		if (max_ap_len < ap.size ())
			max_ap_len = ap.size ();
	}

	float avg_len = (float) avg_ap_len / nodes.size ();
	RESULT ("\ng_ap, nodes=%d", nodes.size ());
	RESULT ("\ng_ap, acyclic-edges=%d", tot_acyclic_edge_count);
	RESULT ("\ng_ap, cyclic-edges=%d", tot_cyclic_edge_count);
	RESULT ("\ng_ap, avg_acyclic_ap_len=%f", avg_len);
	RESULT ("\ng_ap, max_acyclic_ap_len=%d", max_ap_len);
        FILE * stat_file = fopen (STAT_FILE, "a");
	if (!stat_file)
	{
		RESULT ("\nError: cannot open STAT_FILE=%d", STAT_FILE);
		return;
	}
	fprintf (stat_file, "\ng_ap, nodes=%d", nodes.size ());
	fprintf (stat_file, "\ng_ap, acyclic-edges=%d", tot_acyclic_edge_count);
	fprintf (stat_file, "\ng_ap, cyclic-edges=%d", tot_cyclic_edge_count);
	fprintf (stat_file, "\ng_ap, avg_acyclic_ap_len=%f", avg_len);
	fprintf (stat_file, "\ng_ap, max_acyclic_ap_len=%d", max_ap_len);
	fclose (stat_file);
}

void ap_fi_graph::
get_access_paths (set<ap_node_index> & ap_nids,
	set<list<label> > & aps)
{
	set<ap_node_index>::iterator api;
	for (api = ap_nids.begin (); api != ap_nids.end (); api++)
	{
		list<label> ap;
		ap_node_index apnid = *api;
		DEBUG ("\nget_access_paths (ap_nid=%d)", apnid);
		get_access_paths (apnid, ap);
		aps.insert (ap);
	}
}

void ap_fi_graph::
get_access_paths (ap_node_index apnid,
	list<label> & ap)
{
	if (apnid == stack.get_node_id ())
		return;

	ap_fi_node * apn = nodes[apnid];
	label in_edge_label = apn->get_in_edge_label ();
	ap.push_front (in_edge_label);

	// Get acyclic APs
	ap_node_index in_ap_nid = apn->get_in_node_id ();
	get_access_paths (in_ap_nid, ap);
}

void ap_fi_graph::
append_ap_field (list<label> & ap, label field)
{
	label last = *(--ap.end ());

	if (last == wild_card_id)
		return;

	// Since AP already has within MAX_LEN_PRINT number of pointers,
	// appending a non-pointer field will still retain that property.
//	if (field)
//	{
//		ap.push_back (field);
//		return;
//	}

	unsigned int ap_len = ap.size ();
//	unsigned int ap_len = 0;
//	list<label>::iterator li;
//	for (li = ap.begin (); li != ap.end (); li++)
//	{
//		label l = *li;
//		if (!l)
//			ap_len++;
//	}

	if (ap_len == MAX_LEN_PRINT)
		ap.push_back (wild_card_id);
	else if (ap_len < MAX_LEN_PRINT)
		ap.push_back (field);
        else if (ap_len > MAX_LEN_PRINT)
        {
                // label last = *(--ap.end ());
                // if (last != wild_card_id)
                {
                        // RESULT ("\nError: ap size is greater than %d", MAX_LEN_PRINT);
                        RESULT ("\nError: ap has more than %d pointer fields", MAX_LEN_PRINT);
                        print_access_path (ap);
                }
        }
}

void ap_fi_graph::
print_access_path (list<label> & ap)
{
	list<label>::iterator li;
	for (li = ap.begin (); li != ap.end (); li++)
	{
		label l = *li;
		if (li == ap.begin ())
		{
			csvarinfo_t var = program.cs_get_varinfo (l);
			RESULT ("%s(%d).", var->name, l);
		}
#if SUMM_K_PREFIX || SUMM_K_CONSISTENT
		else if (l == wild_card_id)
		{
			RESULT ("+.");
		}
#endif
		else
		{
			RESULT ("%d.", *li);
		}
	}
}

#if SUMM_STMT_CLOSURE
void ap_fi_graph::
get_access_paths (ap_node_index apnid,
	list<pair<label, def_stmt_set > > & ap)
{
	if (apnid == stack.get_node_id ())
		return;

	ap_fi_node * apn = nodes[apnid];
	label in_edge_label = apn->get_in_edge_label ();
	def_stmt_set in_def_stmt_set = get_in_def_stmt_set (*apn);
	ap_node_index in_ap_nid = apn->get_in_node_id ();

	ap.push_front (make_pair (in_edge_label, in_def_stmt_set));
	get_access_paths (in_ap_nid, ap);

	#if DEBUG_CONTAINER
	unsigned int apn_len = apn->get_ap_len ();
	DEBUG ("\nlen=%d:", apn_len);
	#endif
}
#endif

void ap_fi_graph::
print_access_path (list<pair<label, def_stmt_set> > & ap)
{
	list<pair<label, def_stmt_set> >::iterator li;
	for (li = ap.begin (); li != ap.end (); li++)
	{
		label l = li->first;
		def_stmt_set ds = li->second;
		if (li == ap.begin ())
		{
			csvarinfo_t var = program.cs_get_varinfo (l);
#if SUMM_STMT_CLOSURE
			RESULT ("%s(%d{", var->name, l);
#else
			RESULT ("%s(%d).", var->name, l);
#endif
		}
		else
#if SUMM_STMT_CLOSURE
			RESULT ("(%d{", l);
#else
			RESULT ("(%d).", l);
#endif

#if SUMM_STMT_CLOSURE
		def_stmt_set::iterator dsi;
		for (dsi = ds.begin (); dsi != ds.end (); dsi++)
			RESULT ("%d,", *dsi);
		RESULT ("}).");
#endif
	}
}

#if gAP_CYCLIC && SUMM_TYPE_K
void ap_fi_graph::
print_cyclic_edges (g_ap_edges & ce)
{
	g_ap_edges::iterator cei;
	for (cei = ce.begin (); cei != ce.end (); cei++)
	{
		ap_node_index apsrc = cei->first;
		map<pair<label, type>, ap_node_index> outce = cei->second;
	
		map<pair<label, type>, ap_node_index>::iterator out_cedge_i;
		for (out_cedge_i = outce.begin(); out_cedge_i != outce.end(); out_cedge_i++)
		{
			label l = out_cedge_i->first.first;
			type t = out_cedge_i->first.second; 
			DEBUG ("\ncyclic edge label l=%d,t=%d", l, t);

			ap_node_index apdest = out_cedge_i->second;

			RESULT ("\n%d -> %d,%d", apsrc, l, t);
			RESULT (" -> %d", apdest);
		}
	}
} 
#endif

void ap_fi_graph::
print_subgraph (set<ap_node_index> & ap_nodes)
{
	set<ap_node_index>::iterator pi;
	for (pi = ap_nodes.begin (); pi != ap_nodes.end (); pi++)
	{
		ap_fi_node * n = nodes[*pi];
		n->print_node (NULL);
	}
}

void ap_fi_graph::
print_graph (FILE * file)
{
	DEBUG ("\nap_fi_graph=");
	if (file)
		fprintf (file, "\ndigraph ap_fi_graph {");
	map<ap_node_index, ap_fi_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		if (!ni->first)
		{
			RESULT ("\nError: Node 0");
			continue;
		}
		DEBUG ("\nAP-node %d", ni->first);
		ap_fi_node * n = ni->second;
		n->print_node (file);
		
	}
	DEBUG ("\nended print_graph()");
	if (file)
		fprintf (file, "}");
}


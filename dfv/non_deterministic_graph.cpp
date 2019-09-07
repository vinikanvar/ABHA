
/************************
 * @author Vini Kanvar
************************/

#include "non_deterministic_graph.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

non_deterministic_graph::
non_deterministic_graph () : stack (nodes)
{
	DEBUG ("\nnew non_deterministic_graph()");
	reference_count = 0;
	NEW_ADDR ("\nnew non_deterministic_graph %x", this);
}

non_deterministic_graph::
~non_deterministic_graph ()
{
	DEBUG ("\nDelete this graph=%x (stack=%d)", this, stack.get_node_id ());
	DEBUG ("\nGC of live non_deterministic_graph");
	GC_ADDR ("\ngc non_deterministic_graph %x", this);
	erase ();
	nodes.clear ();
}

void non_deterministic_graph::
increment_reference_count ()
{
	reference_count++;
}

void non_deterministic_graph::
decrement_reference_count ()
{
        if (!reference_count)
        {
                RESULT ("\nError: reference count of non_deterministic_graph %x was already 0", this);
                return;
        }

        reference_count--;
        DEBUG ("\nCount = %d (after decr) of variable set", reference_count);
        if (!reference_count)
        {
#if GC
                DEBUG ("\nGC non_deterministic_graph");
                delete this;
#endif
        }
}

set<non_deterministic_node *> non_deterministic_graph::
get_destination_nodes (non_deterministic_node & n, label l)
{
	DEBUG ("\nget_destination_node (src=%d,l=%d)", n.get_node_id (), l);

	set<label_site_pair> lsps = n.get_destination_nodes (l);
	set<non_deterministic_node *> out_nodes;
	set<label_site_pair>::iterator lspsi;
	for (lspsi = lsps.begin (); lspsi != lsps.end (); lspsi++)
	{
		label_site_pair lsp = *lspsi;
		non_deterministic_node * dest_n = nodes[lsp];
		out_nodes.insert (dest_n);
	}
	return out_nodes;
}

void non_deterministic_graph::
insert_destination_nodes (non_deterministic_node & src_node, 
	label offset, 
	set<non_deterministic_node *> & dest_nodes)
{
	set<non_deterministic_node *> temp_dest_nodes = get_destination_nodes (src_node, offset);
	dest_nodes.insert (temp_dest_nodes.begin (), temp_dest_nodes.end ());
}

void non_deterministic_graph::
clean ()
{
	set<label_site_pair> reachable_nodes;
	label_site_pair stack_s = stack.get_label_site_pair ();
	get_reachable_nodes (stack_s, reachable_nodes);
	set<label_site_pair> unreachable_nodes;

	map<label_site_pair, non_deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		label_site_pair ls = ni->first;
		if (reachable_nodes.find (ls) == reachable_nodes.end ())
		{
			non_deterministic_node * n = ni->second;
			DEBUG ("\nDelete n=%d", n->get_node_id ());
#if GC

			// The out-nodes of N may not be dead. Therefore, it is
			// important to disconnect/delete the out-edges of N.
			// The in-nodes of N are always dead.  Therefore, the
			// in-edges will get deleted when in-nodes are deleted.
			delete_out_edges (*n);
			unreachable_nodes.insert (ls);
			// We do not erase node from NODES here otherwise an
			// erased node may be accessed in delete_out_edges from
			// another unreachable node that reaches the erased node.
#endif
		}
	}

	set<label_site_pair>::iterator uni;
	for (uni = unreachable_nodes.begin (); uni != unreachable_nodes.end (); uni++)
	{
		label_site_pair ls = *uni;
		non_deterministic_node * n = nodes[ls];
		delete n;
		nodes.erase (ls);
	}

	DEBUG ("\nclean() done");
}

void non_deterministic_graph::
erase ()
{
	map<label_site_pair, non_deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); )
	{
		non_deterministic_node * n = ni->second;
		// Stack node is not on stack and cannot be deleted. We do not
		// erase it from nodes[] also which is the default state when
		// an empty graph is created.
		if (n == &stack)
		{
			delete_out_edges (*n);
			ni++;
			continue;
		}
		DEBUG ("\nDeleting node=%x (node-id=%d)", n, n->get_node_id ());
		nodes.erase (ni++);
		delete n;
	}
}

bool non_deterministic_graph::
is_empty ()
{
	if (!nodes.size ())
		return true;
	if (nodes.size () > 1)
		return false;
	non_deterministic_node * n = nodes.begin ()->second;
	if (n == &stack)
		return true;
	return false;
}

void non_deterministic_graph::
get_reachable_nodes (label_site_pair & src, set<label_site_pair> & reachable_nodes)
{
	if (reachable_nodes.find (src) != reachable_nodes.end ())
		return;
	reachable_nodes.insert (src);
	non_deterministic_node * n = nodes[src];
	set<label_site_pair> out_nodes;
	n->get_out_nodes (out_nodes);
	set<label_site_pair>::iterator ni;
	for (ni = out_nodes.begin (); ni != out_nodes.end (); ni++)
	{
		label_site_pair ls = *ni;
		get_reachable_nodes (ls, reachable_nodes);
	}
}

bool non_deterministic_graph::
is_value_same (non_deterministic_graph & g)
{
	// If address of THIS and g is same, return true;
	if (this == &g)
	{
		DEBUG ("\nOptimum graph is_value_same()");
		return true;
	}

	if (nodes.size () != g.nodes.size ())
		return false;

	map<label_site_pair, non_deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		label_site_pair lsp = ni->first;
		if (g.nodes.find (lsp) == g.nodes.end ())
			return false;

		non_deterministic_node * n = ni->second;
		non_deterministic_node * g_n = g.nodes[lsp];

		if (!n->is_node_same (*g_n))
			return false;
	}

	return true;
}

non_deterministic_graph * non_deterministic_graph::
copy_value (bool is_loop_merge)
{
	DEBUG ("\ncopy_value() -- to fresh graph");
#if DEBUG_CONTAINER
	DEBUG ("\nTHIS graph=");
	print_value (NULL);
#endif
	non_deterministic_graph * g = new non_deterministic_graph;
	map<label_site_pair, non_deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		non_deterministic_node * n = ni->second;
		non_deterministic_node * g_n = n->new_copy_node (g->nodes);
	}
#if DEBUG_CONTAINER
	DEBUG ("\ncopied graph g=");
	g->print_value (NULL);
#endif

#if CHECK_CONTAINER
	if (!is_value_same (*g))
	{
		RESULT ("\nError: copy_value() is not okay");
	}
	else
	{
		DEBUG ("\ncopy_value() is okay");
	}
#endif

	return g;
}

/**
 * Copy graph G to THIS graph.
 */

void non_deterministic_graph::
copy_value (non_deterministic_graph & g, bool is_loop_merge)
{
#if DEBUG_CONTAINER
	DEBUG ("\nsrc graph=");
	g.print_value (NULL);
	DEBUG ("\ndest graph=");
	print_value (NULL);
#endif

	// If THIS is an empty graph
	if (nodes.size () == 1 && !stack.is_out_edge ())
	{
		DEBUG ("\nOptimum graph copy_value()");
		map<label_site_pair, non_deterministic_node *>::iterator gni;
		for (gni = g.nodes.begin (); gni != g.nodes.end (); gni++)
		{
			non_deterministic_node * g_n = gni->second;
			non_deterministic_node * n = g_n->new_copy_node (nodes);
		}
	}
	else
	{
		set<pair<label_site_pair, label_site_pair> > visited_pairs;
		g.copy_subgraph (g.stack, stack, *this, visited_pairs);

		// ipa/backward_inter_procedural_analysis already calls clean.
		// clean ();
	}
}

/**
 * This function inserts a new edge from SRC_NODE to a node that contains SP
 * via L.
 */

non_deterministic_node * non_deterministic_graph::
insert_edge (non_deterministic_node & src_node, label l, site_pair sp)
{
	label_site_pair new_lsp = make_pair (l, sp);
	non_deterministic_node * new_dest_node = get_node (l, sp);

	src_node.insert_edge (l, *new_dest_node);
	DEBUG ("\ninsert_edge() done");
	return new_dest_node;
}

non_deterministic_node * non_deterministic_graph::
get_node (label l, site_pair sp)
{
	non_deterministic_node * new_dest_node = NULL;
	label_site_pair new_lsp = make_pair (l, sp);
	if (nodes.find (new_lsp) != nodes.end ())
		new_dest_node = nodes[new_lsp];
	else
	{
		new_dest_node = new non_deterministic_node (sp, l, nodes);
#if DEBUG_CONTAINER
		DEBUG ("\nnew dest_node=%d", new_dest_node->get_node_id ());
		new_dest_node->print_node (nodes);
#endif
	}
	return new_dest_node;
}

/**
 * bool ignore is to allow overloading in non_deterministic_graph::insert_edge
 * and deterministic_graph::insert_edge called from
 * liveness_analysis<LIVE_VALUE_TYPE>.
 */

non_deterministic_node * non_deterministic_graph::
insert_edge (non_deterministic_node & src_node, label l, site s,
	bool is_alloc_site)
{
	site_pair sp;
	if (is_alloc_site)
	{
		DEBUG ("\nis_alloc_site - %d", s);
		sp = make_pair (s, 0);
	}
	else
	{
		DEBUG ("\nis_desc_site - %d", s);
		sp = make_pair (0, s);
	}
	non_deterministic_node * new_dest_node = get_node (l, sp);

	src_node.insert_edge (l, *new_dest_node);
	DEBUG ("\ninsert_edge() done");
	return new_dest_node;
}

/**
 * Copy subgraph rooted at SRC_NODE of THIS graph to DEST_NODE of THIS graph.
 */

void non_deterministic_graph::
copy_subgraph (non_deterministic_node & src_node, non_deterministic_node & dest_node)
{
	set<pair<label_site_pair, label_site_pair> > visited_pairs;
	copy_subgraph (src_node, dest_node, *this, visited_pairs);
}

/**
 * Copy subgraph rooted at SRC_NODE of THIS graph to DEST_NODE of DEST_GRAPH.
 */

void non_deterministic_graph::
copy_subgraph (non_deterministic_node & src_node, non_deterministic_node & dest_node,
	non_deterministic_graph & dest_graph)
{
	set<pair<label_site_pair, label_site_pair> > visited_pairs;
	copy_subgraph (src_node, dest_node, dest_graph, visited_pairs);
}

void non_deterministic_graph::
copy_subgraph (non_deterministic_node & src_node, non_deterministic_node & dest_node,
	non_deterministic_graph & dest_graph,
	set<pair<label_site_pair, label_site_pair> > & visited_pairs)
{
	DEBUG ("\ncopy_subgraph (src=%d, dest=%d)", 
		src_node.get_node_id (), dest_node.get_node_id());
	label_site_pair src_lsp = src_node.get_label_site_pair ();
	label_site_pair dest_lsp = dest_node.get_label_site_pair ();
	pair<label_site_pair, label_site_pair> lsp_pair = make_pair (src_lsp, dest_lsp);
	if (visited_pairs.find (lsp_pair) != visited_pairs.end ())
		return;
	visited_pairs.insert (lsp_pair);

	map<label, set<label_site_pair> > src_out_edges = src_node.get_out_edge_list ();
	map<label, set<label_site_pair> >::iterator soutei;
	for (soutei = src_out_edges.begin (); soutei != src_out_edges.end (); soutei++)
	{
		label soutl = soutei->first;
		set<label_site_pair> soutlsps = soutei->second;
		set<label_site_pair>::iterator soutlspsi;
		for (soutlspsi = soutlsps.begin (); soutlspsi != soutlsps.end (); soutlspsi++)
		{
			label_site_pair soutlsp = *soutlspsi;
			site_pair soutsp = soutlsp.second;
			non_deterministic_node * out_src_node = nodes[soutlsp];
#if DEBUG_CONTAINER
			DEBUG ("\ninsert_edge: dest=%d -> %d -> ", dest_node.get_node_id (), soutl);
			non_deterministic_node::print_site_pair (soutsp);
#endif
			non_deterministic_node * out_dest_node = dest_graph.insert_edge (dest_node, soutl, soutsp);
			if (!out_dest_node)
			{
				RESULT ("\nError: Could not copy out-edge of src=%d to dest=%d", 
					src_node.get_node_id (), dest_node.get_node_id ());
				continue;
			}

			copy_subgraph (*out_src_node, *out_dest_node, dest_graph, visited_pairs);
		}
	}
}

/**
 * Copy each out-edge L of SRC_NODE of THIS graph to node reachable by
 * DEST_NODE->DEST_OFFSET+L of THIS graph. Here DEST_OFFSET is a non-pointer.
 * Therefore, the out-fields of SRC_NODE are appended to DEST_OFFSET. Then copy
 * subgraph rooted at child node of SRC_NODE to child node of DEST_NODE via
 * DEST_OFFSET+L.
 */

void non_deterministic_graph::
copy_subgraph (non_deterministic_node & src_node, non_deterministic_node & dest_node, label dest_offset,
	non_deterministic_graph & dest_graph)
{
	DEBUG ("\ncopy_subgraph()");
	DEBUG ("\nsrc_node=%d, dest_node=%d, dest_offset=%d", 
		src_node.get_node_id (), dest_node.get_node_id (), dest_offset);
	map<label, set<label_site_pair> > src_out_edges = src_node.get_out_edge_list ();
	map<label, set<label_site_pair> >::iterator soutei;
	for (soutei = src_out_edges.begin (); soutei != src_out_edges.end (); soutei++)
	{
		label soutl = soutei->first;
		DEBUG ("\nsoutl=%d", soutl);
		set<label_site_pair> soutlsps = soutei->second;
		set<label_site_pair>::iterator soutlspsi;
		for (soutlspsi = soutlsps.begin (); soutlspsi != soutlsps.end (); soutlspsi++)
		{
			label_site_pair soutlsp = *soutlspsi;
			DEBUG ("\nsoutsp=<%d,%d>", soutlsp.second.first, soutlsp.second.second);
			site_pair soutsp = soutlsp.second;
			non_deterministic_node * out_src_node = nodes[soutlsp];
			DEBUG ("\nout_src_node=%d", out_src_node->get_node_id ());
			non_deterministic_node * out_dest_node = NULL;	
			if (!dest_node.is_stack_node ())
			{
				DEBUG ("\ndest_node not stack");
				DEBUG ("\nlabel=%d", soutl + dest_offset);
				out_dest_node = dest_graph.insert_edge (dest_node, soutl + dest_offset, soutsp);
				DEBUG ("\nout_dest_node=%d", out_dest_node->get_node_id ());
			}
			else
			{
				DEBUG ("\ndest_node is stack");
				// Find varid of soutl+dest_offset (next in csvarinfo of dest_offset)
				csvarinfo_t var = program.cs_get_varinfo (dest_offset);
				DEBUG ("\nvar=%s(%d)", var->name, var->id);
				csvarinfo_t varoffset = program.cs_first_vi_for_offset (var, soutl);
				if (!varoffset || !varoffset->decl)
					continue;
				DEBUG ("\nvaroffset=%s(%d)", varoffset->name, varoffset->id);
				label varoffset_id = varoffset->id;
				DEBUG ("\nvar=%s(%d), out_dest_node=%d", var->name, var->id, out_dest_node->get_node_id ());
				// The use-site of soutl is lost here i.e., replaced
				// with varoffset_id*(-1)
				out_dest_node = dest_graph.insert_edge (dest_node, varoffset_id, 
					make_pair(0, varoffset_id * (ROOT_LINK))); 
			}
			set<pair<label_site_pair, label_site_pair> > visited_pairs;
			copy_subgraph (*out_src_node, *out_dest_node, dest_graph, visited_pairs);
		}
	}
}


void non_deterministic_graph::
copy_subgraph (non_deterministic_node & src_node, non_deterministic_node & dest_node, label dest_offset)
{
	copy_subgraph (src_node, dest_node, dest_offset, *this);
}

/** 
 * Add edge v and the subgraph under v from stack of THIS graph to stack of
 * DEST_GRAPH. Perform a temporary deletion of edge v from src_node (i.e. do
 * not clean the graph).
 */

void non_deterministic_graph::
copy_subgraph (variable_id v,
	non_deterministic_node & src_v_node, 
	non_deterministic_graph & dest_graph)
{
	non_deterministic_node * dest_v_node = dest_graph.insert_edge (dest_graph.stack, v, 
		make_pair (0, v * (ROOT_LINK)));
	set<pair<label_site_pair, label_site_pair> > visited_pairs;
	copy_subgraph (src_v_node, *dest_v_node, dest_graph, visited_pairs);
}

/**
 * This function converts a non-deterministic graph into a deterministic graph
 * FIXME: There is a bug in this NFA to DFA. Once <nfa-node,dfa-node> are
 * mapped, this mapping changes when a new dfa-node is inserted by insert_edge.
 * Therefore, we update visited_pairs. However, we cannot do anything about a
 * call already made on old dfa-node.
 */

void non_deterministic_graph::
copy_subgraph (non_deterministic_node & src_node, 
	deterministic_node & dest_node,
	deterministic_graph & dest_graph,
	set<pair<node_index, node_index> > & visited_pairs)
{
	DEBUG ("\ncopy_subgraph (src=%d, dest=%d)", 
		src_node.get_node_id (), dest_node.get_node_id());

	node_index src_nid = src_node.get_node_id ();
	node_index dest_nid = dest_node.get_node_id ();
	pair<node_index, node_index> vis_pair = make_pair (src_nid, dest_nid);
	if (visited_pairs.find (vis_pair) != visited_pairs.end ())
		return;
	visited_pairs.insert (vis_pair);
	DEBUG ("\n\tvisited_pair=<%d,%d>", src_nid, dest_nid);

	map<label, set<label_site_pair> > src_out_edges = src_node.get_out_edge_list ();
	map<label, set<label_site_pair> >::iterator soutei;
	for (soutei = src_out_edges.begin (); soutei != src_out_edges.end (); soutei++)
	{
		label soutl = soutei->first;
		set<label_site_pair> soutlsps = soutei->second;
		set<label_site_pair>::iterator soutlspsi;
#if 0
		for (soutlspsi = soutlsps.begin (); soutlspsi != soutlsps.end (); soutlspsi++)
		{
			label_site_pair soutlsp = *soutlspsi;
			site_pair soutsp = soutlsp.second;
		}
#endif
		for (soutlspsi = soutlsps.begin (); soutlspsi != soutlsps.end (); soutlspsi++)
		{
			label_site_pair soutlsp = *soutlspsi;
			site_pair soutsp = soutlsp.second;
			non_deterministic_node * out_src_node = nodes[soutlsp];
#if DEBUG_CONTAINER
			DEBUG ("\ninsert_edge: dest=%d -> %d -> ", dest_node.get_node_id (), soutl);
			non_deterministic_node::print_site_pair (soutsp);
#endif
			sites soutss;
			soutss.insert (soutsp.first);
			soutss.insert (soutsp.second);

			deterministic_node * out_dest_node = dest_graph.update_deterministic_edge (dest_node, soutl, soutss, visited_pairs);

			if (!out_dest_node)
			{
				RESULT ("\nError: Could not copy out-edge of src=%d to dest=%d", 
					src_node.get_node_id (), dest_node.get_node_id ());
				continue;
			}

			copy_subgraph (*out_src_node, *out_dest_node, dest_graph, visited_pairs);
		}

	}
}

/**
 * This function extracts THIS graph to DEST_GRAPH. Then it cleans THIS graph
 * in the end.
 */

void non_deterministic_graph::
extract_subgraph (set<variable_id> vids,
	non_deterministic_graph & dest_graph)
{
	set<variable_id>::iterator vi;
	for (vi = vids.begin (); vi != vids.end (); vi++)
	{
		variable_id v = *vi;
		set<non_deterministic_node *> src_v_nodes = get_destination_nodes (stack, v);
		set<non_deterministic_node *>::iterator si;	
		for (si = src_v_nodes.begin (); si != src_v_nodes.end (); si++)
		{
			non_deterministic_node * src_v_node = *si;
			copy_subgraph (v, *src_v_node, dest_graph);
		}
		delete_edge (stack, v, false);
	}
	clean ();
}

/**
 * This function deletes edge from SRC node to DEST node via L. It does not
 * delete the DEST node even if it is unreachable. 
 */

void non_deterministic_graph::
temp_delete_edge (non_deterministic_node & src, label l, non_deterministic_node & dest)
{
	src.temp_delete_edge (l, dest);
	if (dest.is_in_nodes ())
		return;

	// This is required to handle x=x->f type of statements where lvalue
	// node is also x and generated rvalue node is from x. If
	// copy_subgraph() from lvalue to rvalue happens after generating
	// rvalue, then it leads to copying generated rvalue to rvalue again.

	// Remove the identity of variable represented by dest node so that
	// when the variable is recreated, a new dest node for the variable
	// with empty subgraph is created, and the same dest node (with its
	// subgraph) is not create.
	label_site_pair old_dest_lsp = dest.get_label_site_pair ();
	nodes.erase (old_dest_lsp);
	// Our graphs are such that only one of alloc-site and desc-site is
	// non-null. Add label of DISCONNECTED_LINK on the null site.
	if (!old_dest_lsp.second.first)
		dest.set_alloc_site (DISCONNECTED_LINK);
	if (!old_dest_lsp.second.second)
		dest.set_desc_site (DISCONNECTED_LINK);
	label_site_pair new_dest_lsp = dest.get_label_site_pair ();
	nodes[new_dest_lsp] = &dest;

	// Replace in-nodes of dest of dest
	set<label> out_edge_labels;
	dest.get_out_edge_labels (out_edge_labels);
	set<label>::iterator li;
	for (li = out_edge_labels.begin (); li != out_edge_labels.end (); li++)
	{
		label l = *li;
		set<non_deterministic_node *> dests_of_dest = get_destination_nodes (dest, l);
		set<non_deterministic_node *>::iterator ddi;
		for (ddi = dests_of_dest.begin (); ddi != dests_of_dest.end (); ddi++)
		{
			non_deterministic_node * dest_dest = *ddi;
			dest_dest->replace_in_nodes (old_dest_lsp, new_dest_lsp);
		}
	}
}

void non_deterministic_graph::
delete_edge (non_deterministic_node & src_node, label l, bool is_clean)
{
	set<non_deterministic_node *> dest_nodes = get_destination_nodes (src_node, l);
	set<non_deterministic_node *>::iterator di;
	for (di = dest_nodes.begin (); di != dest_nodes.end (); di++)
	{
		non_deterministic_node * dest_node = *di;
		src_node.temp_delete_edge (l, *dest_node);
	}

	// TODO: Write better algo to find if subgraph under dest_node is
	// unreachable. Simply checking in-edges is not enough -- dest_node may
	// be reachable from a cycle but not from root node.
	// clean (dest_node);
	if (is_clean)
		clean ();
}

void non_deterministic_graph::
delete_out_edges (non_deterministic_node & node)
{
	set<label> out_edge_labels;
	node.get_out_edge_labels (out_edge_labels);
	set<label>::iterator li;
	for (li = out_edge_labels.begin (); li != out_edge_labels.end (); li++)
	{
		label l = *li;
		set<non_deterministic_node *> dests = get_destination_nodes (node, l);
		set<non_deterministic_node *>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
		{
			non_deterministic_node * dest = *di;
			node.temp_delete_edge (l, *dest);
		}
	}
	DEBUG ("\ndelete_out_edges() done");
}

/**
 * This function returns the dead variables from LOCAL_VARIABLES. Here
 * LOCAL_VARIABLES does not contain parameters, globals, and heap.
 */

set<label> non_deterministic_graph::
get_dead_variables (set<unsigned int> local_variables)
{
	set<unsigned int> dead_vars;
	RESULT ("\nError: non_deterministic_graph::get_dead_variables()");
	RESULT (" to be used by dfa/allocation_site_based_analysis");
	RESULT (" is not defined");
	return dead_vars;
}

void non_deterministic_graph::
get_valid_live_nodes (map<label, set<non_deterministic_node *> > & sync_pts_live_nodes,
	set<label_site_pair> & valid_live_nodes)
{
	map<label, set<non_deterministic_node *> >::iterator pli;
	for (pli = sync_pts_live_nodes.begin (); pli != sync_pts_live_nodes.end (); pli++)
	{
	        set<non_deterministic_node *> live_nodes = pli->second;
		set<non_deterministic_node *>::iterator lni;
		for (lni = live_nodes.begin (); lni != live_nodes.end (); lni++)
		{
			non_deterministic_node * ln = *lni;
			label_site_pair lss = ln->get_label_site_pair ();
			valid_live_nodes.insert (lss);
		}
	}
}

void non_deterministic_graph::
collect_access_paths (map<label_site_pair, set<list<label> > > & lsp_aps,
        set<list<label> > & all_aps)
{
        map<label_site_pair, set<list<label> > >::iterator lsp_api;
        for (lsp_api = lsp_aps.begin (); lsp_api != lsp_aps.end (); lsp_api++)
        {
                set<list<label> > aps = lsp_api->second;
                all_aps.insert (aps.begin (), aps.end ());
        }
}

void non_deterministic_graph::
get_access_paths_stats (map<label_site_pair, set<list<label> > > & lsp_aps,
        unsigned int & aps_count)
{
        map<label_site_pair, set<list<label> > >::iterator lsp_api;
        for (lsp_api = lsp_aps.begin (); lsp_api != lsp_aps.end (); lsp_api)
        {
                set<list<label> > aps = lsp_api->second;
                aps_count += aps.size ();
        }
}

/** 
 * This function basically pushes the access paths of VAR to its destination
 * nodes by appending the out-edge field to the access paths of VAR. It then
 * recursively calls this function on its destination nodes. This is done upto
 * k length of every access path.
 */

void non_deterministic_graph::
get_k_access_paths (set<list<label> > & aps, 
	unsigned int & tot_aps,
	bool is_accum_aps,
	struct cgraph_node * cnode)
{
	set<label_site_pair> valid_live_nodes;
	get_k_access_paths (aps, tot_aps, is_accum_aps, cnode, valid_live_nodes, false);
}

void non_deterministic_graph::
get_k_access_paths (set<list<label> > & aps, 
	unsigned int & tot_aps,
	bool is_accum_aps,
	struct cgraph_node * cnode,
	map<label, set<non_deterministic_node *> > & sync_pts_live_nodes)
{
	set<label_site_pair> valid_live_nodes;
	get_valid_live_nodes (sync_pts_live_nodes, valid_live_nodes);
	get_k_access_paths (aps, tot_aps, is_accum_aps, cnode, valid_live_nodes, true);
}

void non_deterministic_graph::
get_k_access_paths (set<list<label> > & aps,
	unsigned int & tot_aps,
	bool is_accum_aps,
	struct cgraph_node * cnode,
	set<label_site_pair> & valid_live_nodes,
	bool consider_validity)
{
#if 0
	// For efficiency convert graph to deterministic graph. We compute APs
	// on deterministic graph incrementally because of which APs can never
	// repeat in fixed point computation over the graph. 

	deterministic_graph * dest_graph = new deterministic_graph;
	set<pair<node_index, node_index> > visited_pairs;
	// FIXME: There is a bug in this NFA to DFA
	copy_subgraph (stack, dest_graph->stack, *dest_graph, visited_pairs);

	dest_graph->get_k_access_paths (aps, tot_aps, is_accum_aps, cnode);
#endif
	
	get_k_access_paths (aps, cnode, valid_live_nodes, consider_validity);
	tot_aps += aps.size ();
}

void non_deterministic_graph::
get_k_access_paths (set<list<label> > & aps,
	struct cgraph_node * cnode,
	set<label_site_pair> & valid_live_nodes,
	bool consider_validity)
{
        DEBUG ("\nget_k_access_paths");
        map<label_site_pair, set<list<label> > > sent_lsp_aps;
        map<label_site_pair, set<list<label> > > new_lsp_aps;
        label_site_pair stack_lsp = stack.get_label_site_pair ();
        get_k_access_paths (stack_lsp, sent_lsp_aps, new_lsp_aps, cnode,
		valid_live_nodes, consider_validity);
	if (new_lsp_aps.size ())
		RESULT ("\nError: new_lsp_aps not empty");
        sent_lsp_aps[stack_lsp].clear ();
        collect_access_paths (sent_lsp_aps, aps);
}

/**
 * This function adds empty AP to stack node. This is removed by
 * get_k_access_paths(set<list<label> > &) function.
 */

void non_deterministic_graph::
get_k_access_paths (label_site_pair & lsp,
        map<label_site_pair, set<list<label> > > & sent_lsp_aps,
        map<label_site_pair, set<list<label> > > & new_lsp_aps,
	struct cgraph_node * cnode,
	set<label_site_pair> & valid_live_nodes,
	bool consider_validity)
{
#if DEBUG_CONTAINER
	DEBUG ("\nget_k_access_paths, lsp=");
	non_deterministic_node::print_site_pair (lsp.second);
#endif

        if (lsp == stack.get_label_site_pair ())
        {
                list<label> base_ap;
                new_lsp_aps[lsp].insert (base_ap);
        }

        set<label_site_pair> changed_out_lsp;
        // Mark APs of lsp as old/sent. Create space for new aps of lss. This
        // is required when lsp points to lsp, and more new_aps may get added
        // to lsp by lsp itself.
        set<list<label> > new_src_aps = new_lsp_aps[lsp];
        sent_lsp_aps[lsp].insert (new_src_aps.begin (), new_src_aps.end ());
        new_lsp_aps.erase (lsp);

        non_deterministic_node * n = nodes[lsp];
        map<label, set<label_site_pair> > * out_edge_list = n->get_out_edge_list_pointer ();
        map<label, set<label_site_pair> >::iterator outei;
        for (outei = out_edge_list->begin (); outei != out_edge_list->end (); outei++)
        {
                label field = outei->first;
		if (lsp == stack.get_label_site_pair ()
			&& cnode && !program.is_in_scope (field, cnode))
			continue;

		DEBUG ("\nout-field=%d", field);
                set<label_site_pair> out_lsps = outei->second;
		set<label_site_pair>::iterator out_lspi;
		for (out_lspi = out_lsps.begin (); out_lspi != out_lsps.end (); out_lspi++)
		{
			label_site_pair out_lsp = *out_lspi;

			if (consider_validity && valid_live_nodes.find (out_lsp) == valid_live_nodes.end ())
				continue;

#if DEBUG_CONTAINER
			DEBUG ("\nout-lsp=");
			non_deterministic_node::print_site_pair (out_lsp.second);
#endif
	                if (append_k_access_paths (new_src_aps, field, out_lsp, sent_lsp_aps, new_lsp_aps))
				changed_out_lsp.insert (out_lsp);
		}
        }
	new_src_aps.clear ();

        // Breadth first
#if DEBUG_CONTAINER
        DEBUG ("\nchanged_out_lsp of src=<%d,{", lsp.first);
        non_deterministic_node::print_site_pair (lsp.second);
        DEBUG ("}>\n\t");
#endif
        set<label_site_pair>::iterator lsi;
        for (lsi = changed_out_lsp.begin (); lsi != changed_out_lsp.end (); lsi++)
        {
                label_site_pair out_lsp = *lsi;
#if DEBUG_CONTAINER
                DEBUG ("<%d,{", out_lsp.first);
                non_deterministic_node::print_site_pair (out_lsp.second);
                DEBUG ("}>");
#endif
                get_k_access_paths (out_lsp, sent_lsp_aps, new_lsp_aps, cnode, valid_live_nodes, consider_validity);
        }
}

bool non_deterministic_graph::
append_k_access_paths (set<list<label> > & src_aps,
        label field,
        label_site_pair & dest_lsp,
        map<label_site_pair, set<list<label> > > & sent_lsp_aps,
        map<label_site_pair, set<list<label> > > & new_lsp_aps)
{
        bool has_changed = false;
        set<list<label> >::iterator api;
        for (api = src_aps.begin (); api != src_aps.end (); api++)
        {
                list<label> ap = * api;
                append_ap_field (ap, field);

		if (!ap.size ())
			continue;

		// In a non-deterministic graph, the same AP computed even
		// incrementally, can reappear.
                if (sent_lsp_aps[dest_lsp].find (ap) != sent_lsp_aps[dest_lsp].end ())
                        continue;
                if (new_lsp_aps[dest_lsp].find (ap) != new_lsp_aps[dest_lsp].end ())
                        continue;

                new_lsp_aps[dest_lsp].insert (ap);
                has_changed = true;
        }
        return has_changed;
}

void non_deterministic_graph::
append_ap_field (list<label> & ap, label field)
{
        unsigned int ap_len = ap.size ();
        if (ap_len < MAX_LEN_PRINT)
                ap.push_back (field);
	else
		ap.clear ();
}

void non_deterministic_graph::
print_access_paths (map<label_site_pair, set<list<label> > > & lsp_aps)
{
        map<label_site_pair, set<list<label> > >::iterator lsp_api;
        for (lsp_api = lsp_aps.begin (); lsp_api != lsp_aps.end (); lsp_api++)
        {
                set<list<label> > aps = lsp_api->second;
                print_access_paths (aps);
        }
}

void non_deterministic_graph::
print_access_paths (set<list<label> > & aps)
{
        set<list<label> >::iterator api;
        for (api = aps.begin (); api != aps.end (); api++)
        {
                list<label> ap = * api;
                print_access_path (ap);
        }
}

void non_deterministic_graph::
print_access_path (list<label> & ap)
{
        RESULT ("\n\t\t");
        list<label>::iterator li;
        for (li = ap.begin (); li != ap.end (); li++)
        {
                label l = *li;
                if (li == ap.begin ())
                {
                        csvarinfo_t var = program.cs_get_varinfo (l);
                        if (!var)
                                continue;
                        if (var->is_global_var)
                        {
                                RESULT ("# %s(%d).", var->name, l);
                        }
                        else
                        {
                                RESULT ("%s(%d).", var->name, l);
                        }
                }
                else
                {
                        RESULT ("%d.", l);
                }
        }
}

void non_deterministic_graph::
get_graph_stats (unsigned int & node_count,
	unsigned int & edge_count,
	unsigned int & use_sites_count,
	set<site> & unique_use_sites)
{
	unsigned int this_node_count = 0;
	unsigned int this_edge_count = 0;

	this_node_count = nodes.size ();
	map<label_site_pair, non_deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		non_deterministic_node * n = ni->second;
		n->get_node_stats (this_edge_count, use_sites_count, unique_use_sites);
	}

	STATS ("\nthis_node_count=%d, this_edge_count=%d", 
		this_node_count, this_edge_count);
	node_count += this_node_count;
	edge_count += this_edge_count;
}

bool non_deterministic_graph::
is_graph_reachability_okay ()
{
	set<label_site_pair> reachable_nodes;
	label_site_pair stack_s = stack.get_label_site_pair ();
	get_reachable_nodes (stack_s, reachable_nodes);
	if (nodes.size () != reachable_nodes.size ())
	{
		RESULT ("\nError: Nodes are unreachable even after clean()");
		return false;
	}
	return true;
}

bool non_deterministic_graph::
is_graph_labelling_okay ()
{
	bool okay = true;
	map<label_site_pair, non_deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		label_site_pair lsp = ni->first;
		non_deterministic_node * n = ni->second;
		if (!n->is_node_okay (stack))
		{
			RESULT ("\nError: node=%d not okay", n->get_node_id ());
			okay = false;
		}

		// Check out-edge list
		map<label, set<label_site_pair> > out_edges = n->get_out_edge_list ();
		map<label, set<label_site_pair> >::iterator outei;
		for (outei = out_edges.begin (); outei != out_edges.end (); outei++)
		{
			label out_l = outei->first;
			set<label_site_pair> out_lsps = outei->second;
			set<label_site_pair>::iterator out_lspsi;
			for (out_lspsi = out_lsps.begin (); out_lspsi != out_lsps.end (); out_lspsi++)
			{
				label_site_pair out_lsp = *out_lspsi;
				non_deterministic_node * out_n = nodes[out_lsp];
				if (!n->is_out_node_okay (out_l, *out_n))
				{
					RESULT ("\nError: Out-node=%d of node=%d not okay", 
						out_n->get_node_id (), n->get_node_id ());
					okay = false;
				}
			}
		}

		// Check in-nodes
		set<label_site_pair> in_nodes = n->get_in_nodes ();
		set<label_site_pair>::iterator ini;
		for (ini = in_nodes.begin (); ini != in_nodes.end (); ini++)
		{
			label_site_pair in_lsp = *ini;
			non_deterministic_node * in_n = nodes[in_lsp];
			if (!n->is_in_node_okay (*in_n))
			{
				RESULT ("\nError: In-node=%d of node=%d not okay", in_n->get_node_id (), n->get_node_id ());
				okay = false;
			}
		}
	}
	DEBUG ("\nOkay=%d", okay);
	return okay;
}

void non_deterministic_graph::
print_value (const char * file)
{
	DEBUG ("\nlive_graph=");
	DEBUG ("\nstack=%d", stack.get_node_id ());

#if 0
	set<list<label> > aps;
	set<label_site_pair> valid_live_nodes;
	get_k_access_paths (aps, NULL, valid_live_nodes, false);
	print_access_paths (aps);
#endif

        RESULT ("\nNodes=%d", nodes.size ());
        if (nodes.size () > 500)
                RESULT ("\nALARM: Nodes=%d", nodes.size ());

	map<label_site_pair, non_deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		non_deterministic_node * n = ni->second;
		n->print_node (nodes);
	}
}


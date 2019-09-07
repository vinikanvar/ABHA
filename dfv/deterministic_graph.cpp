
/************************
 * @author Vini Kanvar
************************/

#include "deterministic_graph.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

deterministic_graph::
deterministic_graph () : stack (nodes)
{
	DEBUG ("\nnew deterministic_graph()");
	reference_count = 0;
	NEW_ADDR ("\nnew deterministic_graph %x", this);
}

deterministic_graph::
~deterministic_graph ()
{
	DEBUG ("\nDelete this graph=%x (stack=%d)", this, stack.get_node_id ());
	DEBUG ("\nGC of live deterministic_graph");
	GC_ADDR ("\ngc deterministic_graph %x", this);
	erase ();
	nodes.clear ();
}

void deterministic_graph::
increment_reference_count ()
{
	reference_count++;
}

void deterministic_graph::
decrement_reference_count ()
{
        if (!reference_count)
        {
                RESULT ("\nError: reference count of deterministic_graph %x was already 0", this);
                return;
        }

        reference_count--;
        DEBUG ("\nCount = %d (after decr) of variable set", reference_count);
        if (!reference_count)
        {
#if GC
                DEBUG ("\nGC deterministic_graph");
                delete this;
#endif
        }
}

deterministic_node * deterministic_graph::
get_destination_node (label l)
{
	return get_destination_node (stack, l);
}

deterministic_node * deterministic_graph::
get_destination_node (deterministic_node & n, label l)
{
	DEBUG ("\nget_destination_node (src=%d,l=%d)", n.get_node_id (), l);

	label_sites lss = n.get_destination_node (l);
	if (lss.second.empty ())
	{
		DEBUG ("\ndest of n=%d l=%d does not exist", n.get_node_id (), l);
		return NULL;
	}
	deterministic_node * dest_n = nodes[lss];
	return dest_n;
}

set<deterministic_node *> deterministic_graph::
get_destination_nodes (deterministic_node & n, label l)
{
	set<deterministic_node *> dest_nodes;
	deterministic_node * dest_node = get_destination_node (n, l);
	dest_nodes.insert (dest_node);
	return dest_nodes;
}

void deterministic_graph::
insert_destination_nodes (deterministic_node & src_node,
	label offset,
	set<deterministic_node *> & dest_nodes)
{
	deterministic_node * dest = get_destination_node (src_node, offset);
	if (dest)
		dest_nodes.insert (dest);
}
	
void deterministic_graph::
clean ()
{
	set<label_sites> reachable_nodes;
	label_sites stack_s = stack.get_label_sites ();
	get_reachable_nodes (stack_s, reachable_nodes);
	set<label_sites> unreachable_nodes;

	map<label_sites, deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		label_sites ls = ni->first;
		if (reachable_nodes.find (ls) == reachable_nodes.end ())
		{
			deterministic_node * n = ni->second;
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

	set<label_sites>::iterator uni;
	for (uni = unreachable_nodes.begin (); uni != unreachable_nodes.end (); uni++)
	{
		label_sites ls = *uni;
		deterministic_node * n = nodes[ls];
		delete n;
		nodes.erase (ls);
	}

	DEBUG ("\nclean() done");
}

void deterministic_graph::
erase ()
{
	map<label_sites, deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); )
	{
		deterministic_node * n = ni->second;
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

bool deterministic_graph::
is_empty ()
{
	if (!nodes.size ())
		return true;
	if (nodes.size () > 1)
		return false;
	deterministic_node * n = nodes.begin ()->second;
	if (n == &stack)
		return true;
	return false;
}

void deterministic_graph::
get_reachable_nodes (label_sites & src, set<label_sites> & reachable_nodes)
{
	if (reachable_nodes.find (src) != reachable_nodes.end ())
		return;
	reachable_nodes.insert (src);
	deterministic_node * n = nodes[src];
	set<label_sites> out_nodes;
	n->get_out_nodes (out_nodes);
	set<label_sites>::iterator ni;
	for (ni = out_nodes.begin (); ni != out_nodes.end (); ni++)
	{
		label_sites ls = *ni;
		get_reachable_nodes (ls, reachable_nodes);
	}
}

bool deterministic_graph::
is_value_same (deterministic_graph & g)
{
	// If address of THIS and g is same, return true;
	if (this == &g)
	{
		DEBUG ("\nOptimum graph is_value_same()");
		return true;
	}

	if (nodes.size () != g.nodes.size ())
		return false;

	map<label_sites, deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		label_sites lss = ni->first;
		if (g.nodes.find (lss) == g.nodes.end ())
			return false;

		deterministic_node * n = ni->second;
		deterministic_node * g_n = g.nodes[lss];

		if (!n->is_node_same (*g_n))
			return false;
	}

	return true;
}

deterministic_graph * deterministic_graph::
copy_value (bool is_loop_merge)
{
	DEBUG ("\ncopy_value() -- to fresh graph");
#if DEBUG_CONTAINER
	DEBUG ("\nTHIS graph=");
	print_value (NULL);
#endif
	deterministic_graph * g = new deterministic_graph;
	map<label_sites, deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		deterministic_node * n = ni->second;
		deterministic_node * g_n = n->new_copy_node (g->nodes);
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

void deterministic_graph::
copy_value (deterministic_graph & g, bool is_loop_merge)
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
		map<label_sites, deterministic_node *>::iterator gni;
		for (gni = g.nodes.begin (); gni != g.nodes.end (); gni++)
		{
			deterministic_node * g_n = gni->second;
			deterministic_node * n = g_n->new_copy_node (nodes);
		}
	}
	else
	{
		set<pair<label_sites, label_sites> > visited_pairs;
		g.copy_subgraph (g.stack, stack, *this, visited_pairs);

		// ipa/backward_inter_procedural_analysis already calls clean.
		// clean ();
	}
}

/**
 * This function inserts a new edge from SRC_NODE to a node that contains S via
 * L. It ensures that the graph remains deterministic. It does not clean the
 * graph if an old node becomes unreachable.
 */

deterministic_node * deterministic_graph::
insert_edge (deterministic_node & src_node, label l, site s,
	bool latest_use_only)
{
	sites ss;
	ss.insert (s);
	deterministic_node * dest_node = insert_edge (src_node, l, ss, latest_use_only);
	return dest_node;
}

/**
 * This function inserts a new edge from SRC_NODE to a node that contains SS
 * via L. It ensures that the graph remains deterministic. It does not clean
 * the graph if an old node becomes unreachable.
 */

deterministic_node * deterministic_graph::
insert_edge (deterministic_node & src_node, label l, sites & ss,
	bool latest_use_only)
{
	deterministic_node * old_dest_node = get_destination_node (src_node, l);

	if (old_dest_node)
	{
		DEBUG ("\nold_dest_node=%d", old_dest_node->get_node_id ());
		sites old_ss = old_dest_node->get_desc_sites ();
		// if old_dest_node with ss already exists, nothing to be done.
		// Note that if ss is subset of old_ss then, subgraph of node
		// ss needs to be copied to old_ss.
		if (old_ss == ss)
			return old_dest_node;
	}

	sites new_ss;
	if (!latest_use_only)
	{
		// if old_dest_node exists without s
		if (old_dest_node)
			new_ss = old_dest_node->get_desc_sites ();
	}
	new_ss.insert (ss.begin (), ss.end ());

	label_sites new_lss = make_pair (l, new_ss);

	deterministic_node * new_dest_node = NULL;
	if (nodes.find (new_lss) != nodes.end ())
		new_dest_node = nodes[new_lss];
	else
	{
		new_dest_node = new deterministic_node (new_ss, l, nodes);
#if DEBUG_CONTAINER
		DEBUG ("\nnew dest_node=%d", new_dest_node->get_node_id ());
		new_dest_node->print_node (nodes);
#endif
	}

	if (old_dest_node)
	{
		src_node.temp_delete_edge (l, *old_dest_node);
		DEBUG ("\ndelete_edge() done");
	}

	src_node.insert_edge (l, *new_dest_node);
	DEBUG ("\ninsert_edge() done");

	if (!old_dest_node)
		return new_dest_node;

	// We need to copy the subgraph under old_dest_node to new_dest_node.
	// We cannot simply copy only the out-edges. 
	set<pair<label_sites, label_sites> > visited_pairs;
	copy_subgraph (*old_dest_node, *new_dest_node, *this, visited_pairs);

	return new_dest_node;
}

deterministic_node * deterministic_graph:: 
update_deterministic_edge (deterministic_node & src_node,
	label soutl,
	sites & soutss,
	set<pair<node_index, node_index> > & visited_pairs)
{
	deterministic_node * old_dest_node = get_destination_node (src_node, soutl);
	node_index old_dest_nid = 0;
	if (old_dest_node) 
		old_dest_nid = old_dest_node->get_node_id ();
	deterministic_node * new_dest_node = insert_edge (src_node, soutl, soutss);
	if (!old_dest_node || old_dest_node == new_dest_node)
		return new_dest_node;

	node_index new_dest_nid = new_dest_node->get_node_id ();

	set<pair<node_index, node_index> > new_visited_pairs;
	set<pair<node_index, node_index> >::iterator vpi;
	for (vpi = visited_pairs.begin (); vpi != visited_pairs.end (); )
	{
		node_index non_det_nid = vpi->first;
		node_index det_nid = vpi->second;
		if (old_dest_nid != det_nid)
		{
			vpi++;
			continue;
		}
		DEBUG ("\n\t\told_visited_pair=<%d,%d>", non_det_nid, det_nid);

		visited_pairs.erase (vpi++);
		new_visited_pairs.insert (make_pair (non_det_nid, new_dest_nid));

		DEBUG ("\n\t\tnew_visited_pair=<%d,%d>", non_det_nid, new_dest_nid);
	}
	visited_pairs.insert (new_visited_pairs.begin (), new_visited_pairs.end ());
	return new_dest_node;
}

/**
 * Copy subgraph rooted at SRC_NODE of THIS graph to DEST_NODE of THIS graph.
 */

void deterministic_graph::
copy_subgraph (deterministic_node & src_node, deterministic_node & dest_node)
{
	set<pair<label_sites, label_sites> > visited_pairs;
	copy_subgraph (src_node, dest_node, *this, visited_pairs);
}

/**
 * Copy subgraph rooted at SRC_NODE of THIS graph to DEST_NODE of DEST_GRAPH.
 */

void deterministic_graph::
copy_subgraph (deterministic_node & src_node, deterministic_node & dest_node,
	deterministic_graph & dest_graph)
{
	set<pair<label_sites, label_sites> > visited_pairs;
	copy_subgraph (src_node, dest_node, dest_graph, visited_pairs);
}

void deterministic_graph::
copy_subgraph (deterministic_node & src_node, deterministic_node & dest_node,
	deterministic_graph & dest_graph,
	set<pair<label_sites, label_sites> > & visited_pairs)
{
	DEBUG ("\ncopy_subgraph (src=%d, dest=%d)", 
		src_node.get_node_id (), dest_node.get_node_id());
	label_sites src_lss = src_node.get_label_sites ();
	label_sites dest_lss = dest_node.get_label_sites ();
	pair<label_sites, label_sites> lss_pair = make_pair (src_lss, dest_lss);
	if (visited_pairs.find (lss_pair) != visited_pairs.end ())
		return;
	visited_pairs.insert (lss_pair);

	map<label, label_sites> src_out_edges = src_node.get_out_edge_list ();
	map<label, label_sites>::iterator soutei;
	for (soutei = src_out_edges.begin (); soutei != src_out_edges.end (); soutei++)
	{
		label soutl = soutei->first;
		label_sites soutlss = soutei->second;
		sites soutss = soutlss.second;
		deterministic_node * out_src_node = nodes[soutlss];
#if DEBUG_CONTAINER
		DEBUG ("\ninsert_edge: dest=%d -> %d -> ", dest_node.get_node_id (), soutl);
		deterministic_node::print_sites (soutss);
#endif
		deterministic_node * out_dest_node = dest_graph.insert_edge (dest_node, soutl, soutss);
		if (!out_dest_node)
		{
			RESULT ("\nError: Could not copy out-edge of src=%d to dest=%d", 
				src_node.get_node_id (), dest_node.get_node_id ());
			continue;
		}

		copy_subgraph (*out_src_node, *out_dest_node, dest_graph, visited_pairs);
	}
}

/**
 * Copy each out-edge L of SRC_NODE of THIS graph to node reachable by
 * DEST_NODE->DEST_OFFSET+L of THIS graph. Here DEST_OFFSET is a non-pointer.
 * Therefore, the out-fields of SRC_NODE are appended to DEST_OFFSET. Then copy
 * subgraph rooted at child node of SRC_NODE to child node of DEST_NODE via
 * DEST_OFFSET+L.
 */

void deterministic_graph::
copy_subgraph (deterministic_node & src_node, deterministic_node & dest_node, label dest_offset,
	deterministic_graph & dest_graph)
{
	DEBUG ("\ndest_offset=%d", dest_offset);
	map<label, label_sites> src_out_edges = src_node.get_out_edge_list ();
	map<label, label_sites>::iterator soutei;
	for (soutei = src_out_edges.begin (); soutei != src_out_edges.end (); soutei++)
	{
		label soutl = soutei->first;
		label_sites soutlss = soutei->second;
		sites soutss = soutlss.second;
		deterministic_node * out_src_node = nodes[soutlss];
		deterministic_node * out_dest_node = NULL;	
		if (!dest_node.is_stack_node ())
		{
			out_dest_node = dest_graph.insert_edge (dest_node, soutl + dest_offset, soutss);
		}
		else
		{
			// Find varid of soutl+dest_offset (next in csvarinfo of dest_offset)
			csvarinfo_t var = program.cs_get_varinfo (dest_offset);
			csvarinfo_t varoffset = program.cs_first_vi_for_offset (var, soutl);
			if (!varoffset || !varoffset->decl)
				continue;
			label varoffset_id = varoffset->id;
			// The use-site of soutl is lost here i.e., replaced
			// with varoffset_id*(-1)
#if DEBUG_CONTAINER
			DEBUG ("\nsource graph node=");
			print_value (NULL);
			DEBUG ("\nEdge: src_node=%d, dest_node=%d, varoffset=%s(%d), site=%d",
				src_node.get_node_id (), dest_node.get_node_id (), 
				varoffset->name, varoffset_id, varoffset_id * (ROOT_LINK));
#endif
			out_dest_node = dest_graph.insert_edge (dest_node, varoffset_id, 
				varoffset_id * (ROOT_LINK)); 
		}
		set<pair<label_sites, label_sites> > visited_pairs;
		copy_subgraph (*out_src_node, *out_dest_node, dest_graph, visited_pairs);
	}
}


void deterministic_graph::
copy_subgraph (deterministic_node & src_node, deterministic_node & dest_node, label dest_offset)
{
	copy_subgraph (src_node, dest_node, dest_offset, *this);
}

/** 
 * Add edge v and the subgraph under v from stack of THIS graph to stack of
 * DEST_GRAPH. Perform a temporary deletion of edge v from src_node (i.e. do
 * not clean the graph).
 */

void deterministic_graph::
extract_subgraph (variable_id v, 
	deterministic_graph & dest_graph)
{
	deterministic_node * src_v_node = get_destination_node (stack, v);
	if (!src_v_node)
		return;

	deterministic_node * dest_v_node = dest_graph.insert_edge (dest_graph.stack, v, v * (ROOT_LINK));
	set<pair<label_sites, label_sites> > visited_pairs;
	copy_subgraph (*src_v_node, *dest_v_node, dest_graph, visited_pairs);
	delete_edge (stack, v, false);
}

/**
 * This function extracts THIS graph to DEST_GRAPH. Then it cleans THIS graph
 * in the end.
 */

void deterministic_graph::
extract_subgraph (set<variable_id> vids,
	deterministic_graph & dest_graph)
{
	set<variable_id>::iterator vi;
	for (vi = vids.begin (); vi != vids.end (); vi++)
	{
		variable_id v = *vi;
		extract_subgraph (v, dest_graph);
	}
	clean ();
}

/**
 * This function deletes edge from SRC node to DEST node via L. It does not
 * delete the DEST node even if it is unreachable. 
 */

void deterministic_graph::
temp_delete_edge (deterministic_node & src, label l, deterministic_node & dest)
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
	label_sites old_dest_ls = dest.get_label_sites ();
	nodes.erase (old_dest_ls);
	dest.insert_desc_site (DISCONNECTED_LINK);
	label_sites new_dest_ls = dest.get_label_sites ();
	nodes[new_dest_ls] = &dest;

	// Update label_sites in in_nodes of dest of dest
	set<label> out_edge_labels;
	dest.get_out_edge_labels (out_edge_labels);
	set<label>::iterator li;
	for (li = out_edge_labels.begin (); li != out_edge_labels.end (); li++)
	{
		label l = *li;
		deterministic_node * dest_dest = get_destination_node (dest, l);
		dest_dest->replace_in_nodes (old_dest_ls, new_dest_ls);
	}
	DEBUG ("\ndelete_out_edges() done");

}

void deterministic_graph::
delete_edge (deterministic_node & src_node, label l, bool is_clean)
{
	deterministic_node * dest_node = get_destination_node (src_node, l);
	if (!dest_node)
		return;

	src_node.temp_delete_edge (l, *dest_node);
	// TODO: Write better algo to find if subgraph under dest_node is
	// unreachable. Simply checking in-edges is not enough -- dest_node may
	// be reachable from a cycle but not from root node.
	// clean (dest_node);
	if (is_clean)
		clean ();
}

void deterministic_graph::
delete_out_edges (deterministic_node & node)
{
	set<label> out_edge_labels;
	node.get_out_edge_labels (out_edge_labels);
	set<label>::iterator li;
	for (li = out_edge_labels.begin (); li != out_edge_labels.end (); li++)
	{
		label l = *li;
		deterministic_node * dest = get_destination_node (node, l);
		node.temp_delete_edge (l, *dest);
	}
	DEBUG ("\ndelete_out_edges() done");
}

/**
 * This function returns the dead variables from LOCAL_VARIABLES. Here
 * LOCAL_VARIABLES does not contain parameters, globals, and heap.
 */

set<label> deterministic_graph::
get_dead_variables (set<unsigned int> local_variables)
{
	set<unsigned int> dead_vars;
	RESULT ("\nError: deterministic_graph::get_dead_variables()");
	RESULT (" to be used by dfa/allocation_site_based_analysis");
	RESULT (" is not defined");
	return dead_vars;
}

void deterministic_graph::
get_valid_live_nodes (map<label, set<deterministic_node *> > & sync_pts_live_nodes,
	set<label_sites> & valid_live_nodes)
{
	DEBUG ("\nget_valid_live_nodes()");
	map<label, set<deterministic_node *> >::iterator pli;
	for (pli = sync_pts_live_nodes.begin (); pli != sync_pts_live_nodes.end (); pli++)
	{
	        set<deterministic_node *> live_nodes = pli->second;
		DEBUG ("\npt=%d, live=", pli->first);
		set<deterministic_node *>::iterator lni;
		for (lni = live_nodes.begin (); lni != live_nodes.end (); lni++)
		{
			deterministic_node * ln = *lni;
			label_sites lss = ln->get_label_sites ();
			valid_live_nodes.insert (lss);
			DEBUG ("%d,", ln->get_node_id ());
		}
	}
}

void deterministic_graph::
collect_access_paths (map<label_sites, set<list<label> > > & lss_aps,
	set<list<label> > & all_aps)
{
	map<label_sites, set<list<label> > >::iterator lss_api;
	for (lss_api = lss_aps.begin (); lss_api != lss_aps.end (); lss_api++)
	{
		set<list<label> > aps = lss_api->second;
		all_aps.insert (aps.begin (), aps.end ());
	}
}

void deterministic_graph::
get_access_paths_stats (map<label_sites, set<list<label> > > & lss_aps,
	unsigned int & aps_count)
{
	map<label_sites, set<list<label> > >::iterator lss_api;
	for (lss_api = lss_aps.begin (); lss_api != lss_aps.end (); lss_api)
	{
		set<list<label> > aps = lss_api->second;
		aps_count += aps.size ();
	}
}

/** 
 * This function basically pushes the access paths of VAR to its destination
 * nodes by appending the out-edge field to the access paths of VAR. It then
 * recursively calls this function on its destination nodes. This is done upto
 * k length of every access path.
 */

void deterministic_graph::
get_k_access_paths (set<list<label> > & aps, 
	unsigned int & tot_aps,
	bool is_accum_aps,
	struct cgraph_node * cnode)
{
	set<label_sites> valid_live_nodes;
	get_k_access_paths (aps, tot_aps, is_accum_aps, cnode, valid_live_nodes, false);
}

void deterministic_graph::
get_k_access_paths (set<list<label> > & aps, 
	unsigned int & tot_aps,
	bool is_accum_aps,
	struct cgraph_node * cnode,
	map<label, set<deterministic_node *> > & sync_pts_live_nodes)
{
	set<label_sites> valid_live_nodes;
	get_valid_live_nodes (sync_pts_live_nodes, valid_live_nodes);
#if DEBUG_CONTAINER
	set<label_sites>::iterator li;
	DEBUG ("\nvalid_live_nodes=");
	for (li = valid_live_nodes.begin (); li != valid_live_nodes.end (); li++)
	{
		label_sites lss = *li;
		DEBUG ("<%d,{", lss.first);
		deterministic_node::print_sites (lss.second);
		DEBUG ("}>,");
	}
#endif
	get_k_access_paths (aps, tot_aps, is_accum_aps, cnode, valid_live_nodes, true);
}

void deterministic_graph::
get_k_access_paths (set<list<label> > & aps, 
	unsigned int & tot_aps,
	bool is_accum_aps,
	struct cgraph_node * cnode,
	set<label_sites> & valid_live_nodes,
	bool consider_validity)
{
	DEBUG ("\nget_k_access_paths");
	map<label_sites, set<list<label> > > sent_lss_aps;
	map<label_sites, set<list<label> > > new_lss_aps;
	label_sites stack_lss = stack.get_label_sites ();
	get_k_access_paths (stack_lss, sent_lss_aps, new_lss_aps, tot_aps, is_accum_aps, cnode,
		valid_live_nodes, consider_validity);
	if (new_lss_aps.size ())
		RESULT ("\nError: new_lss_aps not sent to out-nodes");
	if (is_accum_aps)
	{
		sent_lss_aps[stack_lss].clear ();
		collect_access_paths (sent_lss_aps, aps);
	}
}

/**
 * This function adds empty AP to stack node. This is removed by
 * get_k_access_paths(set<list<label> > &) function.
 */

void deterministic_graph::
get_k_access_paths (label_sites & lss,
        map<label_sites, set<list<label> > > & sent_lss_aps,
        map<label_sites, set<list<label> > > & new_lss_aps,
	unsigned int & tot_aps,
	bool is_accum_aps,
	struct cgraph_node * cnode,
	set<label_sites> & valid_live_nodes,
	bool consider_validity)
{
#if DEBUG_CONTAINER
	DEBUG ("\nget_k_aps, lss=<%d,{", lss.first);
	deterministic_node::print_sites (lss.second);
	DEBUG ("}");
#endif

	if (lss == stack.get_label_sites ())
	{
		list<label> base_ap;
		new_lss_aps[lss].insert (base_ap);
	}

	set<label_sites> changed_out_lss;
	// Mark APs of lss as old/sent. Create space for new aps of lss. This
	// is required when lss points to lss, and more new_aps may get added
	// to lss by lss itself.
	set<list<label> > new_src_aps = new_lss_aps[lss];
	if (lss != stack.get_label_sites ())
		tot_aps += new_src_aps.size ();
	if (is_accum_aps)
		sent_lss_aps[lss].insert (new_src_aps.begin (), new_src_aps.end ());
	new_lss_aps.erase (lss);

	deterministic_node * n = nodes[lss];
	map<label, label_sites> * out_edge_list = n->get_out_edge_list_pointer ();
	map<label, label_sites>::iterator outei;
	for (outei = out_edge_list->begin (); outei != out_edge_list->end (); outei++)
	{
		label field = outei->first;
		if (lss == stack.get_label_sites ()
			&& cnode && !program.is_in_scope (field, cnode))
			continue;
		label_sites out_lss = outei->second;

		if (consider_validity && valid_live_nodes.find (out_lss) == valid_live_nodes.end ())
			continue;

		// Send APs of lss to its out-nodes
		if (append_k_access_paths (new_src_aps, field, out_lss, new_lss_aps))
			changed_out_lss.insert (out_lss);
	}
	new_src_aps.clear ();
	
	// Breadth first
#if DEBUG_CONTAINER
	DEBUG ("\nchanged_out_lss of src=<%d,{", lss.first);
	deterministic_node::print_sites (lss.second);
	DEBUG ("}>\n\t");
#endif
	set<label_sites>::iterator lsi;
	for (lsi = changed_out_lss.begin (); lsi != changed_out_lss.end (); lsi++)
	{
		label_sites out_lss = *lsi;
#if DEBUG_CONTAINER
		DEBUG ("<%d,{", out_lss.first);
		deterministic_node::print_sites (out_lss.second);
		DEBUG ("}>");
#endif
		get_k_access_paths (out_lss, sent_lss_aps, new_lss_aps, tot_aps, is_accum_aps, cnode,
			valid_live_nodes, consider_validity);
	}
}

bool deterministic_graph::
append_k_access_paths (set<list<label> > & src_aps,
	label field,
	label_sites & dest_lss,
	map<label_sites, set<list<label> > > & new_lss_aps)
{
	bool has_changed = false;
	set<list<label> >::iterator api;
	for (api = src_aps.begin (); api != src_aps.end (); api++)
	{
		list<label> ap = *api;
		append_ap_field (ap, field);

		if (!ap.size ())
			continue;
		// This check is not required. In a deterministic graph, the
		// same AP computed incrementally, cannot reappear.
		// if (sent_lss_aps[dest_lss].find (ap) != sent_lss_aps[dest_lss].end ())
		//	continue;
		// if (new_lss_aps[dest_lss].find (ap) != new_lss_aps[dest_lss].end ())
		//	continue;

		new_lss_aps[dest_lss].insert (ap);
		has_changed = true;
	}
	return has_changed;
}

void deterministic_graph::
append_ap_field (list<label> & ap, label field)
{
	unsigned int ap_len = ap.size ();
	if (ap_len < MAX_LEN_PRINT)
	{
		ap.push_back (field);
#if DEBUG_CONTAINER
		DEBUG ("\nappended_ap_field=");
		print_access_path (ap);
#endif
	}
	// Required so that MAX_LEN_PRINT is unnecessarily not propagated
	else
		ap.clear ();
}

void deterministic_graph::
print_access_paths (map<label_sites, set<list<label> > > & lss_aps)
{
	map<label_sites, set<list<label> > >::iterator lss_api;
	for (lss_api = lss_aps.begin (); lss_api != lss_aps.end (); lss_api++)
	{
		set<list<label> > aps = lss_api->second;
		print_access_paths (aps);
	}
}

void deterministic_graph::
print_access_paths (set<list<label> > & aps)
{
	set<list<label> >::iterator api;
	for (api = aps.begin (); api != aps.end (); api++)
	{
		list<label> ap = * api;
		print_access_path (ap);
	}
}

void deterministic_graph::
print_access_path (list<label> & ap)
{
	STATS ("\n\t\t");
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
				STATS ("# %s(%d).", var->name, l);
			}
			else
			{
				STATS ("%s(%d).", var->name, l);
			}
		}
		else
		{
			STATS ("%d.", l);
		}
	}
}

void deterministic_graph::
get_graph_stats (unsigned int & node_count,
	unsigned int & edge_count,
	unsigned int & use_sites_count,
	set<site> & unique_use_sites)
{
	unsigned int this_node_count = 0;
	unsigned int this_edge_count = 0;
	unsigned int this_use_sites_count = 0;
	set<site> this_unique_use_sites;

	this_node_count = nodes.size ();
	map<label_sites, deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		deterministic_node * n = ni->second;
		n->get_node_stats (this_edge_count, this_use_sites_count, this_unique_use_sites);
	}

	STATS ("\nthis_node_count=%d, this_edge_count=%d, this_use_sites_count=%d, this_unique_use_sites=%d", 
		this_node_count, this_edge_count, this_use_sites_count, this_unique_use_sites.size ());
	if (this_node_count > 1)
	{
		node_count += this_node_count;
		edge_count += this_edge_count;
		use_sites_count += this_use_sites_count;
		unique_use_sites.insert (this_unique_use_sites.begin (), this_unique_use_sites.end ());
	}
}

bool deterministic_graph::
is_graph_reachability_okay ()
{
	set<label_sites> reachable_nodes;
	label_sites stack_s = stack.get_label_sites ();
	get_reachable_nodes (stack_s, reachable_nodes);
	if (nodes.size () != reachable_nodes.size ())
	{
		RESULT ("\nError: Nodes are unreachable even after clean()");
		return false;
	}
	return true;
}

bool deterministic_graph::
is_graph_labelling_okay ()
{
	bool okay = true;
	map<label_sites, deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		label_sites lss = ni->first;
		deterministic_node * n = ni->second;
                if (!n->is_node_okay (stack))
                {
                        RESULT ("\nError: node=%d not okay", n->get_node_id ());
                        okay = false;
                }

		// Check out-edge list
		map<label, label_sites> out_edges = n->get_out_edge_list ();
		map<label, label_sites>::iterator outei;
		for (outei = out_edges.begin (); outei != out_edges.end (); outei++)
		{
			label out_l = outei->first;
			label_sites out_ls = outei->second;
			deterministic_node * out_n = nodes[out_ls];
                        if (!n->is_out_node_okay (out_l, *out_n))
                        {
                                RESULT ("\nError: Out-node=%d of node=%d not okay", out_n->get_node_id (), n->get_node_id ());
                                okay = false;
                        }
		}

		// Check in-nodes
                set<label_sites> in_nodes = n->get_in_nodes ();
                set<label_sites>::iterator ini;
                for (ini = in_nodes.begin (); ini != in_nodes.end (); ini++)
                {
                        label_sites in_lss = *ini;
                        deterministic_node * in_n = nodes[in_lss];
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

void deterministic_graph::
print_value (const char * file)
{
	DEBUG ("\nlive_graph=");
	DEBUG ("\nstack=%d", stack.get_node_id ());

#if 0
	set<list<label> > aps;
	unsigned int tot_aps;
	get_k_access_paths (aps, tot_aps, true, NULL);
	print_access_paths (aps);
#endif

        RESULT ("\nNodes=%d", nodes.size ());
        if (nodes.size () > 500)
                RESULT ("\nALARM: Nodes=%d", nodes.size ());

	map<label_sites, deterministic_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		deterministic_node * n = ni->second;
		n->print_node (nodes);
	}
}


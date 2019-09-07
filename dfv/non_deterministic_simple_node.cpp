
/************************
 * @author Vini Kanvar
************************/

#include "non_deterministic_simple_node.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

unsigned int non_deterministic_simple_node::
number_of_nodes = 1;

non_deterministic_simple_node::
non_deterministic_simple_node ()
{
	node_id = number_of_nodes;
	number_of_nodes++;
	DEBUG ("\nAdded node %d", node_id);
}

non_deterministic_simple_node::
~non_deterministic_simple_node ()
{
	DEBUG ("\nDeleting non deterministic node %d(%x)", node_id, this);
}

unsigned int non_deterministic_simple_node::
get_node_id ()
{
	return node_id;
}

map<label, set<node_index> > non_deterministic_simple_node::
get_in_edge_list ()
{
	return in_edge_list;
}

map<label, set<node_index> > non_deterministic_simple_node::
get_out_edge_list ()
{
	return out_edge_list;
}

/**
 * This function gets the destination nodes of THIS node through label L.
 *
 * @return true if THIS node is not proper variable node (undef/null/readonly)
 * i.e. the out-edge is missing i.e. the destination is undef. 
 */

bool non_deterministic_simple_node::
get_destination_nodes (label l, node_index stack_id, set<node_index> & destination_nodes)
{
	DEBUG ("\nget_destination_node () of label %d from node %d", l, node_id);

	label node_name = get_node_name (stack_id);
	DEBUG ("\nnode_name=%d", node_name);

	// If THIS is not stack node, then either THIS node represents improper
	// variable or L is a field of THIS node.
	if (node_id != stack_id)
	{
		if (!program.is_proper_var (node_name))
		{
			DEBUG ("\nget_destination_nodes() of node=%d is undef", node_name);
			return true;
		}

		// Set L to the difference of offset of the variable returned
		// by cs_first_vi_for_offset(THIS node's name, l) and the
		// offset of THIS node's variable.
		if (l)
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
				l = var_offset_info->offset - var_info->offset;
				// If L field was not already 0 and has become
				// 0 (after using cs_first_vi_for_offset()),
				// then THIS node is the destination.
				if (!l)
				{
					DEBUG ("\nFound destination: %d", node_id);
					destination_nodes.insert (node_id);
					return true;
				}
			}
		}
	}

	if (out_edge_list.find (l) == out_edge_list.end ())
		return true;

#if DEBUG_CONTAINER
	DEBUG ("\nFound destinations: ");
	set<node_index>::iterator ni;
	for (ni = out_edge_list[l].begin (); ni != out_edge_list[l].end (); ni++)
		DEBUG ("%d,", *ni);
#endif
	
	destination_nodes.insert (out_edge_list[l].begin (), out_edge_list[l].end ());
	return false;
}

/**
 * @return true if any label in LABELS is not proper variable node
 * (undef/null/readonly) i.e. the out-edge is missing i.e. the destination is
 * undef.
 */

bool non_deterministic_simple_node::
get_destination_nodes (set<label> & labels, node_index stack_id, set<node_index> & destination_nodes)
{
	DEBUG ("\nget_destination_nodes ()");
	bool out_edge_missing = false;

	set<label>::iterator li;
	for (li = labels.begin (); li != labels.end (); li++)
	{
		set<node_index> dest_temp;
		out_edge_missing += get_destination_nodes (*li, stack_id, dest_temp);
		destination_nodes.insert (dest_temp.begin (), dest_temp.end ());
	}
	
	return out_edge_missing;
}

/**
 * Given PREFIX_VAR which reaches THIS node, we need to find the nodes from
 * THIS node which correspond to VAR.  This function is called for PREFIX_VAR
 * which has is_heap_var as false (e.g.  heap.13) and has is_proper_var as
 * true.
 * Given x.f.g, this function recursively fetches nodes reached by x then f
 * then g. 
 */

set<node_index> non_deterministic_simple_node::
get_var_node (label var, label prefix_var, map<node_index, non_deterministic_simple_node *> & nodes)
{
	set<node_index> var_nodes;

	if (var == prefix_var)
	{
		var_nodes.insert (node_id);
		return var_nodes;
	}

	csvarinfo_t var_info = VEC_index (csvarinfo_t, program.variable_data, var);
	csvarinfo_t prefix_var_info = VEC_index (csvarinfo_t, program.variable_data, prefix_var);
	label offset_diff = var_info->offset - prefix_var_info->offset;

	if (offset_diff < 0)
		return var_nodes;

	// If PREFIX_VAR is a pointer or a non-record variable (e.g. array,
	// scalar, function), then prefix_var+succ_offset cannot be VAR.
	if (!RECORD_OR_UNION_TYPE_P (prefix_var_info->decl))
		return var_nodes;
	
	map<label, set<node_index> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		label succ_offset = ei->first;
		
		set<node_index> out_nodes = ei->second;
		set<node_index>::iterator ni;
		for (ni = out_nodes.begin (); ni != out_nodes.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes[*ni];
			//n->get_var_node (var, longer_prefix_var_info.id, nodes);

			// Get the variable corresponding to prefix_var+succ_offset i.e. longer_prefix_var

			csvarinfo_t longer_prefix_var_info;
			if (succ_offset == 0)
				longer_prefix_var_info = prefix_var_info;
			// If (offset != 0 || progarm.is_proper_var (prefix_var) || 
			//	offset != UNKNOWN_OFFSET || !program.cs_get_varinfo (prefix_var)->is_heap_var)
			// We never create an UNKNOWN_OFFSET edge, because we
			// can safely assume that any kill in a subsequent
			// statement can kill that UNKNOWN_OFFSET edge.
			else if (!program.unexpandable_var (prefix_var, succ_offset))
			{
				longer_prefix_var_info = program.cs_first_vi_for_offset (program.cs_get_varinfo (prefix_var), succ_offset);
				if (!longer_prefix_var_info)
				{
					RESULT ("\nError: Cannot retrieve variable+offset");
					var_nodes.clear ();
					return var_nodes;
				}
			}
			else
			{
				RESULT ("\nError: Either offset=0 or !unexpandable_var (prefix_var, offset) should have been true in this function");
				var_nodes.clear ();
				return var_nodes;
			}

			n->get_var_node (var, longer_prefix_var_info->id, nodes);
		}
	}
	return var_nodes;
}
/** 
 * This function returns the name (LABEL) of THIS node. Each node has only one
 * name which is labeled on the in-edge from STACK node.
 */

label non_deterministic_simple_node::
get_node_name (node_index stack_id)
{
	map<label, set<node_index> >::iterator ei;
	for (ei = in_edge_list.begin (); ei != in_edge_list.end (); ei++)
	{
		set<node_index> in_nodes = ei->second;
		if (in_nodes.find (stack_id) != in_nodes.end ())
			return ei->first;
	}
	return 0;
}

non_deterministic_simple_node * non_deterministic_simple_node::
get_acyclic_parent (map<node_index, non_deterministic_simple_node *> & nodes)
{
	if (!in_edge_list.size ())
	{
		DEBUG ("\nNode %d is a stack node and/or has no parents", node_id);
		return 0;
	}

	map<label, set<node_index> >::iterator ei;
	for (ei = in_edge_list.begin (); ei != in_edge_list.end (); ei++)
	{
		label l = ei->first;
		set<node_index> pn = ei->second;
		set<node_index>::iterator pi;
		for (pi = pn.begin (); pi != pn.end (); pi++)
		{
			node_index parent_node_id = *pi;
			DEBUG ("\nIn-edge of %d is (%d, label=%d, %d)", node_id, parent_node_id, l, node_id);
			set<node_index> visited_nodes;
			visited_nodes.insert (node_id);
			if (is_acyclic_ancestor (parent_node_id, nodes, visited_nodes))
			{
				DEBUG ("\nNode %d has an acyclic parent %d", node_id, parent_node_id);
				non_deterministic_simple_node * parent_node = nodes[parent_node_id];
				return parent_node;
			}
		}
	}	

	// This may not be an error. For example, when we delete the in-edge of
	// a node with a local variable, and then the node may have no acyclic
	// parent.
	DEBUG ("\nNode %d has a parent but in a cycle with itself", node_id);
	return 0;
}

bool non_deterministic_simple_node::
is_acyclic_ancestor (node_index ancestor, map<node_index, non_deterministic_simple_node *> & nodes, set<node_index> & visited_nodes)
{
	DEBUG ("\n%d->is_acyclic_ancestor (%d)", node_id, ancestor); 

	if (ancestor == node_id)
	{
		DEBUG ("\nNode %d is in a cycle with node %d", ancestor, node_id);
		return false;
	}

	if (visited_nodes.find (ancestor) != visited_nodes.end ())
	{
		DEBUG ("\nNode %d is in a cycle, although not in a cycle with node %d", 
			ancestor, node_id);
		return true;
	}

	visited_nodes.insert (ancestor);

	non_deterministic_simple_node * ancestor_node = nodes[ancestor];
	map<label, set<node_index> > ancestor_in_edges = ancestor_node->in_edge_list;
	map<label, set<node_index> >::iterator ei;
	for (ei = ancestor_in_edges.begin (); ei != ancestor_in_edges.end (); ei++)
	{
		set<node_index> a_in_nodes = ei->second;
		set<node_index>::iterator ni;
		for (ni = a_in_nodes.begin (); ni != a_in_nodes.end (); ni++)
			if (!is_acyclic_ancestor (*ni, nodes, visited_nodes))
			{
				DEBUG ("\nNode %d is in a cycle with node %d", *ni, node_id);
				return false;
			}
	}

	return true;	
}

/**
 * This function collects all the nodes reachable from THIS node. Note that a
 * heap node (with zero or non-zero offset) is considered unreachable if THIS
 * node is the STACK node; heap node with non-zero offset is indirectly
 * reachable from its corresponding heap node with zero offset.
 */

void non_deterministic_simple_node::
get_reachable_nodes (node_index root, map<node_index, non_deterministic_simple_node *> & nodes_map, set<node_index> & reachable_nodes)
{
	// Return if this node has already been visited
	if (reachable_nodes.find (node_id) != reachable_nodes.end ())
		return;

	// A node is unreachable if it is nameless, even though it is reachable
	// from some other node.
	if (is_node_nameless (root))
		return;
 
	reachable_nodes.insert (node_id);

	map<label, set<node_index> >::iterator out_edge_i;
	for (out_edge_i = out_edge_list.begin (); out_edge_i != out_edge_list.end (); out_edge_i++)
	{
		// If THIS is the STACK node, then do not consider a heap node
		// as reachable from THIS node.
		if (node_id == root)
		{
			label v = out_edge_i->first;
			csvarinfo_t variable = program.cs_get_varinfo (v);
			if (variable && variable->is_heap_var)
				continue;
		}
		set<node_index> out_nodes = out_edge_i->second;
		set<node_index>::iterator ni;
		for (ni = out_nodes.begin (); ni != out_nodes.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes_map[*ni];
			n->get_reachable_nodes (root, nodes_map, reachable_nodes);
		}
	}

	// This function is used by clean(). A stack node at non-zero offset
	// will never be cleaned. Therefore, no need to find y.32 which is
	// reachable from y.

	// Mark the reachability of any non-zero offset heap nodes that are
	// reachable from THIS node
	get_heap_reachable_nodes (root, nodes_map, reachable_nodes);
}

/**
 * This function checks if THIS node is a heap node of zero offset. If it is,
 * then it calls GET_REACHABLE_NODES from all the heap field nodes of THIS
 * heap.
 */

void non_deterministic_simple_node::
get_heap_reachable_nodes (node_index root, map<node_index, non_deterministic_simple_node *> & nodes_map, set<node_index> & reachable_nodes)
{
	label this_node_name = get_node_name (root);
	csvarinfo_t this_node_varinfo = program.cs_get_varinfo (this_node_name);
	if (this_node_varinfo->is_heap_var && this_node_varinfo->offset == 0)
	{
		set<label> heap_field_ids;
		program.get_field_var_ids (this_node_varinfo->decl, heap_field_ids);
		non_deterministic_simple_node * stack = nodes_map[root];
		set<node_index> heap_field_nodes;
		stack->get_destination_nodes (heap_field_ids, stack->get_node_id (), heap_field_nodes);

		set<node_index>::iterator ni;
		for (ni = heap_field_nodes.begin (); ni != heap_field_nodes.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes_map[*ni];
			n->get_reachable_nodes (root, nodes_map, reachable_nodes);
		}
	}
}

void non_deterministic_simple_node::
get_reaching_nodes (map<node_index, non_deterministic_simple_node *> & nodes_map, set<node_index> & reaching_nodes)
{
	// Return if this node has already been visited
	if (reaching_nodes.find (node_id) != reaching_nodes.end ())
		return;

	reaching_nodes.insert (node_id);

	map<label, set<node_index> >::iterator in_edge_i;
	for (in_edge_i = in_edge_list.begin (); in_edge_i != in_edge_list.end (); in_edge_i++)
	{
		set<node_index> in_nodes = in_edge_i->second;
		set<node_index>::iterator ni;
		for (ni = in_nodes.begin (); ni != in_nodes.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes_map[*ni];
			n->get_reaching_nodes (nodes_map, reaching_nodes);
		}
	}
}

/**
 * This function finds the nodes connected to THIS node. It also finds the
 * nodes connected to the fields of the variable that THIS node represents.
 */

void non_deterministic_simple_node::
mark_connected_nodes (node_index root, map<node_index, non_deterministic_simple_node *> & nodes, set<node_index> & connected_nodes)
{
	// We do not want to find nodes connected to ROOT node because
	// every node is anyway connected to the ROOT node (directly/indirectly).
	if (node_id == root)
		return;

	// Return if this node has already been visited
	if (connected_nodes.find (node_id) != connected_nodes.end ())
	{
		DEBUG ("\nNodes connected to %d are already marked", node_id);
		return;
	}

	DEBUG ("\nInserting node %d into par-glob-connected-nodes", node_id);
	connected_nodes.insert (node_id);

	// We do not want to find nodes connected to null/readonly/undef nodes
	// because these nodes do not indicate alias relationship.
	label v = get_node_name (root);
	if (!program.is_proper_var (v))
		return;

#if 0
	// If the name of THIS node is y.32, then mark y.0, y.64, and y.96 also
	// as connected. Note that we do not need to find fields of globals
	// because mark_connected_nodes() called by
	// extract_arg_glob_connected_value () already passes all globals.
	label node_name = get_node_name (root);
	set<label> field_ids;
	program.get_field_var_ids (node_name, field_ids);
	non_deterministic_simple_node * stack = nodes[root];
	set<node_index> field_nodes;
	stack->get_destination_nodes (field_ids, root, field_nodes);
	set<node_index>::iterator ni;
	for (ni = field_nodes.begin (); ni != field_nodes. end (); ni++)
	{
		non_deterministic_simple_node * n = nodes[*ni];
		n->mark_connected_nodes (root, nodes, connected_nodes);
	}
#endif
	// If the name of THIS node is y.32, then mark y.64 also as connected.
	// Note that when y.32 is populated, it will recursively populate y.64
	// and so on too. Note that we do not need to insert y.0 because it is
	// not accessible from y.32. In case of access based abstraction, it
	// would be important to insert y.0 if y.0 is connected to y.32 etc via
	// a graph edge in which case out-edges will automatically insert y.0
	// node.
	label node_name = get_node_name (root);
	label next_field_var = program.get_next_field (node_name);
	set<node_index> field_nodes;
	non_deterministic_simple_node * stack = nodes[root];
	stack->get_destination_nodes (next_field_var, root, field_nodes);
	set<node_index>::iterator ni;
	for (ni = field_nodes.begin (); ni != field_nodes. end (); ni++)
	{
		non_deterministic_simple_node * n = nodes[*ni];
		n->mark_connected_nodes (root, nodes, connected_nodes);
	}


	map<label, set<node_index> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		set<node_index> out_n = ei->second;
		set<node_index>::iterator ni;
		for (ni = out_n.begin (); ni != out_n.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes[*ni];
			n->mark_connected_nodes (root, nodes, connected_nodes);
		}
	}
	for (ei = in_edge_list.begin (); ei != in_edge_list.end (); ei++)
	{
		set<node_index> in_n = ei->second;
		set<node_index>::iterator ni;
		for (ni = in_n.begin (); ni != in_n.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes[*ni];
			n->mark_connected_nodes (root, nodes, connected_nodes);
		}
	}
}

/**
 * Checks if there exists at least one in-edge to node NODEI with a variable
 * name.  We can delete a node which has no variable pointing directly to it.
 */

bool non_deterministic_simple_node::
is_node_nameless (node_index stack_id)
{
	DEBUG ("\nStack node %d", stack_id);

	// Stack node does not need a name
	if (node_id == stack_id)
		return false;

	bool found_stack = false;
	map<label, set<node_index> >::iterator ei;
	for (ei = in_edge_list.begin (); ei != in_edge_list.end (); ei++)
	{
		set<node_index> in_nodes = ei->second;

		// If there is an in-edge directly from the root node,
		// then we can say there is a variable directly
		// pointing to this node.
		if (in_nodes.find (stack_id) != in_nodes.end ())
		{
			found_stack = true;
			break;
		}
	}

	// If there is no stack node at the in-edge, then node NODEI is
	// nameless.
	if (!found_stack)
		return true;

	return false;
}

/** 
 * If there is only one in-edge, then it has to be a variable edge because of
 * the above check. Now if NI has only one in-edge and no out-edge, then NI is
 * neither saving any alias information at the in nor saving any pointee
 * information at the out. Therefore, NI is useless and can be deleted. 
*/

bool non_deterministic_simple_node::
is_node_useless (node_index stack_id)
{
	if (node_id == stack_id)
		return false;

	DEBUG ("\nnode %d, in-edges # %d, out-edges # %d", 
		node_id, in_edge_list.size (), out_edge_list.size ());
	if (!in_edge_list.size () || in_edge_list.size () == 1 && out_edge_list.size () == 0)
		return true;

	return false;
}

void non_deterministic_simple_node::
delete_edge (label l, non_deterministic_simple_node & out_node)
{
	// Note that OUT_EDGE_LIST of THIS node may not contain L edge as it
	// may have been deleted earlier, but IN_EDGE_LIST of OUT_NODE may
	// still have the L edge.

	DEBUG ("\ndeleting out edge %d -> %d -> %d", node_id, l, out_node.node_id);
	if (out_edge_list.find (l) != out_edge_list.end ())
	{
		DEBUG ("---done");
		out_edge_list[l].erase (out_node.node_id);
		if (!out_edge_list[l].size ())
			out_edge_list.erase (l);
	}
	else
		DEBUG ("---already deleted");

	DEBUG ("\ndeleting in edge %d <- %d <- %d", out_node.node_id, l, node_id);
	if (out_node.in_edge_list.find (l) != out_node.in_edge_list.end ())
	{
		DEBUG ("---done");
		out_node.in_edge_list[l].erase (node_id);
		if (!out_node.in_edge_list[l].size ())
			out_node.in_edge_list.erase (l);
	}
	else
		DEBUG ("---already deleted");
}

void non_deterministic_simple_node::
delete_in_edges (label l)
{
	DEBUG ("\nDeleting in-edges of node %d", node_id);
	in_edge_list.erase (l);
}

void non_deterministic_simple_node::
delete_out_edges (label l)
{
	DEBUG ("\nDeleting out-edges of node %d", node_id);
	out_edge_list.erase (l);
}

/**
 * This function recursively traverses depth-first from THIS node and N node
 * while checking if their properties are the same. THIS and N nodes belong to
 * graphs with nodes THIS_NODES and N_NODES, respectively. The property could
 * be IS_IN_GRAPH_ISOMORPHIC() or IS_IN_LANGUAGE_SAME().  EQUIV_NODE_PAIRS is
 * populated with the matching nodes in this recursive function.
 * EQUIV_STATE_PAIRS is a set of equivalent states, precomputed using
 * Hopkroft-Karp algorithm for NFAs. EQUIV_STATE_PAIRS is used if the property
 * to be used is IS_IN_LANGUAGE_SAME().
 */

bool non_deterministic_simple_node::
depth_first_comparison (non_deterministic_simple_node & n, 
	map<node_index, non_deterministic_simple_node *> & this_nodes, 
	map<node_index, non_deterministic_simple_node *> & n_nodes, 
	map<node_index, node_index> & equiv_node_pairs,
	map<state_index, state_index, state_order> & equiv_state_pairs,
	bool reverse_node_property)
{
	DEBUG ("\ndepth_first_comparison (): THIS node %d, N Node %d", node_id, n.node_id);

	map<node_index, node_index>::iterator vi;

	vi = equiv_node_pairs.find (node_id);
	// if (N1,N2) is in EQUIV_NODE_PAIRS
	if (vi != equiv_node_pairs.end () && vi->second == n.node_id)
	{
		DEBUG ("\nN1=%d and N2=%d are already visited", node_id, n.node_id);
		return true;
	}

	// If (N1,*) is in EQUIV_NODE_PAIRS. Note that unlike the automorphism
	// case of IS_IN_GRAPH_ISOMORPHIC, (N1,N1) cannot exist since the nodes
	// in the pair belong to two graphs, respectively.
	if (vi != equiv_node_pairs.end ())
	{
		DEBUG ("\nN1=%d has same property as node %d and not with N2=%d", 
			node_id, vi->second, n.node_id);
		return false;
	}

	vi = equiv_node_pairs.find (n.node_id);
	// If (N2,*) is in EQUIV_NODE_PAIRS. Note that unlike the automorphism
	// case of IS_IN_GRAPH_ISOMORPHIC, (N1,N1) cannot exist since the nodes
	// in the pair belong to two graphs, respectively.
	if (vi != equiv_node_pairs.end ())
	{
		DEBUG ("\nN2=%d has same property as node %d and not with N1=%d", 
			n.node_id, vi->second, node_id);
		return false;
	}

	// Depth-first comparison of THIS and N can return a true comparison if
	// both nodes have the same out-degree.
	if (out_edge_list.size () != n.out_edge_list.size ())
	{
#if DEBUG_CONTAINER
		DEBUG ("\nout_edge_list size of THIS node %d = %d, of N node %d = %d", 
			node_id, out_edge_list.size (), n.node_id, n.out_edge_list.size ());
		map<node_index, non_deterministic_simple_node *> nodes;
		print_node (NULL, nodes);
		n.print_node (NULL, nodes);
#endif

		return false;
	}

	// Add (N1,N2) and (N2,N1) to EQUIV_NODE_PAIRS
	equiv_node_pairs[node_id] = n.node_id;
	equiv_node_pairs[n.node_id] = node_id;

	// The values of NODE_ID and N.NODE_ID are never the same since the
	// corresponding nodes are from different graphs.
	
	// Moving depth-first:
	// The out-edges of THIS node may not be in the same order as the
	// out-edges of node N. For example,
	// G1=(stack1,f,n1),(n1,f,n1),(n1,f,n4),G2=(stack2,f,n3),(n3,f,n3),(n3,f,n2).
	// Here G1 and G2 are the same, even though out-edges of
	// n1={(f,n1),(f,n4)} and out-edges of n3={(f,n2),(f,n3)}. Therefore,
	// we need to find all the out-edges of THIS node in the out-edges of
	// node N.

	DEBUG ("\nFinding out-edges of node %d in the out-edges of %d", node_id, n.node_id);
	map<label, set<node_index> >::iterator out_this_i;
	for (out_this_i = out_edge_list.begin (); out_this_i != out_edge_list.end (); out_this_i++)
	{
		label l_this = out_this_i->first;

		if (!depth_first_edge_comparison (n, l_this, this_nodes, n_nodes, equiv_node_pairs, equiv_state_pairs, reverse_node_property))
		{
			DEBUG ("\nout-edges with label %d of node %d are not in the out-edges of %d", 
				l_this, node_id, n.node_id);

			equiv_node_pairs.erase (node_id);
			equiv_node_pairs.erase (n.node_id);
			return false;
		}
	}
	
	// Till this point we can claim that all the out-nodes of THIS have an
	// equivalent counterpart in child nodes of node N.

	// If all the out_nodes of node N have been visited, then we can claim
	// that all the out-nodes of node N also have an equivalent
	// counterpart in child nodes of THIS node.
	map<label, set<node_index> >::iterator ei;
	for (ei = n.out_edge_list.begin (); ei != n.out_edge_list.end (); ei++)
	{
		set<node_index> n_out_nodes = ei->second;
		set<node_index>::iterator ni;
		for (ni = n_out_nodes.begin (); ni != n_out_nodes.end (); ni++)
			if (equiv_node_pairs.find (*ni) == equiv_node_pairs.end ())
			{
				DEBUG ("\nNode %d does not have an equivalent", *ni);
				equiv_node_pairs.erase (node_id);
				equiv_node_pairs.erase (n.node_id);
				return false;
			}
	}

	DEBUG ("\ndepth_first_comparison ()::Nodes %d and %d are same", node_id, n.node_id);
	return true;
}

bool non_deterministic_simple_node::
depth_first_edge_comparison (non_deterministic_simple_node & n, 
	label l, 
	map<node_index, 
	non_deterministic_simple_node *> & this_nodes, 
	map<node_index, non_deterministic_simple_node *> & n_nodes, 
	map<node_index, node_index> & equiv_node_pairs,
	map<state_index, state_index, state_order> & equiv_state_pairs,
	bool reverse_node_property)
{
	DEBUG ("\ndepth_first_edge_comparison(): THIS node %d, N node %d", node_id, n.node_id);

	// Depth-first comparison of THIS and N can return a true comparison if
	// both nodes have the same out-degree.
	set<node_index> out_nodes_this;
	if (out_edge_list.find (l) != out_edge_list.end ())
		out_nodes_this = out_edge_list[l];
	set<node_index> out_nodes_n;
	if (n.out_edge_list.find (l) != n.out_edge_list.end ())
		out_nodes_n = n.out_edge_list[l];
	if (out_nodes_this.size () != out_nodes_n.size ())
	{
		DEBUG ("\nNumber of out-nodes with label %d from node %d = %d and from node %d = %d", 
			l, node_id, out_nodes_this.size (), n.node_id, out_nodes_n.size ());
		return false;
	}

	DEBUG ("\nFinding out-nodes of node %d with label %d in the out-nodes of %d", node_id, l, n.node_id);
	set<node_index>::iterator out_nodes_this_i;
	for (out_nodes_this_i = out_nodes_this.begin (); out_nodes_this_i != out_nodes_this.end (); out_nodes_this_i++)
	{
		node_index out_node_this_id = *out_nodes_this_i;
		DEBUG ("\nComparing node %d with the out-nodes of %d", out_node_this_id, n.node_id);
		non_deterministic_simple_node * out_node_this = this_nodes[out_node_this_id];

		if (!out_node_this->depth_first_node_comparison (out_nodes_n, this_nodes, n_nodes, equiv_node_pairs, equiv_state_pairs, reverse_node_property))
		{
			DEBUG ("\nnode %d is not in the out-nodes of %d", out_node_this_id, n.node_id);
			return false;
		}
	}
	
	DEBUG ("\nOut-edges of %d and %d are same", node_id, n.node_id);
#if DEBUG_CONTAINER
	map<node_index, node_index>::iterator vpi;
	DEBUG ("\nEquivalent node pairs: ");
	for (vpi = equiv_node_pairs.begin (); vpi != equiv_node_pairs.end (); vpi++)
		DEBUG ("(%d,%d),", vpi->first, vpi->second);
#endif
	return true;
}

bool non_deterministic_simple_node::
depth_first_node_comparison (set<node_index> nodes_list, 
	map<node_index, non_deterministic_simple_node *> & this_nodes, 
	map<node_index, non_deterministic_simple_node *> & n_nodes, 
	map<node_index, node_index> & equiv_node_pairs,
	map<state_index, state_index, state_order> & equiv_state_pairs,
	bool reverse_node_property)
{
	DEBUG ("\ndepth_first_node_comparison(): THIS node %d", node_id);

	DEBUG ("\nNODES_LIST: ");
	set<node_index>::iterator nodes_i;
#if DEBUG_CONTAINER
	for (nodes_i = nodes_list.begin (); nodes_i != nodes_list.end (); nodes_i++)
		DEBUG ("%d,", *nodes_i);
#endif

	node_index matching_node_id;
	if (equiv_node_pairs.find (node_id) != equiv_node_pairs.end ())
		matching_node_id = equiv_node_pairs[node_id];
	else
		// Even if NODE_ID has not been visited, we want to check
		// if NODE_ID is present in NODES_LIST 
		matching_node_id = node_id;

	if (nodes_list.find (matching_node_id) != nodes_list.end ())
	{
		DEBUG ("\nNodes %d and %d are same", node_id, matching_node_id);
		// If NODE_ID has not been visited, then the
		// MATCHING_NODE_ID which is NODE_ID itself, is saved in
		// EQUIV_NODE_PAIRS.
		equiv_node_pairs[node_id] = matching_node_id;
		return true;
	}

	for (nodes_i = nodes_list.begin (); nodes_i != nodes_list.end (); nodes_i++)
	{
		node_index n_id = *nodes_i;
		non_deterministic_simple_node * n = n_nodes[n_id];
		
		// The matching property could be IS_IN_GRAPH_ISOMORPHIC() or
		// IS_IN_LANGUAGE_SAME().
		if (is_node_property_same (*n, this_nodes, n_nodes, equiv_state_pairs, reverse_node_property)
			&& depth_first_comparison (*n, this_nodes, n_nodes, equiv_node_pairs, equiv_state_pairs, reverse_node_property))
		{
			DEBUG ("\nNodes %d and %d are same", node_id, n->node_id);
			return true;
		}
	}
		
	DEBUG ("\nNode %d is not found", node_id);
	return false;
}

bool non_deterministic_simple_node::
is_node_proper (non_deterministic_simple_node & n)
{
	label name = n.get_node_name (node_id);
	return program.is_proper_var (name);
}

bool non_deterministic_simple_node::
are_nodes_improper (non_deterministic_simple_node & n1, non_deterministic_simple_node & n2)
{
	label name1 = n1.get_node_name (node_id);
	label name2 = n2.get_node_name (node_id);
	
	if (!program.is_proper_var (name1) && name1 == name2)
		return true;
	return false;
}

/**
 * Returns true if THIS and N nodes have the same in-property. This function is
 * called when THIS belongs to a graph containing THIS_NODES, and N belongs to
 * a graph containing N_NODES. The algorithm of this function does not work
 * when THIS and N nodes belong to the same graph.
 */

bool non_deterministic_simple_node::
is_node_property_same (non_deterministic_simple_node & n, 
	map<node_index, non_deterministic_simple_node *> & this_nodes, 
	map<node_index, non_deterministic_simple_node *> & n_nodes,
	map<state_index, state_index, state_order> & equiv_state_pairs,
	bool reverse_node_property)
{
	struct timeval start;
	start_timer (start);

	DEBUG ("\nis_node_property_same () -- two graphs");

	// REVERSE_NODE_PROPERTY is set to true when we want to check using
	// another node property as to whether or not the value comparison is
	// okay.

	if ((!reverse_node_property && node_property == in_language) ||
		(reverse_node_property && node_property == in_isomorphism))
	{
		DEBUG ("\nLANGUAGE_AS_NODE_PROPERTY");
		if (!equiv_state_pairs.size ())
		{
			RESULT ("\nError: EQUIV_STATE_PAIRS has not been precomputed.");
			return false;
		}
		bool b = is_in_language_same (node_id, n.node_id, equiv_state_pairs);	
		return b;
	}
	if ((!reverse_node_property && node_property == in_isomorphism) ||
		(reverse_node_property && node_property == in_language))
	{
		DEBUG ("\nISOMORPHISM_AS_NODE_PROPERTY");
		map<node_index, node_index> equiv_node_pairs;
		bool is_same = is_in_graph_isomorphic (n, this_nodes, n_nodes, equiv_node_pairs);

#if CHECK_CONTAINER
		if (is_same)
		{
			DEBUG ("\nis_node_comparison_okay(%d,%d)", node_id, n.node_id);
			is_node_comparison_okay (n, this_nodes, n_nodes, equiv_node_pairs); 
			n.is_node_comparison_okay (*this, n_nodes, this_nodes, equiv_node_pairs);
		}
#endif

		return is_same;
	}
	RESULT ("\nError: node_property not initialized correctly");
	return false;
}

/**
 * Returns true if N1 and N2 nodes have the same in-property. This function is
 * called when N1 and N2 belong to the same graph containing NODES. THIS node
 * is the STACK node.
 */

bool non_deterministic_simple_node::
is_node_property_same (non_deterministic_simple_node & n1, 
	non_deterministic_simple_node & n2,
	map<node_index, non_deterministic_simple_node *> & nodes,
	bool is_loop_merge)
{
	struct timeval start;
	start_timer (start);

	DEBUG ("\nis_node_property_same () -- same graph");

	if (are_nodes_improper (n1, n2))
	{
		DEBUG ("\nnodes %d %d are same improper", n1.node_id, n2.node_id);
		stop_timer (start, is_node_property_same_stats);
		return true;
	}

	if (node_property == in_language && !is_loop_merge)
	{
		DEBUG ("\nLANGUAGE_AS_NODE_PROPERTY");
		state_index n1_state;
		state_index n2_state;
		n1_state.insert (n1.node_id);
		n2_state.insert (n2.node_id);
		set<set<state_index> > equiv_states;
		bool is_same = is_in_language_same (node_id, n1_state, n2_state, nodes, equiv_states);

#if CHECK_CONTAINER
		state_index root;
		root.insert (node_id);
		set<state_index> visited_dfa_states;
		bool is_same_check = is_in_language_comparison_okay (node_id, root, n1.node_id, n2.node_id, nodes, visited_dfa_states);
		if (is_same != is_same_check)
		{
			RESULT ("\nError: is_in_language_same (n1=%d,n2=%d) of same graph not okay", 
				n1.node_id, n2.node_id);
			stop_timer (start, is_node_property_same_stats);
			return false;
		}
		RESULT ("\nis_in_language_same (n1=%d,n2=%d)=%d of same graph okay \\m/", 
			n1.node_id, n2.node_id, is_same);
#endif
		stop_timer (start, is_node_property_same_stats);
		return is_same;
	}

	if (node_property == in_isomorphism)
	{
		DEBUG ("\nISOMORPHISM_AS_NODE_PROPERTY");
		map<node_index, node_index> equiv_node_pairs;
		bool is_same = n1.is_in_graph_isomorphic (n2, nodes, nodes, equiv_node_pairs);

#if CHECK_CONTAINER
		if (is_same)
		{
			DEBUG ("\nis_node_comparison_okay(%d,%d)", n1.node_id, n2.node_id);
			n1.is_node_comparison_okay (n2, nodes, nodes, equiv_node_pairs); 
			n2.is_node_comparison_okay (n1, nodes, nodes, equiv_node_pairs);
		}
#endif
		stop_timer (start, is_node_property_same_stats);
		return is_same;
	}
	if (node_property == name || is_loop_merge)
	{
		DEBUG ("\nNAME AS NODE PROPERTY");

		// Each node has only one name which is labeled on the edge
		// from THIS (STACK) node.
		label name1 = n1.get_node_name (node_id);
		label name2 = n2.get_node_name (node_id);
		if (name1 == name2)
		{
			stop_timer (start, is_node_property_same_stats);
			return true;
		}
		stop_timer (start, is_node_property_same_stats);
		return false;
	}

	stop_timer (start, is_node_property_same_stats);
	RESULT ("\nError: node_property not initialized correctly");
	return false;
}

/**
 * This function recursively checks if THIS node and node N have the same
 * in-graphs. THIS and N are nodes belong to graphs with nodes THIS_NODES and
 * N_NODES, respectively. This function identifies whether the preceding nodes
 * of THIS and N form isomorphic graphs. It identifies automorphism if THIS and
 * N nodes belong to the same graph (in which case THIS_NODES is same as
 * N_NODES).
 */

bool non_deterministic_simple_node::
is_in_graph_isomorphic (non_deterministic_simple_node & n, 
	map<node_index, non_deterministic_simple_node *> & this_nodes, 
	map<node_index, non_deterministic_simple_node *> & n_nodes, 
	map<node_index, node_index> & equiv_node_pairs)
{
	DEBUG ("\nis_in_graph_isomorphic (): THIS node %d, N Node %d", node_id, n.node_id);

#if DEBUG_CONTAINER
	map<node_index, node_index>::iterator vpi;
	DEBUG ("\nEquivalent node pairs: ");
	for (vpi = equiv_node_pairs.begin (); vpi != equiv_node_pairs.end (); vpi++)
		DEBUG ("(%d,%d),", vpi->first, vpi->second);
#endif

	map<node_index, node_index>::iterator vi;

	vi = equiv_node_pairs.find (node_id);
	// if (N1,N2) is in EQUIV_NODE_PAIRS
	if (vi != equiv_node_pairs.end () && vi->second == n.node_id)
	{
		DEBUG ("\nN1=%d and N2=%d are already visited", node_id, n.node_id);
		return true;
	}

	// If (N1,*) is in EQUIV_NODE_PAIRS. However, if (N1,N1) is found in
	// EQUIV_NODE_PAIRS, we do not want to deny a possible match (N1,N2).
	if (vi != equiv_node_pairs.end () && vi->first != vi->second)
	{
		DEBUG ("\nN1=%d is isomorphic with node %d and not with N2=%d", 
			node_id, vi->second, n.node_id);
		return false;
	}

	vi = equiv_node_pairs.find (n.node_id);
	// If (N2,*) is in EQUIV_NODE_PAIRS. However, if (N2,N2) is found in
	// EQUIV_NODE_PAIRS, we do not want to deny a possible match (N1,N2).
	if (vi != equiv_node_pairs.end () && vi->first != vi->second)
	{
		DEBUG ("\nN2=%d is isomorphic with node %d and not with N1=%d", 
			n.node_id, vi->second, node_id);
		return false;
	}

	if (in_edge_list.size () != n.in_edge_list.size ())
	{
		DEBUG ("\nin_edge_list size of THIS node %d = %d, of N node %d = %d", 
			node_id, in_edge_list.size (), n.node_id, n.in_edge_list.size ());
#if DEBUG_CONTAINER
		print_node_reverse (NULL);
		n.print_node_reverse (NULL);
#endif

		return false;
	}

	// Add (N1,N2) and (N2,N1) to EQUIV_NODE_PAIRS
	equiv_node_pairs[node_id] = n.node_id;
	equiv_node_pairs[n.node_id] = node_id;

	if (node_id == n.node_id)
	{
		DEBUG ("\nCommon node: N1=N2=%d are obviously the same", node_id);
		return true;
	}

	// The in-edges of THIS node may not be in the same order as the
	// in-edges of node N. For example,
	// (n2,g,n3),(n2,g,n4),(n3,f,n5),(n4,f,n1),(n5,g,n3),(n1,g,n4). Here n3
	// and n4 are indistinguishable, even though in-edges of
	// n3={(n2,g),(n5,g)} and in-edges of n4={(n1,g),(n2,g)}. Therefore, we
	// need to find all the in-edges of THIS node in the in-edges of node N.

	DEBUG ("\nFinding in-edges of node %d in the in-edges of %d", node_id, n.node_id);
	map<label, set<node_index> >::iterator in_this_i;
	for (in_this_i = in_edge_list.begin (); in_this_i != in_edge_list.end (); in_this_i++)
	{
		label l_this = in_this_i->first;

		if (!is_in_edge_list_isomorphic (n, l_this, this_nodes, n_nodes, equiv_node_pairs))
		{
			DEBUG ("\nin-edges with label %d of node %d are not in the in-edges of %d", 
				l_this, node_id, n.node_id);

			equiv_node_pairs.erase (node_id);
			equiv_node_pairs.erase (n.node_id);
			return false;
		}
	}
	
	// Till this point we can claim that all the in-nodes of THIS have an
	// indistinguishable counterpart in parent of node N.

	// If all the in_nodes of node N have been visited, then we can claim
	// that all the in-nodes of node N also have an indistinguishable
	// counterpart in parent of THIS node.
	map<label, set<node_index> >::iterator ei;
	for (ei = n.in_edge_list.begin (); ei != n.in_edge_list.end (); ei++)
	{
		set<node_index> n_in_nodes = ei->second;
		set<node_index>::iterator ni;
		for (ni = n_in_nodes.begin (); ni != n_in_nodes.end (); ni++)
			if (equiv_node_pairs.find (*ni) == equiv_node_pairs.end ())
			{
				equiv_node_pairs.erase (node_id);
				equiv_node_pairs.erase (n.node_id);
				return false;
			}
	}

	DEBUG ("\nIn-graph of nodes %d and %d are same", node_id, n.node_id);
	return true;
}

bool non_deterministic_simple_node::
is_in_edge_list_isomorphic (non_deterministic_simple_node & n, 
	label l, 
	map<node_index, non_deterministic_simple_node *> & this_nodes, 
	map<node_index, non_deterministic_simple_node *> & n_nodes, 
	map<node_index, node_index> & equiv_node_pairs)
{
	DEBUG ("\nis_in_edge_list_isomorphic(): THIS node %d, N node %d", node_id, n.node_id);

	set<node_index> in_nodes_this;
	if (in_edge_list.find (l) != in_edge_list.end ())
		in_nodes_this = in_edge_list[l];
	set<node_index> in_nodes_n;
	if (n.in_edge_list.find (l) != n.in_edge_list.end ())
		in_nodes_n = n.in_edge_list[l];
	if (in_nodes_this.size () != in_nodes_n.size ())
	{
		DEBUG ("\nNumber of in-nodes with label %d from node %d = %d and from node %d = %d", 
			l, node_id, in_nodes_this.size (), n.node_id, in_nodes_n.size ());
		return false;
	}

	DEBUG ("\nFinding in-nodes of node %d with label %d in the in-nodes of %d", node_id, l, n.node_id);
	set<node_index>::iterator in_nodes_this_i;
	for (in_nodes_this_i = in_nodes_this.begin (); in_nodes_this_i != in_nodes_this.end (); in_nodes_this_i++)
	{
		node_index in_node_this_id = *in_nodes_this_i;
		DEBUG ("\nComparing node %d with the in-nodes of %d", in_node_this_id, n.node_id);
		non_deterministic_simple_node * in_node_this = this_nodes[in_node_this_id];

		if (!in_node_this->is_in_node_list_isomorphic (in_nodes_n, this_nodes, n_nodes, equiv_node_pairs))
		{
			DEBUG ("\nnode %d is not in the in-nodes of %d", in_node_this_id, n.node_id);
			return false;
		}
	}
	
	DEBUG ("\nIn-edges of %d and %d are same", node_id, n.node_id);
	return true;
}

/** 
 * Returns true if THIS node and one of the nodes in NODES_LIST have the same
 * in-graphs.  THIS node is part of the graph containing THIS_NODES map, and
 * NODES_LIST is part of the graph containing N_NODES map.
 */

bool non_deterministic_simple_node::
is_in_node_list_isomorphic (set<node_index> nodes_list, 
	map<node_index, non_deterministic_simple_node *> & this_nodes, 
	map<node_index, non_deterministic_simple_node *> & n_nodes, 
	map<node_index, node_index> & equiv_node_pairs)
{
	DEBUG ("\nis_element_of_node_list(): THIS node %d", node_id);

	DEBUG ("\nNODES_LIST: ");
	set<node_index>::iterator nodes_i;
#if DEBUG_CONTAINER
	for (nodes_i = nodes_list.begin (); nodes_i != nodes_list.end (); nodes_i++)
		DEBUG ("%d,", *nodes_i);
#endif

	node_index matching_node_id;
	if (equiv_node_pairs.find (node_id) != equiv_node_pairs.end ())
		matching_node_id = equiv_node_pairs[node_id];
	else
		// Even if NODE_ID has not been visited, we want to check
		// if NODE_ID is present in NODES_LIST 
		matching_node_id = node_id;

	if (nodes_list.find (matching_node_id) != nodes_list.end ())
	{
		DEBUG ("\nNodes %d and %d are same", node_id, matching_node_id);
		// If NODE_ID has not been visited, then the
		// MATCHING_NODE_ID which is NODE_ID itself, is saved in
		// EQUIV_NODE_PAIRS.
		equiv_node_pairs[node_id] = matching_node_id;
		return true;
	}

	for (nodes_i = nodes_list.begin (); nodes_i != nodes_list.end (); nodes_i++)
	{
		node_index n_id = *nodes_i;
		non_deterministic_simple_node * n = n_nodes[n_id];
		
		if (is_in_graph_isomorphic (*n, this_nodes, n_nodes, equiv_node_pairs))
		{
			DEBUG ("\nNodes %d and %d are same", node_id, n->node_id);
			return true;
		}
	}
		
	DEBUG ("\nNode %d is not found", node_id);
	return false;
}

/**
 * This function checks if N1 node and node N2 accept the same language.  This
 * function is called when N1 and N2 nodes belong to separate graphs.  Note
 * that this algorithm does not work when N1 and N nodes are from the same
 * graph.  The algorithm is as follows: EQUIV_STATE_PAIRS are precomputed by
 * Hopkroft-Karp algorithm.  N1 and N2 are not equivalent if there exists a pair
 * in EQUIV_STATE_PAIRS which contains only one of N1 and N2; otherwise they are
 * equivalent.
 */

bool non_deterministic_simple_node::
is_in_language_same (node_index n1, node_index n2,
	map<state_index, state_index, state_order> & equiv_state_pairs)
{
	map<state_index, state_index, state_order>::iterator pi;
	for (pi = equiv_state_pairs.begin (); pi != equiv_state_pairs.end (); pi++)
	{
		state_index s1 = pi->first;
		state_index s2 = pi->second;
		if (s1.find (n1) != s1.end () || s2.find (n1) != s2.end ())
			if (s1.find (n2) == s1.end () && s2.find (n2) == s2.end ())
			{
				DEBUG ("\nFound n1 %d but not n2 %d", n1, n2);
				return false;
			}
		if (s1.find (n2) != s1.end () || s2.find (n2) != s2.end ())
			if (s1.find (n1) == s1.end () && s2.find (n1) == s2.end ())
			{
				DEBUG ("\nFound n2 %d but node n1 %d", n2, n1);
				return false;
			}
	}

	return true;
}

/**
 * This function checks if nodes N1 and N2 accept the same language. This
 * function is called when nodes N1 and N2 belong to the same graph containing
 * NODES. The algorithm is as follows: Start from N1 and N2 and keep finding
 * language equivalent states by moving on the predecessor edges until the
 * states are found language equivalent. Note: This is same as marking start
 * node as end node, reversing the direction of all the edges, and then running
 * the HK algorithm starting from N1 and N2. In the algorithm above, we work on
 * the original graph itself.
 */

bool non_deterministic_simple_node::
is_in_language_same (node_index root, 
	state_index s1, 
	state_index s2,
	map<node_index, non_deterministic_simple_node *> & nodes,
	set<set<state_index> > & equiv_states)
{
	if (s1 == s2)
		return true;
	if (!s1.size ())
		return false;
	if (!s2.size ())
		return false;
	if (s1.find (root) != s1.end () && s2.find (root) == s2.end ())
		return false;
	if (s2.find (root) != s2.end () && s1.find (root) == s1.end ())
		return false;

	// Find equivalence classes containing S1 and S2. If they are the same,
	// return true. Else merge them.
	if (are_states_merged (s1, s2, equiv_states))
		return true;
	
	// Prepare predecessor DFA states of S1 and S2
	map<label, state_index> dfa_s1_in_edges;
	get_in_dfa_edges (root, s1, dfa_s1_in_edges, nodes);
	map<label, state_index> dfa_s2_in_edges;
	get_in_dfa_edges (root, s2, dfa_s2_in_edges, nodes);
	// If the IN labels are different
	if (dfa_s1_in_edges.size () != dfa_s2_in_edges.size ())
		return false;

	map<label, state_index>::iterator s1_in_i;
	map<label, state_index>::iterator s2_in_i;
	for (s1_in_i = dfa_s1_in_edges.begin (), s2_in_i = dfa_s2_in_edges.begin ();
		s1_in_i != dfa_s1_in_edges.end ();
		s1_in_i++, s2_in_i++)
	{
		label l = s1_in_i->first;
		if (s2_in_i->first != l)
			return false;
		state_index s1_in_state = s1_in_i->second;
		state_index s2_in_state = s2_in_i->second;
		if (!is_in_language_same (root, s1_in_state, s2_in_state, nodes, equiv_states))
			return false;
	}
	return true;
}

/**
 * Find equivalence classes in EQUIV_STATES containing S1 and S2. If they are
 * the same, return true. Else merge them and return false.
 */

bool non_deterministic_simple_node::
are_states_merged (state_index & s1, state_index & s2, set<set<state_index> > & equiv_states)
{
	set<set<state_index> >::iterator esi;
	set<set<state_index> >::iterator s1i = equiv_states.end ();
	set<set<state_index> >::iterator s2i = equiv_states.end ();
	for (esi = equiv_states.begin (); esi != equiv_states.end (); esi++)
	{
		set<state_index> s = *esi;
		// Find the equivalence class containing S1
		if (s.find (s1) != s.end ())
			s1i = esi;
		// Find the equivalence class containing S2
		if (s.find (s2) != s.end ())
		{
			s2i = esi;
			// If S1 and S2 are in the same equivalence class
			if (s1i == s2i)
				return true;
		}
	}

	if (s1i != equiv_states.end ())
	{
		// If equivalence classes of S1 and S2 exist, merge them
		if (s2i != equiv_states.end ())
		{
			// Create a merged equivalence class, erase old classes
			// containing S1 and S2, and insert merged equivalence
			// class.
			set<state_index> merged_set = *s1i;
			merged_set.insert (s2i->begin (), s2i->end ());
			equiv_states.erase (s1i);
			equiv_states.erase (s2i);
			equiv_states.insert (merged_set);
		}
		// Else if equivalence class of S1 exists, add S2 to it
		else
		{ 
			// Create a merged equivalence class, erase old classes
			// containing S1 and S2, and insert merged equivalence
			// class.
			set<state_index> merged_set = *s1i;
			merged_set.insert (s2);
			equiv_states.erase (s1i);
			equiv_states.insert (merged_set);
		}
	}
	// Else if equivalence class of S2 exists, add S1 to it
	else if (s2i != equiv_states.end ())
	{
		// Create a merged equivalence class, erase old classes
		// containing S1 and S2, and insert merged equivalence
		// class.
		set<state_index> merged_set = *s2i;
		merged_set.insert (s1);
		equiv_states.erase (s2i);
		equiv_states.insert (merged_set);
	}
	else
	{
		// Create a merged equivalence class, and insert merged
		// equivalence class.
		set<state_index> merged_set;
		merged_set.insert (s1);
		merged_set.insert (s2);
		equiv_states.insert (merged_set);
	}

	return false;
}

void non_deterministic_simple_node::
get_out_dfa_edges (node_index root, 
	state_index state, 
	map<label, state_index> & dfa_state_out_edges, 
	map<node_index, non_deterministic_simple_node *> & nodes) 
{
	DEBUG ("\nget_out_dfa_edges ()");
	set<node_index>::iterator ni;
	for (ni = state.begin (); ni != state.end (); ni++)
	{
		if (nodes.find (*ni) == nodes.end ())
		{
			RESULT ("\nError: cannot find node %d", *ni);
			return;
		}
		non_deterministic_simple_node * n = nodes[*ni];
		map<label, set<node_index> > n_out_edges = n->out_edge_list;
		map<label, set<node_index> >::iterator ei;
		for (ei = n_out_edges.begin (); ei != n_out_edges.end (); ei++)
		{
			label l = ei->first;
			set<node_index> out_nodes = ei->second;
			dfa_state_out_edges[l].insert (out_nodes.begin (), out_nodes.end ());
		}
	}
}

/**
 * This function is called to find the in-language of nodes in STATE.
 */

void non_deterministic_simple_node::
get_in_dfa_edges (node_index root, 
	state_index state, 
	map<label, state_index> & dfa_state_in_edges, 
	map<node_index, non_deterministic_simple_node *> & nodes)
{
	DEBUG ("\nget_in_dfa_edges ()");
	set<node_index>::iterator ni;
	for (ni = state.begin (); ni != state.end (); ni++)
	{
		if (nodes.find (*ni) == nodes.end ())
		{
			RESULT ("\nError: cannot find node %d", *ni);
			return;
		}
		non_deterministic_simple_node * n = nodes[*ni];
		map<label, set<node_index> > n_in_edges = n->in_edge_list;
		map<label, set<node_index> >::iterator ei;
		for (ei = n_in_edges.begin (); ei != n_in_edges.end (); ei++)
		{
			label l = ei->first;
			set<node_index> in_nodes = ei->second;

#if 0
			// If in-node is ROOT, then check if L is a temporary
			// variable; if yes, ignore it. However, the problem
			// here is that this merging will also merge two
			// temporary variables.
			if (in_nodes.find (root) != in_nodes.end ())	
			{
				csvarinfo_t variable = program.cs_get_varinfo (l);
				if (variable && variable->decl 
					&& DECL_ARTIFICIAL (variable->decl))
					continue;
			}
#endif

			// We want to merge STATE1 and STATE2 even if their
			// in-languages are L.f* and L. Therefore, we ignore
			// in-nodes which are accessed via self-loops (denoting
			// f*).
			in_nodes.erase (*ni);

			dfa_state_in_edges[l].insert (in_nodes.begin (), in_nodes.end ());
		}
	}
}

/** 
 * This function inserts a new edge with label L to the node DEST.  It may lead
 * to making the graph non-deterministic in terms of the labels on the edges.
 * It also updates the incoming edge list of the DEST node.
 */

void non_deterministic_simple_node::
insert_edge (label l, non_deterministic_simple_node & dest, node_index stack_id)
{
	DEBUG ("\nInserting edge from %d -> %d -> %d", node_id, l, dest.node_id);
	DEBUG ("\nStack id=%d", stack_id);

	// Do not add any out edge from an improper node
	label node_name = get_node_name (stack_id);
	// If THIS is not stack and THIS is improper variable node, then do not
	// insert edge.
	if (stack_id != node_id && !program.is_proper_var (node_name))
	{
		DEBUG ("\nDo not insert edge from node_name=%d", node_name);
		return;
	}

	out_edge_list[l].insert (dest.node_id);
	dest.in_edge_list[l].insert (node_id);
}

/**
 * Transfer IN_EDGE_LIST of N to THIS.
 */

void non_deterministic_simple_node::
transfer_in_edges (non_deterministic_simple_node & n, map<node_index, non_deterministic_simple_node *> & nodes, node_index stack_id)
{
	struct timeval start;	
	start_timer (start);

	DEBUG ("\nTransfer in edges of node %d to node %d", n.get_node_id (), node_id);

	map<label, set<node_index> > n_in_edges = n.get_in_edge_list ();
	// Iterate over all in edges of N2
	map<label, set<node_index> >::iterator n_in_ei;
	for (n_in_ei = n_in_edges.begin (); n_in_ei != n_in_edges.end (); n_in_ei++)
	{
		label l = n_in_ei->first;
		set<node_index> n_in_nodes = n_in_ei->second;

		DEBUG ("\nIn edge of node %d has label %d", n.get_node_id (), l);
		
		// Iterate over all in nodes (with label L) of N2
		set<node_index>::iterator n_in_ni;
		for (n_in_ni = n_in_nodes.begin (); n_in_ni != n_in_nodes.end (); n_in_ni++)
		{
			DEBUG ("\nIn node of node %d is %d", n.get_node_id (), *n_in_ni);
			non_deterministic_simple_node * n_in_node;
			n_in_node = nodes[*n_in_ni];
			DEBUG ("\nDeleting edge %d -> %d -> %d", *n_in_ni, l, n.get_node_id ());
			n_in_node->delete_edge (l, n);
			DEBUG ("\nInserting in edges of %d i.e. %d -> %d -> %d", 
				n.get_node_id (), *n_in_ni, l, node_id);
			n_in_node->insert_edge (l, *this, stack_id);
		}

		// Delete N2.IN_EDGE_LIST[L] if its value set is empty
		if (!n_in_ei->second.size ())
			n.delete_in_edges (l);
	}
	stop_timer (start, transfer_in_edges_stats);
}


/**
 * Transfer OUT_EDGE_LIST of N to THIS: Transfer out nodes of N one by
 * one. 
 *
 * @returns the set of nodes which have been transferred. These nodes need to
 * be merged with their new siblings.
 */

set<node_index> non_deterministic_simple_node::
transfer_out_edges (non_deterministic_simple_node & n, map<node_index, non_deterministic_simple_node *> & nodes, node_index stack_id)
{
	struct timeval start;	
	start_timer (start);

	DEBUG ("\nTransfer out edges of node %d to node %d", n.get_node_id (), node_id);

	map<label, set<node_index> > n_out_edges = n.get_out_edge_list ();
	// Iterate over all out edges of N2
	map<label, set<node_index> >::iterator n_out_ei;
	for (n_out_ei = n_out_edges.begin (); n_out_ei != n_out_edges.end (); n_out_ei++)
	{
		label l = n_out_ei->first;
		set<node_index> n_out_nodes = n_out_ei->second;

		DEBUG ("\nOut edge of node %d has label %d", n.get_node_id (), l);
		
		// Iterate over all out nodes (with label L) of N2
		set<node_index>::iterator n_out_ni;
		for (n_out_ni = n_out_nodes.begin (); n_out_ni != n_out_nodes.end (); n_out_ni++)
		{
			DEBUG ("\nOut node of node %d is %d", n.get_node_id (), *n_out_ni);
			non_deterministic_simple_node * n_out_node;
			n_out_node = nodes[*n_out_ni];
			DEBUG ("\nDeleting out edges of node %d", n.get_node_id ());
			n.delete_edge (l, *n_out_node);
			DEBUG ("\nInserting n1 %d -> %d -> out edges of %d i.e. %d", 
				node_id, l, n.get_node_id (), *n_out_ni);
			insert_edge (l, *n_out_node, stack_id);

			// I am not sure if we should interleave transfers with
			// merging. For example, if out-edges of N1 are
			// (N1,13,N3) and (N1,15,N3), then we will create
			// (N2,13,N3) and before creating (N2,15,N3), we will
			// attempt for merging of N3.
			// merge_with_sibling_nodes (*n_out_node);
		}

		// Delete N2.OUT_EDGE_LIST[L] if its value set is empty
		if (!n_out_ei->second.size ())
			n.delete_out_edges (l);
	}

	set<node_index> affected_nodes;
	// Once all the out edges of N2 are transferred to out of N1, merge out
	// nodes of N2. However, we cannot perform merging of out nodes of N2
	// with siblings right now. This is because till now in-edges of N2
	// have not been deleted; And if N2 is encountered again for merging
	// with siblings, then it leads to wrong solutions. Note
	// $hra-source/misc/test-cases.cpp/test33 () and
	// $hra-test/test-cases/test45.c---third iteration,OUT(7).

	for (n_out_ei = n_out_edges.begin (); n_out_ei != n_out_edges.end (); n_out_ei++)
	{
		set<node_index> n_out_nodes = n_out_ei->second;
		affected_nodes.insert (n_out_nodes.begin (), n_out_nodes.end ());
	}

	stop_timer (start, transfer_out_edges_stats);
	return affected_nodes;
}

/**
 * This function copies the in and out edges of the parameter node to THIS
 * node. The insertion of edges increases the out degree of a node, i.e the
 * addition of the edge is not done keeping the graph deterministic. 
 */

void non_deterministic_simple_node::
copy_node_edges (non_deterministic_simple_node & n, map<node_index, node_index> copy_nodes_map)
{
	map<label, set<node_index> >::iterator in_edges;
	map<label, set<node_index> > n_in_edges = n.in_edge_list;
	for (in_edges = n_in_edges.begin (); in_edges != n_in_edges.end (); in_edges++)
	{
		label l = in_edges->first;
		DEBUG ("\nCopying in edges of node %d to node %d, label %d", 
			n.node_id, node_id, l);
		set<node_index> s = in_edges->second;
		set<node_index> copy_s;
		set<node_index>::iterator si;
		for (si = s.begin (); si != s.end (); si++)
			copy_s.insert (copy_nodes_map[*si]);
	
		in_edge_list[l].insert (copy_s.begin (), copy_s.end ());
	}

	map<label, set<node_index> >::iterator out_edges;
	map<label, set<node_index> > n_out_edges = n.out_edge_list;
	for (out_edges = n_out_edges.begin (); out_edges != n_out_edges.end (); out_edges++)
	{
		label l = out_edges->first;
		DEBUG ("\nCopying out edges of node %d to node %d, label %d", 
			n.node_id, node_id, l);
		set<node_index> s = out_edges->second;
		set<node_index> copy_s;
		set<node_index>::iterator si;
		for (si = s.begin (); si != s.end (); si++)
			copy_s.insert (copy_nodes_map[*si]);
	
		out_edge_list[l].insert (copy_s.begin (), copy_s.end ()); 
	}

#if DEBUG_CONTAINER
	DEBUG ("\nSource node %d", n.node_id);
	map<node_index, non_deterministic_simple_node *> nodes;
	n.print_node (NULL, nodes);
	DEBUG ("\nDestination node %d", node_id);
	print_node (NULL, nodes);
#endif
}

/**
 * This function checks if nodes N1 and N2 accept the same language. This
 * function is called when nodes N1 and N2 belong to the same graph containing
 * NODES. The algorithm is as follows: It computes DFA states from the NFA
 * graph. N1 and N2 are not equivalent if there exists a DFA state which
 * contains only one of N1 and N2; otherwise they are equivalent.
 */

bool non_deterministic_simple_node::
is_in_language_comparison_okay (node_index root, 
	state_index dfa_state, 
	node_index n1, 
	node_index n2,
	map<node_index, non_deterministic_simple_node *> & nodes,
	set<state_index> & visited_dfa_states)
{
	DEBUG ("\nis_in_language_comparison_okay () -- same graph");

	if (visited_dfa_states.find (dfa_state) != visited_dfa_states.end ())
		return true;

	visited_dfa_states.insert (dfa_state);

	// Return false if only one of N1 and N2 is present in DFA_STATE
	if (dfa_state.find (n1) != dfa_state.end () && 
		dfa_state.find (n2) == dfa_state.end ())
	{
		DEBUG ("\nn1 %d is present, but n2 %d is not", n1, n2);
		return false;
	}
	if (dfa_state.find (n2) != dfa_state.end () && 
		dfa_state.find (n1) == dfa_state.end ())
	{
		DEBUG ("\nn2 %d is present, but n1 %d is not", n2, n1);
		return false;
	}

	// Prepare successor DFA states of DFA_STATE
	map<label, state_index> dfa_state_out_edges;
	get_out_dfa_edges (root, dfa_state, dfa_state_out_edges, nodes);

	// Recursively compute successor DFA states for the states in
	// DFA_STATE_OUT_EDGES.
	map<label, state_index>::iterator ei;
	for (ei = dfa_state_out_edges.begin (); ei != dfa_state_out_edges.end (); ei++)
		if (!is_in_language_comparison_okay (root, ei->second, n1, n2, nodes, visited_dfa_states))
			return false;

	return true;
}

bool non_deterministic_simple_node::
is_node_comparison_okay (non_deterministic_simple_node & n, 
	map<node_index, non_deterministic_simple_node *> this_nodes, 
	map<node_index, non_deterministic_simple_node *> n_nodes, 
	map<node_index, node_index> equiv_node_pairs)
{
	non_deterministic_simple_node * n1 = this;
	non_deterministic_simple_node * n2 = &n;

	set<node_index> nodes_reaching_n1;
	set<node_index> nodes_reaching_n2;
	n1->get_reaching_nodes (this_nodes, nodes_reaching_n1);
	n2->get_reaching_nodes (n_nodes, nodes_reaching_n2);
#if DEBUG_CONTAINER
	set<node_index>::iterator nri;
	DEBUG ("\nNodes reaching n1=%d: ", n1->get_node_id ());
	for (nri = nodes_reaching_n1.begin (); nri != nodes_reaching_n1.end (); nri++)
		DEBUG ("%d,", *nri);
	DEBUG ("\nNodes reaching n2=%d: ", n2->get_node_id ());
	for (nri = nodes_reaching_n2.begin (); nri != nodes_reaching_n2.end (); nri++)
		DEBUG ("%d,", *nri);
	map<node_index, node_index>::iterator vpi;
	DEBUG ("\nEquivalent node pairs: ");
	for (vpi = equiv_node_pairs.begin (); vpi != equiv_node_pairs.end (); vpi++)
		DEBUG ("(%d,%d),", vpi->first, vpi->second);
#endif

	// The following is not an error: it is not necessary that the sizes
	// are the same. For example, (1,f,2), (1,g,3), (1,g,4), (2,h,3),
	// (2,h,4), (3,i,2). Nodes 3 and 4 have in-isomorphic graphs. However,
	// the nodes reaching 3 are {1,2,3} and nodes reaching 4 are {1,2,3,4}. 
	if (nodes_reaching_n1.size () != nodes_reaching_n2.size ())
		DEBUG ("\nNodes %d and %d have %d and %d number of reaching nodes",
			n1->get_node_id (), n2->get_node_id (), 
			nodes_reaching_n1.size (), nodes_reaching_n2.size ());

	// Check that the in- and out-edges of every node reaching N1 map to
	// the in- and out-edges of the matching node. For the above reason,
	// nodes reaching N1 and N2 may be different, this function is called
	// twice---once for (N1,N2) and then for (N2,N1).
	set<node_index>::iterator ni;
	for (ni = nodes_reaching_n1.begin (); ni != nodes_reaching_n1.end (); ni++)
	{
		node_index in_n1_id = *ni;
		if (equiv_node_pairs.find (in_n1_id) == equiv_node_pairs.end ())
		{
			DEBUG ("\nCannot find equiv_node_pair(%d)", in_n1_id);
			// This may not be an error. For example, (n4,f,n3),
			// (n3,f,n1), (n3,f,n2), is_in_graph_isomorphic() will
			// check only n3 for n1 and n2; it will not visit n4,
			// even though n4 reaches n1 and n2.
			continue;
		}
		node_index in_n2_id = equiv_node_pairs[in_n1_id];
		if (in_n1_id == in_n2_id)
			continue;
		// It could be possible that for the edges = (n0,f,n1),
		// (n0,f,n2), we have in_n1=n0, equiv_node_pairs(n0)=n0',still n0'
		// is not reachable to n2.
		if (nodes_reaching_n2.find (in_n2_id) == nodes_reaching_n2.end () &&
			nodes_reaching_n2.find (in_n1_id) == nodes_reaching_n2.end ())
		{
			RESULT ("\nError: Neither %d nor equiv_node_pair(%d)=%d reach n2=%d", 
				in_n1_id, in_n1_id, in_n2_id, n2->get_node_id ());
			return false;
		}
		
		non_deterministic_simple_node * in_n1 = this_nodes[in_n1_id];
		non_deterministic_simple_node * in_n2 = n_nodes[in_n2_id];
		map<label, set<node_index> > in_n1_in_edges = in_n1->get_in_edge_list ();
		map<label, set<node_index> > in_n2_in_edges = in_n2->get_in_edge_list ();
		if (!in_n1->is_edge_comparison_okay (in_n2_id, equiv_node_pairs, in_n1_in_edges, in_n2_in_edges))
			return false;
		DEBUG ("\nIn-edges of %d and %d are same", in_n1_id, in_n2_id);
	}

	RESULT ("\nNode merging of %d and %d is okay \\m/", 
		n1->get_node_id (), n2->get_node_id ());
	return true;
}


/**
 * This function is called after two graphs are compared and matched.
 * EQUIV_NODE_PAIRS contains the mapping of the nodes of the two graphs,
 * respectively. This function checks if the in- and out-edges of the mapped
 * nodes match.
 */

bool non_deterministic_simple_node::
is_edge_comparison_okay (node_index matching_node_id, map<node_index, node_index> & equiv_node_pairs, map<label, set<node_index> > this_edges, map<label, set<node_index> > g_edges)
{
	if (this_edges.size () != g_edges.size ())
	{
		RESULT ("\nError: Number of edges of node %d = %d, edges of matching node %d = %d",
			node_id, this_edges.size (), matching_node_id, g_edges.size ());
		return false;
	}
	map<label, set<node_index> >::iterator this_ei;
	map<label, set<node_index> >::iterator g_ei;
	DEBUG ("\nthis_edges size = %d, g_edges size = %d", this_edges.size (), g_edges.size ());
	for (this_ei = this_edges.begin (), g_ei = g_edges.begin (); 
		this_ei != this_edges.end (); 
		this_ei++, g_ei++)
	{
		label this_l = this_ei->first;
		label g_l = g_ei->first;
		if (this_l != g_l)
		{
			RESULT ("\nError: Node %d has label %d, Matching node %d has label %d",
				node_id, this_l, matching_node_id, g_l);
			return false;
		}		
		set<node_index> this_edge_n = this_ei->second;
		set<node_index> g_edge_n = g_ei->second;
		if (this_edge_n.size () != g_edge_n.size ())
		{
			RESULT ("\nError: Number of edge nodes of node %d = %d, edge nodes of matching node %d = %d",
				node_id, this_edge_n.size (), matching_node_id, g_edge_n.size ());
			return false;
		}
		set<node_index>::iterator this_edge_ni;
		for (this_edge_ni = this_edge_n.begin (); this_edge_ni != this_edge_n.end (); this_edge_ni++)
		{
			if (equiv_node_pairs.find (*this_edge_ni) == equiv_node_pairs.end ())
			{
				RESULT ("\nError: Cannot find equiv_node_pair(%d)", *this_edge_ni);
				return false; 
			}
			node_index matched_edge_n = equiv_node_pairs[*this_edge_ni];
			if (g_edge_n.find (matched_edge_n) == g_edge_n.end ())
			{
				RESULT ("\nError: Node %d with edge (%d,%d) does not match the edges of matching node %d", 
					node_id, this_l, *this_edge_ni, matched_edge_n);
				return false;
			}
			DEBUG ("\n  Node %d with edge (%d,%d) matches with matching node %d edge (%d,%d)", 
				node_id, this_l, *this_edge_ni, matching_node_id, this_l, matched_edge_n);
		}
	}

	return true;
}
 
int non_deterministic_simple_node::
count_in_edges ()
{
	int no_of_in_edges = 0;
	map<label, set<node_index> >::iterator in_edge_i;
	for (in_edge_i = in_edge_list.begin(); in_edge_i != in_edge_list.end(); in_edge_i++)
	{
		no_of_in_edges += in_edge_i->second.size ();
	}
	return no_of_in_edges;
}

int non_deterministic_simple_node::
count_out_edges ()
{
	int no_of_out_edges = 0;
	map<label, set<node_index> >::iterator out_edge_i;
	for (out_edge_i = out_edge_list.begin(); out_edge_i != out_edge_list.end(); out_edge_i++)
	{
		no_of_out_edges += out_edge_i->second.size ();
	}
	return no_of_out_edges;
}

/**
 * This function makes the out-edges of THIS node deterministic. It does not
 * make the entire subgraph deterministic.
 */

void non_deterministic_simple_node::
make_edge_deterministic (map<node_index, non_deterministic_simple_node *> & nodes, node_index stack_id)
{
	map<label, set<node_index> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		set<node_index> out_nodes = ei->second;
		set<node_index>::iterator ni = out_nodes.begin ();
		node_index n1_id = *ni;
		non_deterministic_simple_node * n1 = nodes[n1_id];
		for (; ni != out_nodes.end (); ni++)
		{
			node_index n2_id = *ni;
			if (n1_id == n2_id)
				continue;
			non_deterministic_simple_node * n2 = nodes[n2_id];
			n1->transfer_out_edges (*n2, nodes, stack_id);
			n1->transfer_in_edges (*n2, nodes, stack_id);
		} 
	}
}

void non_deterministic_simple_node::
print_node (const char * file, map<node_index, non_deterministic_simple_node *> & nodes)
{
	DEBUG ("\nnon_deterministic_simple_node::print_node (), node %d", node_id);

	map<label, set<node_index> >::iterator out_edge_i;
	for (out_edge_i = out_edge_list.begin(); out_edge_i != out_edge_list.end(); out_edge_i++)
	{
		label l = out_edge_i->first;	
		DEBUG ("\nout-edge l=%d", l);

		set<node_index>::iterator si;
		for (si = out_edge_i->second.begin (); si != out_edge_i->second.end (); si++)
		{
			DEBUG ("\nout-node %d", *si);
			RESULT ("\n");

			non_deterministic_simple_node * dest_node = NULL;
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
				RESULT ("%d(%x) -> %s (%d) -> %d(%x) \t#%d(in) \t#%d(out)", 
					node_id, this, variable->name, l, *si, dest_node, no_of_in_edges, no_of_out_edges);
			else
				RESULT ("%d(%x) -> %d -> %d(%x) \t#%d(in) \t#%d(out)", 
					node_id, this, l, *si, dest_node, no_of_in_edges, no_of_out_edges);
#endif

			if (l != stack_deref && variable)
				RESULT ("%d -> %s (%d) -> %d \t#%d(in) \t#%d(out)", 
					node_id, variable->name, l, *si, no_of_in_edges, no_of_out_edges);
			else
				RESULT ("%d -> %d -> %d #%d", 
					node_id, l, *si, no_of_in_edges);
		}
	}
}


void non_deterministic_simple_node::
print_node_reverse (const char * file)
{
//#if 0
	DEBUG ("\nnon_deterministic_simple_node::print_node_reverse () %d", node_id);
	map<label, set<node_index> >::iterator in_edge_i;
	for (in_edge_i = in_edge_list.begin(); in_edge_i != in_edge_list.end(); in_edge_i++)
	{
		label l = in_edge_i->first;	

		if (in_edge_i->second.begin () == in_edge_i->second.end ())
		{
			RESULT ("\nError: Node %d has in edge with label %d, but without any source node", 
				node_id, l);
			RESULT ("--size=%d", in_edge_i->second.size ());
		}

		set<node_index>::iterator si;
		for (si = in_edge_i->second.begin (); si != in_edge_i->second.end (); si++)
			// Do not extract name of edge label since it may be a member field.
			RESULT ("\n%d <- %d <- %d", node_id, l, *si);
	}
//#endif
}


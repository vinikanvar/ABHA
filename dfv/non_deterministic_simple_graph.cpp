
/************************
 * @author Vini Kanvar
************************/

#include "non_deterministic_simple_graph.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

non_deterministic_simple_graph::
non_deterministic_simple_graph ()
{
	stack = new non_deterministic_simple_node;
	nodes[stack->get_node_id ()] = stack;
	DEBUG ("\nInserted stack node = %d", stack->get_node_id ());
	reference_count = 0;
}

non_deterministic_simple_graph::
~non_deterministic_simple_graph ()
{
	DEBUG ("\nDeleting non deterministic graph with stack node %d(%x)", stack->get_node_id (), stack);
	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
		delete ni->second;
}

void non_deterministic_simple_graph::
increment_reference_count ()
{
	reference_count++;
	DEBUG ("\nCount = %d (after incr) of graph with stack node %d", 
		reference_count, stack->get_node_id ());
}

void non_deterministic_simple_graph::
decrement_reference_count ()
{
	if (!reference_count)
	{
		RESULT ("\nError: reference count of graph with stack node %d was already 0",
			stack->get_node_id ());	
		return;
	}
	
	reference_count--;
	DEBUG ("\nCount = %d (after decr) of graph with stack node %d", 
		reference_count, stack->get_node_id ());
	if (!reference_count)
	{
#if GC
		DEBUG ("\nGC non_deterministic_simple_graph");
		delete this;
#endif
	}
}

bool non_deterministic_simple_graph::
is_element (label v)
{
	map<label, set<node_index> > out_edges = stack->get_out_edge_list ();
	return out_edges.find (v) != out_edges.end ();
}

set<node_index> non_deterministic_simple_graph::
get_arg_glob_connected_nodes (set<unsigned int> arg_glob_vars)
{
	struct timeval start;
	start_timer(start);
	DEBUG ("\nget_arg_glob_connected_nodes()");
	set<node_index> arg_glob_connected_nodes;

	// Nodes reachable via function arguments are ARG_GLOB_CONNECTED_NODES
	// Nodes connected to ARG_GLOB_CONNECTED_NODES are also ARG_GLOB_CONNECTED_NODES
	map<label, set<node_index> > stack_out_edges = stack->get_out_edge_list ();
	set<unsigned int>::iterator vi;
	for (vi = arg_glob_vars.begin (); vi != arg_glob_vars.end (); vi++)
	{
		DEBUG ("\nConsider variable %d", *vi);

		if (stack_out_edges.find (*vi) == stack_out_edges.end ())
			continue;

		set<node_index> conn_n = stack_out_edges[*vi];
		set<node_index>::iterator ni;
		for (ni = conn_n.begin (); ni != conn_n.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes[*ni];
			// We do not find nodes connected to null/readonly/undef nodes
			// because these nodes do not indicate alias relationship.
			n->mark_connected_nodes (stack->get_node_id (), nodes, arg_glob_connected_nodes);
		}
	}

	arg_glob_connected_nodes.erase (stack->get_node_id ());
	stop_timer (start, get_arg_glob_connected_nodes_stats);
	return arg_glob_connected_nodes;
}

non_deterministic_simple_graph * non_deterministic_simple_graph::
extract_arg_glob_connected_graph (set<node_index> arg_glob_connected_nodes)
{
	struct timeval start;
	start_timer(start);

	DEBUG ("\nextract_arg_glob_connected_graph");

	non_deterministic_simple_graph * arg_glob_connected_graph = new non_deterministic_simple_graph;

	// Copy all ARG_GLOB_CONNECTED_NODES to NODES map of ARG_GLOB_CONNECTED_GRAPH
	set<node_index> improper_nodes;
	set<node_index>::iterator cn;
	for (cn = arg_glob_connected_nodes.begin (); cn != arg_glob_connected_nodes.end (); )
	{
		DEBUG ("\nAdding node %d to map of new graph", *cn);

		// If node is not a proper node, then save the node in
		// IMPROPER_NODES and remove it from ARG_GLOB_CONNECTED_NODES.
		non_deterministic_simple_node * n = nodes[*cn];
		label name = n->get_node_name (stack->get_node_id ());
		if (!program.is_proper_var (name))
		{
			improper_nodes.insert (*cn);
			arg_glob_connected_nodes.erase (cn++);
			continue;
		}

		// If node is a proper node, then transfer it to ARG_GLOB_CONNECTED_GRAPH.
		arg_glob_connected_graph->nodes[*cn] = nodes[*cn];
		nodes.erase (*cn);
		cn++;
	}

	// Copy OUT_EDGE_LIST of THIS->STACK to ARG_GLOB_CONNTECTED_GRAPH->STACK,
	// except for the edges which point to nodes not in ARG_GLOB_CONNECTED_NODES.
	// Here ARG_GLOB_CONNECTED_NODES does not contain any improper node.
	arg_glob_connected_graph->transfer_connected_edges (stack, arg_glob_connected_graph->stack, arg_glob_connected_nodes);

	// Copy from improper nodes the IN_EDGE_LIST that is connected to
	// ARG_GLOB_CONNECTED_NODDES. We assume that improper nodes do not have
	// an out edge.
	set<node_index>::iterator ni;
	for (ni = improper_nodes.begin (); ni != improper_nodes.end (); ni++)
	{
		non_deterministic_simple_node * improper_node = nodes[*ni];
		set<node_index> arg_glob_improper_nodes;
		arg_glob_connected_graph->generate_addressof_nodes (name, arg_glob_improper_nodes);
		node_index arg_glob_improper_nid = *(arg_glob_improper_nodes.begin ());
		non_deterministic_simple_node * arg_glob_improper_node = arg_glob_connected_graph->nodes[arg_glob_improper_nid];
		arg_glob_connected_graph->transfer_connected_edges (improper_node, arg_glob_improper_node, arg_glob_connected_nodes);		
	}

	stop_timer (start, extract_arg_glob_connected_graph_stats);
	return arg_glob_connected_graph;
}

/**
 * This function transfers to DEST_NODE the in and out edges of SRC_NODE that
 * are connected to CONNECTED_NODES. It is assumed that DEST_NODE and
 * CONNECTED_NODES are in THIS graph. We also assume there is no improper node
 * in CONNECTED_NODES.
 */

void non_deterministic_simple_graph::
transfer_connected_edges (non_deterministic_simple_node * src_node, non_deterministic_simple_node * dest_node, set<node_index> & connected_nodes)
{
	node_index stack_id = stack->get_node_id ();

	// Below, do not merge transferred N with its indistinguishable sibling
	// nodes inside the loops below i.e. before the loop completes i.e.
	// before all the edges of N are not transferred from SRC_NODE to
	// DEST_NODE. 

	map<label, set<node_index> > src_node_out_edges = src_node->get_out_edge_list ();
	map<label, set<node_index> >::iterator ei;
	for (ei = src_node_out_edges.begin (); ei != src_node_out_edges.end (); ei++)
	{
		label l = ei->first;
		set<node_index> out_n = ei->second;
		set<node_index>::iterator ni;
		for (ni = out_n.begin (); ni != out_n.end (); ni++)
			if (connected_nodes.find (*ni) != connected_nodes.end ())
			{
				DEBUG ("\nInserting edge to dest_node %d -> %d -> %d", 
					dest_node->get_node_id (), l, *ni);
				non_deterministic_simple_node * n = nodes[*ni];
				src_node->delete_edge (l, *n);
				dest_node->insert_edge (l, *n, stack_id);
			}
	}
	map<label, set<node_index> > src_node_in_edges = src_node->get_in_edge_list ();
	for (ei = src_node_in_edges.begin (); ei != src_node_in_edges.end (); ei++)
	{
		label l = ei->first;
		set<node_index> in_n = ei->second;
		set<node_index>::iterator ni;
		for (ni = in_n.begin (); ni != in_n.end (); ni++)
			if (connected_nodes.find (*ni) != connected_nodes.end ())
			{
				DEBUG ("\nInserting edge to dest_node %d -> %d -> %d", 
					*ni, l, dest_node->get_node_id ());
				non_deterministic_simple_node * n = nodes[*ni];
				n->delete_edge (l, *src_node);
				n->insert_edge (l, *dest_node, stack_id);
			}
	}
}

/**
 * Cleans unreachable nodes.
 *
 * @returns nodes whose in-edges have been deleted. These have become
 * candidates for merging with their indistinguishable siblings.
 */

set<node_index> non_deterministic_simple_graph::
clean_unreachable_nodes ()
{
	struct timeval start;
	start_timer (start);
	DEBUG ("\nclean_unreachable_nodes ()");

	set<node_index> reachable_nodes;
	{
		struct timeval start;
		start_timer (start);
		stack->get_reachable_nodes (stack->get_node_id (), nodes, reachable_nodes);
		stop_timer (start, get_reachable_nodes_stats);
	}

#if DEBUG_CONTAINER
	DEBUG ("\nReachable nodes=");
	set<node_index>::iterator rni;
	for (rni = reachable_nodes.begin (); rni != reachable_nodes.end (); rni++)
		DEBUG ("%d,", *rni);
#endif

	set<node_index> affected_nodes;
	set<node_index> unreachable_nodes;
	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		DEBUG ("\nIn loop");
		DEBUG ("\nNext node %d", ni->first);
		node_index n_index = ni->first;
		non_deterministic_simple_node * n = ni->second;

		// If N_INDEX is reachable and the node is not useless
		if (reachable_nodes.find (n_index) != reachable_nodes.end ())
		{
			DEBUG ("\nNode %d is reachable", n_index);
			continue;
		}

		DEBUG ("\nNode %d is unreachable", n_index);
		// We should not call nodes.erase(ni++); here. It causes
		// segmentation fault in test4i.c at delete_in_edges(*n)
		// (below) because in-node has already been erased. Note that
		// this was not giving fault in our earlier versions since now
		// we have slightly modified delete_local_variables().
		unreachable_nodes.insert (n_index);

		// Delete IN_EDGE_LIST of node N
		// If we were simulataneously erasing the unreachable nodes,
		// then for N, the in-node might have already been erased from
		// NODES. Therefore, we choose to erase unreachable nodes in
		// the end only.
		DEBUG ("\nDeleting in-edges of %d", n_index);
		delete_in_edges (*n);
	
		// Delete OUT_EDGE_LIST of node N 
		map<label, set<node_index> > out_edges = n->get_out_edge_list ();
		map<label, set<node_index> >::iterator out_edge_i;
		for (out_edge_i = out_edges.begin (); out_edge_i != out_edges.end (); out_edge_i++)
		{
			DEBUG ("\nDeleting out-edges of %d", n_index);
			label l = out_edge_i->first;
			set<node_index> out_nodes = out_edge_i->second;
			set<node_index>::iterator out_node_i;
			for (out_node_i = out_nodes.begin (); out_node_i != out_nodes.end (); out_node_i++)
			{
				node_index out_node_id = *out_node_i;
				if (reachable_nodes.find (*out_node_i) == reachable_nodes.end ())
				{
					DEBUG ("\nNo need to update IN_EDGE_LIST of unreachable node %d",
						*out_node_i);
					continue;
				}
		
				DEBUG ( "\nDelete edge %d -> %d -> %d", n_index, l, *out_node_i);
				// NODES map should be used only on reachable
				// nodes, since other nodes may have been
				// deleted from the map.
				non_deterministic_simple_node * out_node = nodes[*out_node_i];
				n->delete_edge (l, *out_node);
				// If out-node is unreachable, then we mark it as affected.
				affected_nodes.insert (*out_node_i);
			}
		}
	}	

	set<node_index>::iterator uri;
	for (uri = unreachable_nodes.begin (); uri != unreachable_nodes.end (); uri++)
	{
		non_deterministic_simple_node * n = nodes[*uri];
		nodes.erase (*uri);
#if GC
		DEBUG ("\nGC non_deterministic_simple_node %d", *uri);
		delete n;
#endif
	}

	stop_timer (start, clean_unreachable_nodes_stats);
	DEBUG ("\nOut of loop");
	return affected_nodes;
}

/**
 * This function deletes the nodes which have IS_NODE_USELESS as true.
 */

void non_deterministic_simple_graph::
clean_useless_nodes ()
{
	struct timeval start;
	start_timer(start);
	node_index stack_id = stack->get_node_id ();
	
	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); )
	{
		node_index nid = ni->first;
		non_deterministic_simple_node * n = ni->second;
		if (!n->is_node_useless (stack_id))
		{
			ni++;
			continue;
		}

		delete_in_edges (*n);
#if CHECK_CONTAINER
		if (n->get_out_edge_list ().size ())
			RESULT ("\nError: Useless node %d should have zero out-edges", nid);
#endif
		nodes.erase (ni++);
#if GC
		DEBUG ("\nGC non_deterministic_simple_node %d", nid);
		delete n;
#endif
	}

	stop_timer (start, clean_useless_nodes_stats);
}

/**
 * This function deletes the nodes which have no in-edges i.e. they are
 * disconnected from the graph. This function has been called from CLEAN (),
 * and it has been called after deleting unreachable nodes and merging
 * indistinguishable nodes; therefore, the disconnected nodes have no out-edges
 * also.
 */

void non_deterministic_simple_graph::
clean_disconnected_nodes ()
{
	struct timeval start;
	start_timer(start);

	DEBUG ("\nclean_disconnected_nodes ()");

	node_index stack_id = stack->get_node_id ();

	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); )
	{
		node_index nid = ni->first;
		non_deterministic_simple_node * n = ni->second;
		map<label, set<node_index> > in_edges = n->get_in_edge_list ();
		if (nid == stack_id || in_edges.size ())
		{
			ni++;
			continue;
		}

#if CHECK_CONTAINER
		if (n->get_out_edge_list ().size ())
			RESULT ("\nError: We had expected out-edges of node %d to be empty", 
				n->get_node_id ());
#endif

		nodes.erase (ni++);
#if GC
		DEBUG ("\nGC non_deterministic_simple_node %d", n->get_node_id ());
		delete n;
#endif
	}
	stop_timer (start, clean_disconnected_nodes_stats);
}

/**
 * If UNIVERSAL is a pointee of a node, then all other pointees of the node
 * should be deleted. This is because UNIVERSAL subsumes all pointees.
 */

void non_deterministic_simple_graph::
subsume_in_universal ()
{
	// Get UNIVERSAL node
	set<node_index> universal_node_ids;
	get_addressof_nodes (universal_id, universal_node_ids);
	if (!universal_node_ids.size ())
		return;
	node_index universal_node_id = *(universal_node_ids.begin ());
	non_deterministic_simple_node * universal_node = nodes[universal_node_id];

	node_index stack_id = stack->get_node_id ();

	// Get nodes that point to the UNIVERSAL node
	set<node_index> pointers_to_universal;
	map<label, set<node_index> > in_edges = universal_node->get_in_edge_list ();
	map<label, set<node_index> >::iterator ei;
	for (ei = in_edges.begin (); ei != in_edges.end (); ei++)
	{
		label l = ei->first;
		set<node_index> in_nodes = ei->second;
		in_nodes.erase (stack_id);

		set<node_index>::iterator ni;
		for (ni = in_nodes.begin (); ni != in_nodes.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes[*ni];
			set<node_index> out_nodes;
			n->get_destination_nodes (l, stack_id, out_nodes);

			// Delete all pointees (except UNIVERSAL) of N
			out_nodes.erase (universal_node_id);
			set<node_index>::iterator pi;
			for (pi = out_nodes.begin (); pi != out_nodes.end (); pi++)
			{
				non_deterministic_simple_node * pointee = nodes[*pi];
				n->delete_edge (l, *pointee);
			}
		}
	}
}

/**
 * UNIVERSAL represents all variables. Therefore, if POINTEES contains an
 * UNIVERSAL node, then retain only the UNIVERSAL node.
 */

void non_deterministic_simple_graph::
subsume_in_universal_pointees (set<node_index> & pointees)
{
	// Get UNIVERSAL node
	set<node_index> universal_nodes;
	get_addressof_nodes (universal_id, universal_nodes);
	if (!universal_nodes.size ())
		return;
	node_index universal_node = *(universal_nodes.begin ());

	if (pointees.find (universal_node) != pointees.end ())
	{
		pointees.clear ();
		pointees.insert (universal_node);
	}
}

/**
 * Removes from POINTERS those nodes whose pointee (via l) is UNIVERSAL.
 */

void non_deterministic_simple_graph::
remove_pointers_with_universal_pointees (set<node_index> & pointers, label l)
{
	// Get UNIVERSAL node
	set<node_index> universal_node_ids;
	get_addressof_nodes (universal_id, universal_node_ids);
	if (!universal_node_ids.size ())
		return;
	node_index universal_node_id = *(universal_node_ids.begin ());

	set<node_index>::iterator ni;
	for (ni = pointers.begin (); ni != pointers.end (); )
	{
		non_deterministic_simple_node * pointer = nodes[*ni];
		map<label, set<node_index> > out_edges = pointer->get_out_edge_list ();
		set<node_index> pointees = out_edges[l];
		if (pointees.find (universal_node_id) != pointees.end ())
			pointers.erase (ni++);
		else
			ni++;
	}
}

/**
 * Deletes unreachable nodes, nameless nodes, and useless nodes.
 */

void non_deterministic_simple_graph::
clean ()
{
	struct timeval start;
	start_timer (start);

	DEBUG ("\nclean ()");

#if DEBUG_CONTAINER
	DEBUG ("\nGraph before clean ()");
	print_value (NULL);

	map<node_index, non_deterministic_simple_node *>::iterator nodesi;
	DEBUG ("\nNodes: ");
	for (nodesi = nodes.begin (); nodesi != nodes.end (); nodesi++)
	{
		non_deterministic_simple_node * n = nodesi->second;
		DEBUG ("%d,", n->get_node_id ());
	}
#endif

//#if CHECK_CONTAINER
	are_improper_nodes_okay ();
//#endif

	// Deletion of nodes, causes the deletion of their out-edges, which act
	// as the in-edges of some nodes. The nodes whose in-edges are deleted
	// are called AFFECTED_NODES.
	set<node_index> affected_nodes;
	affected_nodes = clean_unreachable_nodes ();
	
	// We delete nodes which have IS_NODE_USELESS as true: nodes which have
	// one in-edge and no out-edge. Note that we identify nodes as useless
	// only after cleaning the unreachable nodes because some nodes become
	// useless after some unreachable nodes are deleted. Since these nodes
	// do not have any out-edges, these do not affect the in-edges of any
	// nodes.
	clean_useless_nodes ();

	// We perform merging of the affected nodes after cleaning up so that
	// the same node need not go through merging again and again.
	set<node_index>::iterator ani;
	for (ani = affected_nodes.begin (); ani != affected_nodes.end (); ani++)
	{
		DEBUG ("\nNext affected node %d", *ani);
		// An affected node may have been deleted if IS_NODE_USELESS
		// was true for that node.  Proceed only if it is present in
		// the NODES map.
		if (nodes.find (*ani) != nodes.end ())
		{
			non_deterministic_simple_node * node = nodes[*ani];
			// In CLEAN() we do not change merging criterion
			// whether or not it is a loop merge. Therefore, FALSE.
			merge_with_sibling_nodes (*node, false);
		}
	}

	DEBUG ("\nMerged siblings after cleanup");

	// If N1 and N2 are merged, all the in- and out-edges of N2 are
	// transferred to N1, and N2 is disconnected from the graph. We now
	// need to delete such nodes too.
	clean_disconnected_nodes ();

	stop_timer (start, clean_stats);
}

void non_deterministic_simple_graph::
delete_local_variables (set<label> & local_variables)
{
	struct timeval start;
	start_timer (start);

	DEBUG ("\ndelete_local_variables()");

	map<label, set<node_index> > out_edges = stack->get_out_edge_list ();
	set<label>::iterator vi;
	for (vi = local_variables.begin (); vi != local_variables.end (); vi++)
	{
		if (out_edges.find (*vi) == out_edges.end ())
			continue;
		set<node_index> out_nodes = out_edges[*vi];
		set<node_index>::iterator ni;
		for (ni = out_nodes.begin (); ni != out_nodes.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes[*ni];
			// Delete only the edge with label *vi. Note that since
			// all temporary variables point to the same node,
			// there could be other in-edges which should not be
			// deleted.
			stack->delete_edge (*vi, *n);
			// If N has no other in-edge, then it will get deleted
			// in function CLEAN ().
		}
	}

	clean ();
#if DEBUG_CONTAINER
	DEBUG ("\nGraph after clean ()");
	print_value (NULL);
#endif

	stop_timer (start, delete_local_variables_stats);
}

/**
 * A pointer variable is dead if it is neither live nor is directly pointed by
 * a live variable. This function returns all such dead pointers in THIS graph
 * which is a subset of DEAD_VARIABLES.
 */

set<label> non_deterministic_simple_graph::
get_dead_graph_variables (set<label> & dead_variables)
{
	struct timeval start;
	start_timer (start);

	set<label> dead_graph_variables;

	map<label, set<node_index> > out_edges = stack->get_out_edge_list ();
	map<label, set<node_index> >::iterator vi;
	for (vi = out_edges.begin (); vi != out_edges.end (); vi++)
	{
		label l = vi->first;
		// If L is dead.
		if (dead_variables.find (l) == dead_variables.end ())
			continue;

		// Check that all of the pointers (IN_NODES) of L are also
		// dead.
		set<node_index> pointees = vi->second;
		set<node_index> in_nodes;
		get_in_nodes (pointees, in_nodes);
#if DEBUG_CONTAINER
		DEBUG ("\nvar %d, in-nodes.size()=%d, ", l, in_nodes.size ());
		set<node_index>::iterator si;
		for (si = in_nodes.begin (); si != in_nodes.end (); si++)
			DEBUG ("%d,", *si);
#endif
		set<label> in_nodes_names;
		get_nodes_names (in_nodes, in_nodes_names);
		set<label>::iterator ni;
		bool is_in_node_live = false;
		for (ni = in_nodes_names.begin (); ni != in_nodes_names.end (); ni++)
		{
			DEBUG ("\nChecking in-node-name %d of variable %d", *ni, l);
			// If any of the pointers (in-nodes) of L is live, then
			// do not delete L.
			if (dead_variables.find (*ni) == dead_variables.end ())
			{
				DEBUG ("\nin-node-name %d is live", *ni);
				is_in_node_live = true;
				break;
			}
		}

		if (!is_in_node_live)
		{
			// We do not delete the dead variable node but only
			// store it right now.
			// delete_out_edges (*stack, l);
			dead_graph_variables.insert (l);
			DEBUG ("\nDead graph pointer %d", l);
		}
	}

	stop_timer (start, get_dead_graph_variables_stats);
	return dead_graph_variables;
}

/**
 * This function retains in DEAD_VARIABLES only those variables whose whole
 * structure (i.e. other member fields of the structure to which it belongs)
 * are all dead.
 */

void non_deterministic_simple_graph::
get_structurally_dead_variables (set<label> & dead_variables)
{
	// Do nothing if dead_variables is empty.
	if (!dead_variables.size ())
		return;

	DEBUG ("\nRetain field nodes");
	// Iterate over all variables in the graph. If a field of the variable
	// is live, then retain all fields of the variable in the graph i.e.
	// erase them from dead_variables;
	set<label> retain_fields;
	map<label, set<node_index> > out_edges = stack->get_out_edge_list ();
	map<label, set<node_index> >::iterator ei;
	for (ei = out_edges.begin (); ei != out_edges.end (); ei++)
	{
		label v = ei->first;
		// All globals+heaps and their fields are any way not in
		// dead_variables.
		if (program.global_var (v) || program.heap_var (v))
			continue;
		// Do nothing if variable has already been considered.
		if (retain_fields.find (v) != retain_fields.end ())
			continue;
		DEBUG ("\nvar=%d", v);
		// Get fields of the local variable.
		set<label> field_ids;
		program.get_field_var_ids (v, field_ids);
		// If any field_id is live, then retain all its fields.
		set<label>::iterator fi;
		for (fi = field_ids.begin (); fi != field_ids.end (); fi++)
		{
			if (dead_variables.find (*fi) == dead_variables.end ())
			{
				DEBUG ("\n%d is live", *fi);
				retain_fields.insert (field_ids.begin (), field_ids.end ());
				break;
			}
		}
	}

	// Erase fields of retain_fields from dead_variables.
	set<label>::iterator fi;
	for (fi = retain_fields.begin (); fi != retain_fields.end (); fi++)
	{
//#if DEBUG_CONTAINTER
		if (dead_variables.find (*fi) != dead_variables.end ())
			RESULT ("\nRetain %d", *fi);
//#endif
		dead_variables.erase (*fi);
	}
}

/**
 * This function deletes variables that are neither live nor are directly
 * pointed by a live variable.  
 */

void non_deterministic_simple_graph::
delete_dead_pointers (set<label> & dead_graph_variables)
{
	struct timeval start;
	start_timer (start);

#if DEBUG_CONTAINER
	DEBUG ("\ndelete_dead_pointers()");
	DEBUG ("\nGraph without deleting dead pointers:");
	print_value (NULL);
#endif

	set<label>::iterator di;
	for (di = dead_graph_variables.begin (); di != dead_graph_variables.end (); di++)
	{
		label l = *di;
		delete_out_edges (*stack, l);
		csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, l);
		RESULT ("\nDeleted dead pointer %s(%d)", v_info->name, l);
	}

#if DEBUG_CONTAINER
	DEBUG ("\nGraph after deleting dead pointers ()");
	print_value (NULL);
#endif
	stop_timer (start, delete_dead_pointers_stats);
}

/**
 * This function creates a copy of THIS graph.
 */

non_deterministic_simple_graph * non_deterministic_simple_graph::
copy_value (bool is_loop_merge)
{
	struct timeval start;
	start_timer (start);

	non_deterministic_simple_graph * copy_g = new non_deterministic_simple_graph;

	copy_g->copy_value (*this, is_loop_merge);

	stop_timer (start, copy_value_stats);

	return copy_g;
}

/**
 * This function copies graph G to THIS graph.
 */

void non_deterministic_simple_graph::
copy_value (non_deterministic_simple_graph & g, bool is_loop_merge)
{
	DEBUG ("\nCopying graph rooted at %d to graph rooted at %d", 
		g.stack->get_node_id (), stack->get_node_id ());

	// We need to perform merging of equivalent nodes, only if THIS graph
	// already has some nodes. However, if THIS graph is empty, then we do
	// not need to merge; this is assuming that graph G already has its
	// indistinguishable sibling nodes in a merged state.  If THIS graph
	// has only the stack node: if (nodes.size () == 1)
 
	bool is_this_graph_empty = nodes.size () == 1;

	// Create new nodes in NODES, without updating their IN_EDGES and OUT_EDGES.
	map<node_index, node_index> copy_nodes_map;
	copy_nodes_map = copy_nodes (g);

	// Update the IN_EDGES and OUT_EDGES of the nodes in G graph to THIS
	// graph. We copy the edges first without merging equivalent nodes.
	// Merging simultaneously with edge addition may lead to wrong merging,
	// since while merging two nodes, or while recursively merging their
	// child nodes, all the in-edges of the nodes may not have yet been
	// copied. 

	DEBUG ("\nCopying edges from graph with stack %d onto graph with stack %d", 
		g.stack->get_node_id (), stack->get_node_id ());
	copy_edges (g, copy_nodes_map);

	// Merge indistinguishable nodes of THIS graph with the nodes created
	// by copying G onto THIS graph
	if (!is_this_graph_empty)
	{
		set<node_index> visited_nodes;

		static struct timeval start;	
		start_timer (start);
		merge_graph (g, *g.stack, copy_nodes_map, visited_nodes, is_loop_merge);
		stop_timer (start, merge_graph_stats);
	}

	// UNIVERSAL represents all variables. Therefore, if the pointee of a
	// variable is UNIVERSAL, then delete other pointees.
	subsume_in_universal ();
}

map<node_index, node_index> non_deterministic_simple_graph::
copy_nodes (non_deterministic_simple_graph & g)
{
	DEBUG ("\ncopy_nodes ()");

	map<node_index, node_index> copy_nodes_map;
	// STACK node is already created in THIS graph. Map the STACK of THIS
	// graph to the STACK of G.
	node_index g_stack_id = g.stack->get_node_id ();
	copy_nodes_map[g_stack_id] = stack->get_node_id ();
	DEBUG ("\nMapped stack %d to stack %d", g_stack_id, stack->get_node_id ());	

	// Create new nodes in NODES, without updating their IN_EDGES and OUT_EDGES.
	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = g.nodes.begin (); ni != g.nodes.end (); ni++)
	{
		node_index g_n_id = ni->first;
		non_deterministic_simple_node * g_n = ni->second;

		// If NI is the STACK node, skip it since a copy of STACK has
		// been created above before the loop.
		if (g_n_id == g_stack_id)
			continue;	

		non_deterministic_simple_node * copy_n = new non_deterministic_simple_node;
		node_index copy_n_id = copy_n->get_node_id ();
		nodes[copy_n_id] = copy_n;
		copy_nodes_map[g_n_id] = copy_n_id;
		DEBUG ("\nMapped node %d to node %d", g_n_id, copy_n_id);
	}

#if DEBUG_CONTAINER
	// Check that every node in G has a copy in THIS graph
	DEBUG ("\nNode mappings: ");
	for (ni = g.nodes.begin (); ni != g.nodes.end (); ni++)
	{
		if (copy_nodes_map.find (ni->first) == copy_nodes_map.end ())
			RESULT ("\nError: A copy of node %d in graph g has not been created", ni->first);
		DEBUG ("(%d,%d),", ni->first, copy_nodes_map[ni->first]);
	}
#endif

	return copy_nodes_map;
}

/** 
 * This function copies G (containing N) to THIS graph. The copies of nodes in
 * G are mapped to newly created nodes in THIS graph. This mapping is saved in
 * COPY_NODES_MAP.
 */

void non_deterministic_simple_graph::
copy_edges (non_deterministic_simple_graph & g, map<node_index, node_index> & copy_nodes_map)
{
	DEBUG ("\ncopy_edges ()");

	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = g.nodes.begin (); ni != g.nodes.end (); ni++)
	{
		node_index n_id = ni->first;
		non_deterministic_simple_node * n = ni->second;
		non_deterministic_simple_node * copy_n = nodes[copy_nodes_map[n_id]];
		DEBUG ("\nCopying node edges of node %d to node %d", n_id, copy_n->get_node_id ());
		copy_n->copy_node_edges (*n, copy_nodes_map);
		DEBUG ("\nDone copying node edges of node %d to node %d", n_id, copy_n->get_node_id ());
	}
}

/** 
 * This function merges equivalent nodes of THIS graph. However, it saves time
 * by looking for equivalent of only the nodes of THIS graph which have a
 * mapping to a node in G (i.e. a mapping to node N). The mapping from nodes in
 * G graph to THIS graph are saved in COPY_NODES_MAP. The mapping is updated as
 * and when equivalent nodes of THIS graph are merged.
 */

void non_deterministic_simple_graph::
merge_graph (non_deterministic_simple_graph & g, non_deterministic_simple_node & n, map<node_index, node_index> & copy_nodes_map, set<node_index> & visited_nodes, bool is_loop_merge)
{
	DEBUG ("\nmerge_graph () at node %d onto graph with stack %d", 
		n.get_node_id (), stack->get_node_id ());

	// Return if the node has already been visited
	if (visited_nodes.find (n.get_node_id ()) != visited_nodes.end ())
		return;

	visited_nodes.insert (n.get_node_id ());

	non_deterministic_simple_node * copy_n = NULL;
	if (copy_nodes_map.find (n.get_node_id ()) != copy_nodes_map.end ())
	{
		node_index copy_n_id = copy_nodes_map[n.get_node_id ()];
		if (nodes.find (copy_n_id) != nodes.end ())
			copy_n = nodes[copy_n_id];
	}
	if (!copy_n)
		return;

	// If node COPY_N and a sibling node are the same, merge the two and
	// reset the COPY_NODES_MAP of N so that copy of N is not attempted for
	// merge again.

	// FIXME: problem:
	// Note that MERGE_WITH_SIBLING_NODES calls MERGE_NODES which calls
	// TRANSFER_OUT_EDGES which calls MERGE_WITH_SIBLING_NODES. We have not
	// propagated COPY_NODES_MAP to all these functions. Therefore,
	// COPY_NODES_MAP is not updated in the recursive calls to
	// MERGE_WITH_SIBLING_NODES. Consequently, even though a node of THIS
	// graph might have got merged in one of the recursive calls to
	// MERGE_WITH_SIBLING_NODES, we might end up unnecessarily attempting
	// for merging of the node again if it is still a copy through
	// COPY_NODES_MAP.

	node_index sibling_node_id;
	if (sibling_node_id = merge_with_sibling_nodes (*copy_n, is_loop_merge))
	{
		DEBUG ("\ncopy_n %d has an equivalent sibling node %d", 
			copy_n->get_node_id (), sibling_node_id);
		// Remove any mapping of N so that the node mapped to N, i.e.
		// SIBLING_NODE is not attempted for merge again.
		copy_nodes_map.erase (n.get_node_id ());
		// Set the COPY_NODES_MAP of N to the node id of the sibling node
		// copy_nodes_map[n.get_node_id ()] = sibling_node_id;
	}
	else
		DEBUG ("\ncopy_n %d does not have any equivalent sibling node", 
			copy_n->get_node_id ());

	// Merge graph G with THIS graph at the successor nodes of N in G

	map<label, set<node_index> > n_out_edges = n.get_out_edge_list ();
	map<label, set<node_index> >::iterator out_edge_i;
	for (out_edge_i = n_out_edges.begin (); out_edge_i != n_out_edges.end (); out_edge_i++)
	{
		set<node_index> out_nodes = out_edge_i->second;
		set<node_index>::iterator out_node_i;
		for (out_node_i = out_nodes.begin (); out_node_i != out_nodes.end (); out_node_i++)
		{
			DEBUG ("\nOut node of %d is %d", n.get_node_id (), *out_node_i);
			non_deterministic_simple_node * out_node = g.nodes[*out_node_i];
			merge_graph (g, *out_node, copy_nodes_map, visited_nodes, is_loop_merge);
		}
	}
}

bool non_deterministic_simple_graph::
merge_nodes (non_deterministic_simple_node & n1, non_deterministic_simple_node & n2, bool is_loop_merge)
{
	DEBUG ("\nmerge_nodes node %d and %d", n1.get_node_id (), n2.get_node_id ());

	// Check if the IN_EDGE_LIST of N1 and N2 is the same
	map<label, set<node_index> > n1_in_edges = n1.get_in_edge_list ();
	map<label, set<node_index> > n2_in_edges = n2.get_in_edge_list ();

#if DEBUG_CONTAINER
#if 0
	map<label, set<node_index> >::iterator ei;
	DEBUG ("\nn1 %d in edges: ", n1.get_node_id ());
	for (ei = n1_in_edges.begin (); ei != n1_in_edges.end (); ei++)
	{
		label l = ei->first;
		set<node_index> n1_in_nodes = ei->second;
		set<node_index>::iterator ni;
		for (ni = n1_in_nodes.begin (); ni != n1_in_nodes.end (); ni++)
			DEBUG ("%d->%d->%d,", *ni, l, n1.get_node_id ());
	}
	DEBUG ("\nn2 %d in edges: ", n2.get_node_id ());
	for (ei = n2_in_edges.begin (); ei != n2_in_edges.end (); ei++)
	{
		label l = ei->first;
		set<node_index> n2_in_nodes = ei->second;
		set<node_index>::iterator ni;
		for (ni = n2_in_nodes.begin (); ni != n2_in_nodes.end (); ni++)
			DEBUG ("%d->%d->%d,", *ni, l, n2.get_node_id ());
	}
#endif
#endif

	// The following checkes only the in-edges.
	// if (n1_in_edges != n2_in_edges)
	// {
	//	DEBUG ("\nNodes cannot be merged");
	//	return false;
	// }
	// The following checks if the in-graphs of N1 and N2 are the same.
	// This is necessary if we have a cyclic data structure, where nodes
	// are indistinguishable when the in-graphs are same, even though
	// in-edges are different.

	// Finding a matching property --- IS_IN_GRAPH_ISOMORPHIC()
	// (automorphism in this case) or IS_IN_LANGUAGE_SAME().
	if (!stack->is_node_property_same (n1, n2, nodes, is_loop_merge))
	{
		DEBUG ("\nNodes %d %d cannot be merged", n1.get_node_id (), n2.get_node_id ());
		return false;
	}

	DEBUG ("\nNodes %d %d can be merged", n1.get_node_id (), n2.get_node_id ());

	// Transfer out edges of N2 to out of N1
#if DEBUG_CONTAINER
	DEBUG ("\nN1 %d and N2 %d before transfer", n1.get_node_id (), n2.get_node_id ());
	n1.print_node (NULL, nodes);
	n1.print_node_reverse (NULL);
	n2.print_node (NULL, nodes);
	n2.print_node_reverse (NULL);
#endif
	
	set<node_index> affected_nodes;
	affected_nodes = n1.transfer_out_edges (n2, nodes, stack->get_node_id ());

	// If nodes are improper and same, we merge them. But the in-edges need to transferred.
	if (node_property == name || is_loop_merge || stack->are_nodes_improper (n1, n2))
	{
		DEBUG ("\nnode_property == name || is_loop_merge");
		n1.transfer_in_edges (n2, nodes, stack->get_node_id ());
		// No need to delete in edges of N2 now. This is already done
		// while transferring in edges of N2 to N1.
	}
	else
	{
		DEBUG ("\nnode_property != name");
		// Note that N1 and N2 may have in-languages viz. L.f* and L.
		// IS_NODE_PROPERTY() will return true for such cases so that
		// N1 and N2 are merged. Note that in such cases (where
		// in-language is different), we do not need to call
		// transfer_in_edges() since transfer_out_edges will itself
		// handle the self-loop (which creates Kleene closure f*).
		delete_in_edges (n2);
	}

#if DEBUG_CONTAINER
	if (n2.get_in_edge_list ().size ())
		RESULT ("\nError: We had expected in-edges of node %d to be empty after transfer to %d", 
		n2.get_node_id (), n1.get_node_id ());
	if (n2.get_out_edge_list ().size ())
		RESULT ("\nError: We had expected out-edges of node %d to be empty after transfer to %d", 
		n2.get_node_id (), n1.get_node_id ());
	DEBUG ("\nN1 %d and N2 %d after transfer", n1.get_node_id (), n2.get_node_id ());
	n1.print_node (NULL, nodes);
	n1.print_node_reverse (NULL);
	n2.print_node (NULL, nodes);
	n2.print_node_reverse (NULL);
#endif

	// Ideally we should delete N2 from NODES since it is no more
	// reachable. However, functions which are iterating over IN_EDGES and
	// OUT_EDGES still hold a reference of N2 and may try to access it in
	// NODES. Either we need to put a check before each access of NODES to
	// prevent segmentation fault or we can perform this deletion in CLEAN
	// ().
	// int n2_id = n2.get_node_id ();
	// if (nodes.find (n2_id) != nodes.end ())
	//	nodes.erase (n2_id);

	// Once all the out edges of N1 are transferred to out of N2, merge out
	// nodes of N2 (i.e. the AFFECTED_NODES) with their new siblings from
	// N1.

	set<node_index>::iterator ani;
	for (ani = affected_nodes.begin (); ani != affected_nodes.end (); ani++)
	{
		non_deterministic_simple_node * affected_node;
		affected_node = nodes[*ani];
		DEBUG ("\nCheck if transferred node %d (out of node %d) is mergeable", 
			*ani, n2.get_node_id ());
		merge_with_sibling_nodes (*affected_node, is_loop_merge);
	}

	return true;
}

/**
 * Merges node N with one of its sibling nodes. 
 *
 * @returns the node id of the sibling node if N gets merged with a sibling
 * node, else returns 0
 */

node_index non_deterministic_simple_graph::
merge_with_sibling_nodes (non_deterministic_simple_node & n, bool is_loop_merge)
{
	// If N1 and N2 are indistinguishable sibling nodes, then they have the
	// same IN_EDGE_LIST. By same, we mean that the source nodes of the
	// in-edges are indistinguishable (but may not have the same node_id).
	// The source nodes of the in-edges have the same node_id if the edges
	// are forward edges. However, the source nodes may have different
	// node_id and still be indistinguishable when the source nodes are in a
	// cycle with N1 and N2, respectively.

	// The following logic applies for parents/source nodes which are not
	// in a cycle with node N: If p1,p2,... are the parents of N. Then
	// child nodes c11,c12,...,c21,c22,... of p1,p2,... are siblings of N.
	// If cij has the same IN_EDGE_LIST as N, then the parents of cij are
	// also p1,p2,.... Therefore, it is sufficient to find such a sibling
	// (which can merge with N) in only p1. Note that this p1 should not be
	// in a cycle with N.

	// non_deterministic_simple_node * parent_node = n.get_acyclic_parent (nodes);

	// Finding an acyclic parent takes a lot of time. Therefore, below we
	// iterate over all the parents of N, say p1, to find out if there
	// exists a sibling from p1 which is indistinguishable with N.

	// An example where we might not find a sibling with the first parent
	// itself is: (n0,x,n1),(n0,x,n2),(n1,f,n2),(n2,f,n1)
	// Here n1 has n0 and n2 as the parents. If n2 is the first parent, then
	// sibling is n1 itself. Therefore, we need to go for the second parent
	// i.e. n0; this gives the sibling n2, and n1 and n2 are
	// indistinguishable.

	DEBUG ("\nmerge_with_sibling_nodes() for node %d", n.get_node_id ());

	map<label, set<node_index> > n_in_edges = n.get_in_edge_list ();
	map<label, set<node_index> >::iterator in_ei;
	for (in_ei = n_in_edges.begin (); in_ei != n_in_edges.end (); in_ei++)
	{
		DEBUG ("\nNext in-edge");
		set<node_index> n_parents = in_ei->second;
		non_deterministic_simple_node * parent_node = NULL;
		set<node_index>::iterator ni;
		// Iterate over all parents p1
		for (ni = n_parents.begin (); ni != n_parents.end (); ni++)
		{
			DEBUG ("\nNext parent");
			node_index n_parent = *ni;
			parent_node = nodes[n_parent];
			if (!parent_node)
				return 0;
	
			// Iterate over all sibling nodes from parent p1
			map<label, set<node_index> > parent_out_edges = parent_node->get_out_edge_list ();
			map<label, set<node_index> >::iterator ei;
			for (ei = parent_out_edges.begin (); ei != parent_out_edges.end (); ei++)
			{
				DEBUG ("\nNext out-edge");
				label parent_label = ei->first;
				set<node_index> siblings = ei->second;
				DEBUG ("\nParent's label %d", parent_label);
				set<node_index>::iterator ni;
				for (ni = siblings.begin (); ni != siblings.end (); ni++)
				{
					DEBUG ("\nNext sibling");
					non_deterministic_simple_node * sibling_node = nodes[*ni];
					DEBUG ("\nSibling node %d", *ni);
					if (sibling_node->get_node_id () == n.get_node_id ())
					{
						DEBUG ("\nTHIS node=N=%d", n.get_node_id ());
						continue;
					}
					if (merge_nodes (*sibling_node, n, is_loop_merge))
						return sibling_node->get_node_id ();
				}
			}
		}
	}

	DEBUG ("\nOut of loop");
	return 0;
}

/**
 * This function should be called after merging graphs which have been computed
 * along the two predecessor branches. A graph computed along an individual
 * branch has no mergeable nodes. After merging the two graphs from the two
 * branches, each label (edge) pointing to a set of nodes can have only two
 * mergeable nodes in the set.  Therefore, this function finds only the first
 * occurrence of two mergeable nodes for each label (edge), and then merges
 * them.
 */

void non_deterministic_simple_graph::
merge_child_nodes (non_deterministic_simple_node & n, bool is_loop_merge)
{
	DEBUG ("\nmerge_child_nodes of %d", n.get_node_id ());

	map<label, set<node_index> > n_out_edges = n.get_out_edge_list ();
	map<label, set<node_index> >::iterator ei;
	for (ei = n_out_edges.begin (); ei != n_out_edges.end (); ei++)
	{
		DEBUG ("\nOut edge with label %d", ei->first);
		set<node_index> n_out_nodes = ei->second;
		set<node_index>::iterator ni;
		for (ni = n_out_nodes.begin (); ni != n_out_nodes.end (); ni++)
		{
			DEBUG ("\nOut node %d", *ni);

			non_deterministic_simple_node * n_out_node = nodes[*ni];
			if (merge_with_sibling_nodes (*n_out_node, is_loop_merge))
				// Break on finding the first occurrence of two
				// mergeable nodes.
				break;
		}
	}
}

void non_deterministic_simple_graph::
m_limit_graph (int m_limit)
{
	map<label, set<node_index> > out_edges = stack->get_out_edge_list ();
	map<label, set<node_index> >::iterator vi;
	for (vi = out_edges.begin (); vi != out_edges.end (); vi++)
	{
		set<node_index> s = vi->second;
		if (s.size () > m_limit)
		{
			set<node_index>::iterator ni;
			ni = s.begin ();
			non_deterministic_simple_node * n1 = nodes[*ni];
			ni++;
			set<node_index> affected_nodes;

			// Merge all same named nodes with N1 to bring multiplicity count to 1.
			// for (; ni != s.end (); ni++)
			{
				// Merge one node with N1 to bring the mulitplicity count to M_LIMIT.
				non_deterministic_simple_node * n2 = nodes[*ni];

				set<node_index> n2_affected_nodes;
				n2_affected_nodes = n1->transfer_out_edges (*n2, nodes, stack->get_node_id ());
				n1->transfer_in_edges (*n2, nodes, stack->get_node_id ());
				affected_nodes.insert (n2_affected_nodes.begin (), n2_affected_nodes.end ());
			}

			// Once all the out edges of N1 are transferred to out
			// of N2, merge out nodes of N2 (i.e. the
			// AFFECTED_NODES) with their new siblings from N1.
		
			set<node_index>::iterator ani;
			for (ani = affected_nodes.begin (); ani != affected_nodes.end (); ani++)
			{
				non_deterministic_simple_node * affected_node;
				affected_node = nodes[*ani];
				DEBUG ("\nCheck if transferred node %d is mergeable", *ani);
				// Here we do not change merging criterion
				// whether or not it is a loop merge.
				// Therefore, FALSE.
				merge_with_sibling_nodes (*affected_node, false);
			}
		}
	}
}

set<label> non_deterministic_simple_graph::
get_pointees (label pointer)
{
	set<node_index> addr_nodes;
	get_addressof_nodes (pointer, addr_nodes);
	set<node_index> pointee_nodes;
	get_destination_nodes (addr_nodes, ASTERISK, pointee_nodes);
	set<node_index> pointee_names;
	get_nodes_names (pointee_nodes, pointee_names);
	return pointee_names;
}

/** 
 * Fetches node(s) pointed by VARIABLE.
 */

void non_deterministic_simple_graph::
get_addressof_nodes (label variable, set<node_index> & addr_nodes)
{
	// Get &VARIABLE
	stack->get_destination_nodes (variable, stack->get_node_id (), addr_nodes);

#if DEBUG_CONTAINER
	set<node_index>::iterator ni;
	DEBUG ("\nFetched addr nodes for variable %d: ", variable);
	for (ni = addr_nodes.begin (); ni != addr_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif
}

/**
 * Fetches node(s) pointed by VARIABLE.  Generates a node if such a node is not
 * already present.
 */ 

void non_deterministic_simple_graph::
generate_addressof_nodes (label variable, set<node_index> & addr_nodes)
{
	DEBUG ("\ngenerate_addressof_nodes (%d)", variable);

#if UNDEF_LOCATION == 0
	if (variable == undef_id)
		return;
#endif

#if NULL_LOCATION == 0
	if (variable == null_id)
		return;
#endif

#if READONLY_LOCATION == 0
	if (variable == readonly_id)
		return;
#endif

	set<node_index> addr_nodes_temp;
	get_addressof_nodes (variable, addr_nodes_temp);

	if (addr_nodes_temp.size ())
	{
		addr_nodes.insert (addr_nodes_temp.begin (), addr_nodes_temp.end ());
		return;
	}

	non_deterministic_simple_node * addr_node;
	addr_node = new non_deterministic_simple_node;
	node_index id = addr_node->get_node_id ();
	nodes[id] = addr_node;
	DEBUG ("\nInserting edge for variable %d in stack node", variable);
	stack->insert_edge (variable, *addr_node, stack->get_node_id ());

	addr_nodes.insert (id);

#if DEBUG_CONTAINER
	set<node_index>::iterator ni;
	DEBUG ("\ngenerated addr node: ");
	for (ni = addr_nodes.begin (); ni != addr_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif

#if FIELD_CONNECT_BASED_ON_TYPE
	// Connect V.FIELD to V via FIELD if V node exists here in the graph. 
	// Example: struct node1 { struct node1 * F1; struct node2 F2; }; 
	//          struct node2 { int * F3; int * F4; }
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

	generate_addressof_field_nodes (variable, addr_nodes);
#endif
}

/**
 * Given VARIABLE whose nodes are in ADDR_NODES, this function generates all
 * (recursively nested) field nodes inside structure VARIABLE and connects them
 * via field offset difference.
 */

void non_deterministic_simple_graph::
generate_addressof_field_nodes (label variable, set<node_index> & addr_nodes)
{
	csvarinfo_t var = VEC_index (csvarinfo_t, program.variable_data, variable);
	// Return if variable has no fields.
	if (!var->offset && !var->next)
		return;
	// Return if variable is function. (NEXT field of function csvarinfo_t
	// is connected to its function parameter).
	if (program.function_var (var))
		return;
	// Return if variable is function parameter. (OFFSET field of parameter
	// csvarinfo_t is set to the position of the parameter with respect to
	// other parameters).
	if (program.parameter_var (var))
		return;

	// Generate field nodes nested inside VAR and connect them with an edge
	// labeled with offset difference. 
	insert_field_edges (addr_nodes, var);

	// Generate the root variable, which has 0 offset. This will
	// recursively generate and connect all field nodes of this variable.
	// This is redundant if VAR is already at offset 0 but not otherwise.
	csvarinfo_t var_root = program.cs_lookup_vi_for_tree (var->decl);
	DEBUG ("\nvar=%s(%d), var_root=%s(%d)", var->name, var->id, var_root->name, var_root->id);
	set<node_index> var_root_nodes;
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
 * This function fetches nodes pointed by VARIABLE.*.FIELD.
 *
 * @returns true if the destination node needs to be added to THIS graph.
 */

bool non_deterministic_simple_graph::
get_pointer_nodes (label variable, list<label> * field_sequence, set<node_index> & pointer_nodes)
{
	DEBUG ("\nget_pointer_nodes()");

	// Get VARIABLE
	set<node_index> addr_nodes;
	get_addressof_nodes (variable, addr_nodes);

	// Get VARIABLE.*
	set<node_index> dest_nodes;
	bool new_node_needed = get_destination_nodes (addr_nodes, ASTERISK, dest_nodes);
	DEBUG ("\ndest_nodes.size()=%d", dest_nodes.size ());

	// Get VARIABLE.*.FIELD
	if (!field_sequence)
	{
		pointer_nodes = dest_nodes;
		return new_node_needed;
	}

	list<label>::iterator fi;
	for (fi = field_sequence->begin (); fi != field_sequence->end (); fi++)
	{
		DEBUG ("\nField %d", *fi);
		pointer_nodes.clear ();
		get_field_nodes (dest_nodes, *fi, pointer_nodes);
		// get_field_nodes() fetches VARIABLE.*.FIELD nodes if found, else
		// leaves VARIABLE.* in DEST_NODES
		new_node_needed |= dest_nodes.size ();
		dest_nodes = pointer_nodes;
	}
	DEBUG ("\npointer_nodes.size()=%d", pointer_nodes.size ());
	DEBUG ("\ndone get_pointer_nodes()");
	return new_node_needed;
}

/**
 * This function fetches nodes pointed by VARIABLE.*.FIELD. It generates nodes
 * (for example, undef, V.FIELD nodes) as per requirement in THIS graph. 
 */

void non_deterministic_simple_graph::
generate_pointer_nodes (label variable, list<label> * field_sequence, set<node_index> & pointer_nodes)
{
	DEBUG ("\ngenerate_pointer_nodes()");

	// Get VARIABLE
	set<node_index> addr_nodes;
	get_addressof_nodes (variable, addr_nodes);

	// Get VARIABLE.*
	set<node_index> dest_nodes;
	get_destination_nodes (addr_nodes, ASTERISK, dest_nodes);
	DEBUG ("\ndest_nodes.size()=%d", dest_nodes.size ());

	if (!field_sequence)
	{
		pointer_nodes = dest_nodes;
		return;
	}

	// Generate VARIABLE.*.FIELD
	// Get type of node being dereferenced. This is required if a heap
	// field node needs to be created on-the-fly.
	csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, variable);
	list<label>::iterator fi;
	for (fi = field_sequence->begin (); fi != field_sequence->end (); fi++)
	{
		DEBUG ("\ngenerate_field_nodes (field=%d)", *fi);
		pointer_nodes.clear ();
		generate_field_nodes (dest_nodes, v_info->decl, *fi, pointer_nodes);
		dest_nodes = pointer_nodes;
	}
	DEBUG ("\npointer_nodes.size=%d", pointer_nodes.size ());
}

/**
 * Fetches nodes pointed by VARIABLE.*.FIELD.*. 
 * 
 * @returns true if the destination is undef and UNDEF node does not exist in
 * THIS graph.
 *
 */

bool non_deterministic_simple_graph::
get_deref_nodes (label variable, list<label> * field_sequence, set<node_index> & destination_nodes)
{
	DEBUG ("\nget_deref_nodes (%d)", variable);
	set<node_index> pointer_nodes;
	set<node_index> heap_nodes;

	// Get VARIABLE.*.FIELD nodes in POINTER_NODES.
	// If new_node_needed is true, then either UNDEF node is missing or
	// V.FIELD node is missing. In both cases, the destination of
	// get_deref_nodes() is undef.
	bool new_node_needed = get_pointer_nodes (variable, field_sequence, pointer_nodes);
		
	// Get VARIABLE.*.FIELD.* from POINTER_NODES 
	// If out_edge_missing is true, then the destination of
	// get_deref_nodes() is undef.
	bool out_edge_missing = get_destination_nodes (pointer_nodes, ASTERISK, destination_nodes);

	if (new_node_needed || out_edge_missing)
	{
		set<node_index> undef_nodes;
		get_addressof_nodes (undef_id, undef_nodes);
		destination_nodes.insert (undef_nodes.begin (), undef_nodes.end ());
		if (undef_nodes.size ())
			return false;
	}
	return true;
}

/**
 * Fetches nodes pointed by VARIABLE.*.FIELD.*. If the destination is undef and
 * an UNDEF node is missing, this function generates an UNDEF node.
 */

void non_deterministic_simple_graph::
generate_deref_nodes (label variable, list<label> * field_sequence, set<node_index> & destination_nodes) 
{
	DEBUG ("\ngenerate_deref_nodes (%d)", variable);
	bool new_undef_node_needed = get_deref_nodes (variable, field_sequence, destination_nodes);
	if (new_undef_node_needed)
		generate_addressof_nodes (undef_id, destination_nodes);
}

/**
 * Fetches nodes that are must pointed by VARIABLE.*.FIELD.
 */

void non_deterministic_simple_graph::
get_must_pointer_nodes (label variable, list<label> * field_sequence, set<node_index> & destination_nodes)
{
	// Get VARIABLE
	set<node_index> addr_nodes;
	get_addressof_nodes (variable, addr_nodes);

	// Get VARIABLE.*
	set<node_index> dest_nodes;
	get_destination_nodes (addr_nodes, ASTERISK, dest_nodes);

	// Find nodes that have must points-to relation with VARIABLE.*.
	// Here if all the DEST_NODES have the same non-heap name, then the
	// relation is must. 
	set<label> dest_nodes_names;
	get_nodes_names (dest_nodes, dest_nodes_names);
	// If there are more than one names. 
	if (dest_nodes_names.size () != 1)
		return;

	// Get the only destination node name
	label v = *(dest_nodes_names.begin ());

	// If the destination is undef
	if (v == undef_id)
		return;

	// Return empty FIELD_NODES if the only name in DEST_NODES_NAMES is a
	// heap name.
	csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, v);
	if (v_info->is_heap_var)
		return;

	// Get all nodes with the name DEST_NODES_NAMES. Do not use the
	// DEST_NODES produced above. This is required in access-based
	// abstraction where more than one nodes have the same name.
	dest_nodes.clear ();
	get_addressof_nodes (v, dest_nodes);

	if (!field_sequence)
	{
		destination_nodes = dest_nodes;
		return;
	}

	// Get VARIABLE.*.FIELD nodes. 
	set<node_index> field_nodes;
	bool new_node_needed = false;
	list<label>::iterator fi;
	for (fi = field_sequence->begin (); fi != field_sequence->end (); fi++)
	{
		field_nodes.clear ();
		get_field_nodes (dest_nodes, *fi, field_nodes);
		new_node_needed |= dest_nodes.size ();
		// If the destination is undef
		if (new_node_needed)
			return;

		// FIXME: Since connection with field_nodes is created by
		// struct definitions of the program, there can never be two
		// names or undef FIELD_NODES. Either remove the following
		// checks or at least move them outside this loop.

		// Find nodes that have must points-to relation with
		// VARIABLE.*.FIELD.  Here if all the FIELD_NODES have the same
		// name (which will obviously be non-heap), then the relation
		// is must.
		set<label> field_nodes_names;
		get_nodes_names (field_nodes, field_nodes_names);
		// If there are more than one names.
		if (field_nodes_names.size () != 1)
			return;

		// Get the only destination node name
		v = *(field_nodes_names.begin ());

		// If the destination is undef
		if (v == undef_id)
			return;

		dest_nodes = field_nodes;
	}

	destination_nodes = field_nodes;
}

/**
 * This function fetches the out-nodes via FIELD from every node in S. It is
 * more than what GET_DESTINATION_NODES() does, in the sense that it
 * additionally deals with heap and UNDEF nodes in a special way if they do not
 * have an out-edge labeled FIELD. 
 * Note that this function leaves in S only those remaining nodes which do not
 * have an out-edge labeled FIELD and whose corresponding V.FIELD node is not
 * found.
 */

void non_deterministic_simple_graph::
get_field_nodes (set<node_index> & s, label field, set<node_index> & field_nodes)
{
	DEBUG ("\nget_field_nodes() of field %d", field);

	set<node_index>::iterator ni;
	for (ni = s.begin (); ni != s.end (); )
	{
		DEBUG ("\nNode %d", *ni);
		non_deterministic_simple_node * n = nodes[*ni];
		label node_name = n->get_node_name (stack->get_node_id ());

		// Node in set S is undef/null/readonly. 
		// Note that FIELD is absent in x=y statements. Here y could be
		// pointing to NULL and get_field_nodes() is called on NULL
		// node with FIELD=0.  Precisely, we should add NULL node to
		// FIELD_NODES in such a case; but we cannot differentiate
		// between x=y and x=&(y->f).  Therefore, for a safe analysis,
		// we assume it is x=&(y->f) and we add UNDEF to FIELD_NODES.
		// FIXME: Use types or field_sequence to find if rhs is y or &(y->f).
		if (!program.is_proper_var (node_name))
		{
			DEBUG ("\nNode %d being dereferenced", *ni);
//#if UNDEF_LOCATION
			set<node_index> undef_nodes;
			get_addressof_nodes (undef_id, undef_nodes);
			field_nodes.insert (undef_nodes.begin (), undef_nodes.end ());
			if (undef_nodes.size ())
				s.erase (ni++);
			else
				ni++;

//#else
			// If there is no UNDEF node, then this is a
			// may-points-to analysis and we can safely say that
			// null is the pointee.
//			set<node_index> null_nodes;
//			get_addressof_nodes (null_id, null_nodes);
//			field_nodes.insert (null_nodes.begin (), null_nodes.end ());
//			if (null_nodes.size ())
//				s.erase (ni++);
//			else
//				ni++;

//#endif
			continue;
		}

		// If FIELD is the first member of node NI, then NI itself is
		// added to FIELD_NODES.
		if (field == 0)
		{
			DEBUG ("\nField %d == 0", field);
			field_nodes.insert (*ni);
			s.erase (ni++);
			continue;
		}

#if FIELD_CONNECT_BASED_ON_TYPE || FIELD_CONNECT_BASED_ON_PROGRAM
		// If FIELD is a subsequent member of node NI, then check if
		// out-node via FIELD already exists.
		set<node_index> out_nodes;
		n->get_destination_nodes (field, stack->get_node_id (), out_nodes);
		if (out_nodes.size ())
		{
			DEBUG ("\nOut-nodes from node %d via field %d are present", 
				*ni, field);
			field_nodes.insert (out_nodes.begin (), out_nodes.end ());
			// Do not erase NI from S because it will either get
			// erased in FIELD_CONNECT_BASED_ON_TYPE or via
			// cs_first_vi_for_offset().
		}
#endif

#if FIELD_CONNECT_BASED_ON_TYPE
		// If a field node would have existed, it would have been found
		// by get_destination_nodes() because the field nodes of the
		// source would already be connected to it. We do not want to
		// find the field nodes (by the same name) connected to other
		// nodesi i.e. using cs_first_vi_for_offset() as it's imprecise.
		if (out_nodes.size ())
			s.erase (ni++);
		else
			ni++;
		continue;

#elif FIELD_CONNECT_BASED_ON_PROGRAM
		// FIXME: We could make use of the in-edge information of
		// V.FIELD nodes --- if a V.FIELD node is pointed by V, then
		// surely, it has come from a control flow path other than NI
		// node. Therefore, now we need to fetch only those V.FIELD
		// nodes which have no in-edge from V. Actually V.FIELD=x.f.g
		// needs to be linked from x and x.f both. If it is not, then
		// we need to assume that x.f.g is reachable from NI.

#else
		// V may or may not be connected to V.FIELD. Therefore, in
		// addition to finding connected V.FIELD (as done above), do
		// not continue directly to the loop, but proceed to check if
		// there are any other pre-existing V.FIELD nodes. The need is
		// demonstrated in test31g.c
		// s.erase (ni++);
		// continue;
#endif

		csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, node_name);
		// STACK and HEAP with pre-existing field offset variables
		// If NI does not have an out-node via FIELD, then get the
		// pre-existing V.FIELD nodes.
		csvarinfo_t v_field_info = program.cs_first_vi_for_offset (v_info, field);
		if (v_field_info)
		{
			DEBUG ("\nGet Var-offset %s(%d)", v_field_info->name, v_field_info->id);
			// out_nodes.clear ();
			get_addressof_nodes (v_field_info->id, out_nodes);
			field_nodes.insert (out_nodes.begin (), out_nodes.end ());

			// If OUT_NODES has been populated from
			// get_destination_nodes() or from
			// cs_first_vi_for_offset(), erase.
			if (out_nodes.size ())
				s.erase (ni++);
			else
				ni++;
			continue;
		}

		ni++;
	}

#if DEBUG_CONTAINER
	DEBUG ("\nget_field_nodes() with field %d: ", field);
	for (ni = field_nodes.begin (); ni != field_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif
}

/**
 * This function generates the out-nodes via FIELD from every node in S.
 */

void non_deterministic_simple_graph::
generate_field_nodes (set<node_index> & s, tree s_type, label field, set<node_index> & field_nodes)
{
	DEBUG ("\ngenerate_field_nodes() of field %d", field);

	// Get existing out-nodes from nodes in S. 
	get_field_nodes (s, field, field_nodes);

	// Generate out-nodes via FIELD from the nodes remaining in S.
	set<node_index>::iterator ni;
	for (ni = s.begin (); ni != s.end (); ni++)
	{
		DEBUG ("\nNode %d", *ni);
		non_deterministic_simple_node * n = nodes[*ni];
		label node_name = n->get_node_name (stack->get_node_id ());

		// Node in set S is undef/null/readonly. 
		// Note that FIELD is absent in x=y statements. Here y could be
		// pointing to NULL and get_field_nodes() is called on NULL
		// node with FIELD=0.  Precisely, we should add NULL node to
		// FIELD_NODES in such a case; but we cannot differentiate
		// between x=y and x=&(y->f).  Therefore, for a safe analysis,
		// we assume it is x=&(y->f) and we add UNDEF to FIELD_NODES.
		// FIXME: Use types to find if rhs is y or &(y->f).
		if (!program.is_proper_var (node_name))
		{
			DEBUG ("\nNode %d is being dereferenced", *ni);
//#if UNDEF_LOCATION
			generate_addressof_nodes (undef_id, field_nodes);
//#else
			// If there is no UNDEF node, then this is a
			// may-points-to analysis and we can safely say that
			// null is the pointee.
//			generate_addressof_nodes (null_id, field_nodes);
//#endif

			continue;
		}

		csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, node_name);
		DEBUG ("\nv_info=%s(%d)", v_info->name, v_info->id);

#if FIELD_CONNECT_BASED_ON_TYPE
		// If V_INFO is a stack, then field nodes already exist and
		// will get found by get_field_nodes() via
		// get_destination_nodes(); therefore, continue to the loop.
		if (!v_info->is_heap_var)
		{
			DEBUG ("\nField of stack might have been found");
			continue;
		}

		// Else (if V_INFO is a heap H) if H.FIELD needs to be created
		// on-the-fly (i.e. type of H is ptr_type_node = VOID * created
		// in parser.cpp), then generate field nodes i.e. do not
		// continue to the loop. Else field node has already been
		// found; therefore continue to the loop. 
		tree decl = v_info->decl;
		if (decl && TREE_CODE (decl) == VAR_DECL)
		{
			DEBUG ("\nvar_decl found");
			if (TREE_TYPE (decl) != ptr_type_node)
			{
				DEBUG ("\nHeap type already available");
				continue;
			}
			else
				DEBUG ("\non-the-fly generation needed.");
		}
		else
			RESULT ("\nError: VAR_DECL not found in heap");
#else
		// STACK and HEAP with pre-existing field offset variables
		// If NI does not have an out-node via FIELD, then get the
		// pre-existing V.FIELD nodes.
		csvarinfo_t v_field_info = program.cs_first_vi_for_offset (v_info, field);
		if (v_field_info)
		{
			DEBUG ("\nGenerate Var-offset %s(%d)", v_field_info->name, v_field_info->id);
			set<node_index> field_nodes_temp;
			generate_addressof_nodes (v_field_info->id, field_nodes_temp);
			field_nodes.insert (field_nodes_temp.begin (), field_nodes_temp.end ());

			// Structure fields are used only in hmmer; not used in
			// lbm,bzip2,libquantum,sjeng. There is replication of
			// nodes only in sjeng,hmmer; no replication happens in
			// lbm,bzip2,libquantum.  The connections of
			// (replicated) v.0 with v.32 may, therefore, be
			// required only in hmmer; however, in hmmer, this v.32
			// does not have any out-edge; therefore, no use of
			// creating an edge from v.0 to v.32.

#if FIELD_CONNECT_BASED_ON_PROGRAM
			// Connect V.FIELD to V via FIELD:
			// Create an edge from NI to FIELD_NODES_TEMP via FIELD
			// here itself.  Otherwise in
			// process_assignment_statement(), spurious connections
			// via FIELD might get created due to multiple variable
			// pointees of lhs and rhs.  If a node has been
			// generated and not fetched.  Without this condition,
			// it leads to an infinite loop, where NI is made to
			// point to all the pre-existing FIELD_NODES_TEMP.???
			if (field_nodes_temp.size () == 1)
			{
				set<node_index> src_node;
				src_node.insert (*ni);
				insert_edges (src_node, field_nodes_temp, field);
			}
#endif
			continue;
		}
#endif

		// HEAP
		// If NI does not have an out-node via FIELD, then search if
		// V.FIELD node exists in VARIABLE_DATA and in THIS graph.
		if (v_info->is_heap_var)
		{
			DEBUG ("\nHeap node %d, name: %s(%d)", *ni, v_info->name, v_info->id);
			DEBUG ("\nGenerate heap at offset %d from heap node %s", field, v_info->name);
			generate_heap_field_nodes (n->get_node_id (), s_type, field, field_nodes);
			continue;
		}

		RESULT ("\nError: What is this case in generate_field_nodes()?");
	}

#if DEBUG_CONTAINER
	DEBUG ("\ngenerate_field_nodes() with field %d: ", field);
	for (ni = field_nodes.begin (); ni != field_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif
}

/**
 * Create H.FIELD in program.variable_data and generate a corresponding node.
 */

void non_deterministic_simple_graph::
generate_heap_field_nodes (node_index heap_node_id, tree heap_pointer_type, label field, set<node_index> & heap_field_nodes)
{
	DEBUG ("\ngenerate_heap_field_nodes()");
	non_deterministic_simple_node * n = nodes[heap_node_id];
	label heap_var = n->get_node_name (stack->get_node_id ());

        csvarinfo_t heap_field_var =
                program.generate_heap_field_vars (heap_var, heap_pointer_type, field);

        if (!heap_field_var)
                return;

	set<node_index> heap_nodes_temp;
	generate_addressof_nodes (heap_field_var->id, heap_nodes_temp);

#if FIELD_CONNECT_BASED_ON_PROGRAM
	// Create an edge from N to HEAP_NODES_TEMP via FIELD here itself.
	// Otherwise in process_assignment_statement(), spurious connections
	// via FIELD might get created due to multiple variable pointees of lhs
	// and rhs.  If a node has been generated and not fetched.
	if (heap_nodes_temp.size () == 1)
	{
		set<node_index> src_node;
		src_node.insert (heap_node_id);
		insert_edges (src_node, heap_nodes_temp, field);
	}
#endif

	heap_field_nodes.insert (heap_nodes_temp.begin (), heap_nodes_temp.end ());
}

/**
 * @returns true if source is null/undef/readonly node; in which case, out-edge
 * is missing i.e. the destination is undef.
 */

bool non_deterministic_simple_graph::
get_destination_nodes (set<node_index> & s, label l, set<node_index> & destination_nodes)
{
	bool out_edge_missing = false;

	set<node_index>::iterator ni;
	for (ni = s.begin (); ni != s.end (); ni++)
	{
		DEBUG ("\nget_destination_nodes (node=%d,field=%d)", *ni, l);
		non_deterministic_simple_node * n = nodes[*ni];
		set<node_index> dest_nodes_temp;
		out_edge_missing += n->get_destination_nodes (l, stack->get_node_id (), dest_nodes_temp);

#if DEBUG_CONTAINER
		// Check if DESTINATION_NODES are the destinations of S
		set<node_index>::iterator di;
		DEBUG ("\ndest_nodes_temp: ");
		for (di = dest_nodes_temp.begin (); di != dest_nodes_temp.end (); di++)
		{
			non_deterministic_simple_node * dest = nodes[*di];
			map<label, set<node_index> > dest_in_edges = dest->get_in_edge_list ();
			set<node_index> src_nodes = dest_in_edges[l];
			if (src_nodes.find (n->get_node_id ()) == src_nodes.end ())
				RESULT ("\nError: did not get correct destination nodes");
			DEBUG ("%d,", *di);
		}
#endif
		destination_nodes.insert (dest_nodes_temp.begin (), dest_nodes_temp.end ());
	}

#if DEBUG_CONTAINER
	DEBUG ("\nFetched dest nodes for l %d: ", l);
	for (ni = destination_nodes.begin (); ni != destination_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif

	DEBUG ("\nout_edge_missing=%d", out_edge_missing);
	return out_edge_missing;
}

/**
 * If set S contains universal node, substitute it with all the nodes in the
 * graph.
 */

bool non_deterministic_simple_graph::
substitute_universal_node (set<node_index> & s)
{
	set<node_index> universal_nodes;
	get_addressof_nodes (universal_id, universal_nodes);
	node_index universal_node = *(universal_nodes.begin ());
	
	// If universal node is not present in set S
	if (s.find (universal_node) == s.end ())
		return false;

	// Insert all graph nodes
	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
		s.insert (ni->first);

	s.erase (stack->get_node_id ());

	return true;
}

void non_deterministic_simple_graph::
get_in_nodes (set<node_index> & pointees, set<node_index> & in_nodes)
{
	set<node_index>::iterator ni;
	for (ni = pointees.begin (); ni != pointees.end (); ni++)
	{
		non_deterministic_simple_node * n = nodes[*ni];
		map<label, set<node_index> > in_edges = n->get_in_edge_list ();
		map<label, set<node_index> >::iterator ei;
		for (ei = in_edges.begin (); ei != in_edges.end (); ei++)
		{
			set<node_index> n_in_nodes = ei->second;
			in_nodes.insert (n_in_nodes.begin (), n_in_nodes.end ());
		}
	}
}

/**
 * Given x.f.g, this function recursively fetches nodes reached by x then f
 * then g. 
 */

set<node_index> non_deterministic_simple_graph::
get_var_node (label var)
{
	set<node_index> var_nodes;

	map<label, set<node_index> > out_edges = stack->get_out_edge_list ();
	map<label, set<node_index> >::iterator ei;
	for (ei = out_edges.begin (); ei != out_edges.end (); ei++)
	{
		label prefix_var = ei->first;

		// If prefix_var is a heap variable (e.g. heap.13) or
		// prefix_var is not proper variable (i.e. varid <= 2), then
		// prefix_var+succ_offset cannot be equivalent to VAR.
		if (program.cs_get_varinfo (prefix_var)->is_heap_var)
			continue;
		if (!program.is_proper_var (prefix_var))
			continue;

		set<node_index> out_nodes = ei->second;

		set<node_index>::iterator ni;
		for (ni = out_nodes.begin (); ni != out_nodes.end (); ni++)
		{
			set<node_index> var_nodes_temp;
			non_deterministic_simple_node * n = nodes[*ni];
			var_nodes_temp = n->get_var_node (var, prefix_var, nodes);	
			var_nodes.insert (var_nodes_temp.begin (), var_nodes_temp.end ());
		}
	}
	return var_nodes;
}

void non_deterministic_simple_graph::
delete_out_edges (set<node_index> source_nodes, label l)
{
	DEBUG ("\nDeleting edge with label %d", l);

	set<node_index>::iterator ni;
	for (ni = source_nodes.begin (); ni != source_nodes.end (); ni++)
	{
		non_deterministic_simple_node * n = nodes[*ni];
		delete_out_edges (*n, l);
	}
}

/* DELETE_EDGE () is called when the client analysis encounters a KILL
 * statement.  It wants to delete the edge.
 */

void non_deterministic_simple_graph::
delete_out_edges (non_deterministic_simple_node & n, label l)
{
	DEBUG ("\ndelete_out_edge ()");

	map<label, set<node_index> > n_out_edge_list = n.get_out_edge_list ();
	if (n_out_edge_list.find (l) == n_out_edge_list.end ())
	{
		DEBUG ("\nLabel %d not found", l);
		return;
	}

	set<node_index> dest_nodes = n_out_edge_list[l];

	// Delete edge between N (source) and destination nodes 
	set<node_index>::iterator dest_i;
	non_deterministic_simple_node * dest = NULL;
	for (dest_i = dest_nodes.begin (); dest_i != dest_nodes.end (); dest_i++)
	{
		dest = nodes[*dest_i];

#if DEBUG_CONTAINER
		map<label, set<node_index> > dest_in_edges = dest->get_in_edge_list ();
		if (dest_in_edges.find (l) == dest_in_edges.end ())
		{
			RESULT ("\nError: Node %d has an out edge to node %d", 
 				n.get_node_id (), dest->get_node_id ());	
			RESULT (" but node %d does not have an in edge to node %d", 
				dest->get_node_id (), n.get_node_id ());
			return;
		}
#endif

		DEBUG ("\nDeleting edge %d -> %d -> %d", n.get_node_id (), l, *dest_i);
		if (dest)
		{
			n.delete_edge (l, *dest);
			// It might be more efficient to merge when all the
			// edges have been deleted.
			// merge_with_sibling_nodes (*dest);
		}

		else
			RESULT ("\nError: destination node is NULL");
	}

	// If N is a STACK node, then L is a root variable. In this case,
	// DEST_NODE_SET contains unreachable nodes. We need not merge them;
	// they will get removed in clean_unreachable_nodes ().
	if (n.get_node_id () == stack->get_node_id ())
		return;

	// Now that all the edges have been deleted, attempt for merging.
	for (dest_i = dest_nodes.begin (); dest_i != dest_nodes.end (); dest_i++)
	{
		dest = nodes[*dest_i];
		if (dest)
			// Here we do not change merging criterion whether or
			// not it is a loop merge. Therefore, FALSE.
			merge_with_sibling_nodes (*dest, false);
	}
}

void non_deterministic_simple_graph::
delete_in_edges (non_deterministic_simple_node & n)
{
	map<label, set<node_index> > n_in_edges = n.get_in_edge_list ();
	map<label, set<node_index> >::iterator n_in_ei;
	for (n_in_ei = n_in_edges.begin (); n_in_ei != n_in_edges.end (); n_in_ei++)
	{
		label l = n_in_ei->first;
		DEBUG ("\nDeleting -> %d -> %d edge", l, n.get_node_id ());
		delete_in_edges (n, l);
	}

	// Merge with sibling nodes and then recursively merge
	// indistinguishable nodes too. However, once all the in-edges are
	// deleted, this node has no sibling. Therefore, no need to merge.
	// merge_with_sibling_nodes (n);
}

void non_deterministic_simple_graph::
delete_in_edges (non_deterministic_simple_node & n, label l)
{
	DEBUG ("\ndelete_in_edges ()");

	map<label, set<node_index> > n_in_edge_list = n.get_in_edge_list ();

	set<node_index> src_nodes = n_in_edge_list[l];

	// Delete edge between source node and node N (destination) 
	set<node_index>::iterator src_i;
	for (src_i = src_nodes.begin (); src_i != src_nodes.end (); src_i++)
	{
		non_deterministic_simple_node * src = nodes[*src_i];
		src->delete_edge (l, n);
	}

	// Instead of merging here, we have attempted the merging in
	// DELETE_IN_EDGES (N) since DELETE_IN_EDGES (N,L) is called only via
	// the former and never directly --- check FIXME.
	// merge_with_sibling_nodes (n);
}

void non_deterministic_simple_graph::
insert_edges (set<node_index> lhs_nodes, set<node_index> rhs_nodes, label l)
{
	DEBUG ("\ninsert_edges ()");
	node_index stack_id = stack->get_node_id ();

	// Inserting edge from all lhs to all rhs
	set<node_index>::iterator lhsi;
	for (lhsi = lhs_nodes.begin (); lhsi != lhs_nodes.end (); lhsi++)
	{
		node_index lhs_id = *lhsi;
		non_deterministic_simple_node * lhs_dest = nodes[*lhsi];
		DEBUG ("\nlhs_dest = %d", lhs_dest->get_node_id ());

		// If LHS_ID is not stack node and LHS_ID is an improper node,
		// then do not insert edge.
		label lhs_name = lhs_dest->get_node_name (stack_id);
		if (stack_id != lhs_id && !program.is_proper_var (lhs_name))
			continue;
		
		set<node_index>::iterator rhsi;
		for (rhsi = rhs_nodes.begin (); rhsi != rhs_nodes.end (); rhsi++)
		{
			non_deterministic_simple_node * rhs_dest;
			rhs_dest = nodes[*rhsi];

#if DEBUG_CONTAINER
			map<label, set<node_index> >::iterator outei;
			map<label, set<node_index> > out_edges = lhs_dest->get_out_edge_list ();
			outei = out_edges.find (l);
			if (outei != out_edges.end ())
			{
				set<node_index> out_nodes = outei->second;
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
			lhs_dest->insert_edge (l, *rhs_dest, stack->get_node_id ());
		}
	}

	// After adding all possible in-edges to each node in rhs_nodes, merge
	// with sibling nodes and then recursively merge indistinguishable
	// nodes too 
	set<node_index>::iterator rhsi;
	for (rhsi = rhs_nodes.begin (); rhsi != rhs_nodes.end (); rhsi++)
	{
		non_deterministic_simple_node * rhs_dest;
		rhs_dest = nodes[*rhsi];

		// Here we do not change merging criterion whether or not it is
		// a loop merge. Therefore, FALSE.
		node_index sibling_node = merge_with_sibling_nodes (*rhs_dest, false);
		if (sibling_node)
			DEBUG ("\nRhs node %d merged with node %d", *rhsi, sibling_node);
		else
			DEBUG ("\nRhs node %d cannot be merged", *rhsi);
	}
}

/**
 * Generate field edges from SRC_NODES to the field nodes inside structure
 * SRC_VAR.
 */

void non_deterministic_simple_graph::
insert_field_edges (set<node_index> & src_nodes, csvarinfo_t src_var)
{
	DEBUG ("\ninsert_field_edges (%s(%d))", src_var->name, src_var->id);
	// Get all the field variables inside structure SRC_VAR
	set<label> reachable_field_vars = program.get_reachable_fields (src_var);

	set<label>::iterator fi;
	for (fi = reachable_field_vars.begin (); fi != reachable_field_vars.end (); fi++)
	{
		label field_var = *fi;	
		if (!program.is_proper_var (field_var))
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

		set<node_index> field_nodes;
		generate_addressof_nodes (field_var, field_nodes);
		if (field_nodes.size () != 1)
		{
			RESULT ("\nError: Only one field node should have been generated.");
			return;
		}

		DEBUG ("\ninsert_field_edges: %s(%d) -> %d -> %s(%d)",
			src_var->name, src_var->id, field_edge, field_info->name, field_info->id);
		insert_edges (src_nodes, field_nodes, field_edge);
	}
}

void non_deterministic_simple_graph::
initialize (set<label> & vars, label init_value)
{
	DEBUG ("\ninitialize");
	if (!vars.size ())
		return;

	// Create initialization node
	set<node_index> init_nodes;
	generate_addressof_nodes (init_value, init_nodes);
	if (!init_nodes.size ())
		return;
	if (init_nodes.size () != 1)
	{
		RESULT ("\nError: This function assumes that there is a single init_node");
		return;
	}
	node_index init_nid = *(init_nodes.begin ());
	non_deterministic_simple_node * init_node = nodes[init_nid];
	
	RESULT ("\nInitialize with %d variables: ", init_value);
	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
	{
		// Create variable node
		label v = *vi;
		set<node_index> var_nodes;
		generate_addressof_nodes (v, var_nodes);

		// Create connection from variable node to initialization node
		set<node_index>::iterator ni;
		for (ni = var_nodes.begin (); ni != var_nodes.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes[*ni];
			n->insert_edge (ASTERISK, *init_node, stack->get_node_id ());
			RESULT ("%d,", v);
		}
	}
}

/**
 * This function checks if THIS graph is same as the parameter graph.
 */

bool non_deterministic_simple_graph::
is_value_same (non_deterministic_simple_graph & g)
{
	struct timeval start;
	start_timer (start);

	DEBUG ("\nnon_deterministic_simple_graph::is_value_same ()");
	if (nodes.size () != g.nodes.size ())
	{
#if DEBUG_CONTAINER
		DEBUG ("\nNodes # of THIS graph = %d, Nodes # of G graph = %d", 
			nodes.size (), g.nodes.size());
		map<node_index, non_deterministic_simple_node *>::iterator ni;
		DEBUG ("\nNodes of THIS graph = ");
		for (ni = nodes.begin (); ni != nodes.end (); ni++)
			DEBUG ("%d,", ni->first);
		DEBUG ("\nNodes of G graph = ");
		for (ni = g.nodes.begin (); ni != g.nodes.end (); ni++)
			DEBUG ("%d,", ni->first);
#endif

		stop_timer (start, is_value_same_stats);		
		return false;
	}

	// PROBLEM in our out-isomorphism algo:
	// Graph 1: edges: (0,1),(1,3),(1,4),(0,2),(2,3) and
	// Graph 2: edges: (5,6),(6,8),(6,9),(5,7),(7,9). 
	// Our algo does not consider the two graphs as isomorphic, even though
	// they are. Our algo marks 3-8 and 4-9 as equiv_node_pairs. but when
	// 2-7 are visited, it cannot backtrack to instead correctly mark 3-9
	// and 4-8 as equiv_node_pairs.
	// map<node_index, node_index> equiv_node_pairs;
	// return stack->is_out_graph_isomorphic 
	//	(*g.stack, nodes, g.nodes, equiv_node_pairs);


	if (value_property == in)
	{
		// This right now works only for in_language as the node
		// property. It computes EQUIV_STATE_PAIRS using HK algorithm.
		// Then it computes EQUIV_NODE_PAIRS from EQUIV_STATE_PAIRS.
		bool b = is_in_value_same (g);
		stop_timer (start, is_value_same_stats);		
		return b;
	}
	if (value_property == inout)
	{
		// This works for both in_language and in_isomorphism. 
		// If node_property is in_language, it computes
		// EQUIV_STATE_PAIRS using HK algorithm, and then uses
		// DEPTH_FIRST_COMPARISON while making calls to
		// IS_IN_LANGUAGE_SAME.
		// If node_property is in_isomorphism, it uses
		// DEPTH_FIRST_COMPARISON while making calls to
		// IS_IN_GRAPH_ISOMORPHIC.
		bool b = is_inout_value_same (g);
		stop_timer (start, is_value_same_stats);
		return b;
	}
	
	RESULT ("\nError: value_property not initialized correctly");
	stop_timer (start, is_value_same_stats);
	return false;
}

bool non_deterministic_simple_graph::
is_inout_value_same (non_deterministic_simple_graph & g)
{
	DEBUG ("\nis_inout_value_same ()");

	map<node_index, node_index> equiv_node_pairs;
	map<state_index, state_index, state_order> equiv_state_pairs;

	if (node_property == in_language)
		if (!get_equivalent_states (g, equiv_state_pairs))
		{
			DEBUG ("\nequiv_state_pairs cannot be computed in is_inout_value_same ()");
			return false;
		}

	// Move depth-first to compare the in-properties of nodes in graph1
	// with the nodes in graph2.
	bool is_same = stack->depth_first_comparison 
		(*g.stack, nodes, g.nodes, equiv_node_pairs, equiv_state_pairs);

#if DEBUG_CONTAINER
	if (!is_same)
		return is_same;
	DEBUG ("\nequiv_node_pairs:");
	map<node_index, node_index>::iterator npi;
	for (npi = equiv_node_pairs.begin (); npi != equiv_node_pairs.end (); npi++)
		DEBUG ("(%d,%d),", npi->first, npi->second);
#endif

#if CHECK_CONTAINER
	if (is_same)
	{
		DEBUG ("\nCheck inout comparison by matching in- and out-edges of equiv_node_pairs");
		DEBUG ("\nCheck that every node of THIS graph is correctly mapped to a node of G graph.");
		is_inout_comparison_okay (g, equiv_node_pairs);
		DEBUG ("\nCheck that every node of G graph is correctly mapped to a node of THIS graph.");
		bool is_okay = g.is_inout_comparison_okay (*this, equiv_node_pairs);
		DEBUG ("\nis_inout_comparison_okay --- using in- and out-edges = %d", is_okay);
	}
#endif

#if CHECK_CONTAINER
	if (is_same)
	{
		DEBUG ("\nCheck inout comparison by running another node property ");
		DEBUG ("and then comparing equiv_node_pairs");
		bool is_okay = is_inout_comparison_okay (g, equiv_node_pairs, equiv_state_pairs);
		DEBUG ("\nis_inout_comparison_okay --- by running another node property = %d", is_okay);
	}
#endif

	return is_same;
}

bool non_deterministic_simple_graph::
is_in_value_same (non_deterministic_simple_graph & g)
{
	DEBUG ("\nis_in_value_same ()");

	// HOPKROFT-KARP ALGORITHM FOR NFAs
	map<state_index, state_index, state_order> equiv_state_pairs;
	if (!get_equivalent_states (g, equiv_state_pairs))
	{
		DEBUG ("\nequiv_state_pairs cannot be computed");
		return false;
	}

	map<node_index, node_index> equiv_node_pairs;
	bool is_same = get_equivalent_nodes (equiv_state_pairs, equiv_node_pairs);
	DEBUG ("\nis_value_language_same = %d", is_same);

#if DEBUG_CONTAINER
	if (is_same)
	{
		DEBUG ("\nequiv_node_pairs:");
		map<node_index, node_index>::iterator npi;
		for (npi = equiv_node_pairs.begin (); npi != equiv_node_pairs.end (); npi++)
			DEBUG ("(%d,%d),", npi->first, npi->second);
	}
#endif

#if CHECK_CONTAINER
	if (is_same)
		is_in_comparison_okay (g, equiv_node_pairs, equiv_state_pairs);
	// If IS_IN_VALUE_SAME is false, then surely IS_INOUT_VALUE_SAME should
	// also be false.
	if (!is_same && is_inout_value_same (g))
		RESULT ("\nError: is_in_value_same is false, but is_inout_value_same is true.");
#endif
	return is_same;
}

bool non_deterministic_simple_graph::
get_equivalent_states (non_deterministic_simple_graph & g,
	map<state_index, state_index, state_order> & equiv_state_pairs)
{
	DEBUG ("\nget_equivalent_states ()");

	state_index this_root;
	this_root.insert (stack->get_node_id ());
	state_index g_root;
	g_root.insert (g.stack->get_node_id ());
	
	// HOPKROFT-KARP ALGORITHM FOR NFAs
	bool is_equiv = get_equivalent_states (this_root, g_root, *this, g, equiv_state_pairs);
	DEBUG ("\nis_equiv_state_pairs = %d", is_equiv);

#if DEBUG_CONTAINER
	map<state_index, state_index>::iterator pi;
	DEBUG ("\nequiv_state_pairs:");
	for (pi = equiv_state_pairs.begin (); pi != equiv_state_pairs.end (); pi++)
	{
		state_index::iterator ni;
		state_index s1 = pi->first;
		state_index s2 = pi->second;
		DEBUG ("\n({");
		for (ni = s1.begin (); ni != s1.end (); ni++)
			DEBUG ("%d,", *ni);
		DEBUG ("},{");
		for (ni = s2.begin (); ni != s2.end (); ni++)
			DEBUG ("%d,", *ni);
		DEBUG ("})");
	}
#endif

	return is_equiv;
}

/**
 * Hopkroft-Karp algorithm for NFAs.
 */

bool non_deterministic_simple_graph::
get_equivalent_states (state_index & s1, state_index & s2, 
	non_deterministic_simple_graph & g1,
	non_deterministic_simple_graph & g2,
	map<state_index, state_index, state_order> & equiv_state_pairs)
{
	DEBUG ("\nget_equivalent_states () --- HK algo");
#if DEBUG_CONTAINER
	state_index::iterator ni;
	DEBUG ("\ns1=");
	for (ni = s1.begin (); ni != s1.end (); ni++)
		DEBUG ("%d,", *ni);
	DEBUG ("\ns2=");
	for (ni = s2.begin (); ni != s2.end (); ni++)
		DEBUG ("%d,", *ni);
	map<node_index, non_deterministic_simple_node *>::iterator mni;
	DEBUG ("\ng1.nodes=");
	for (mni = g1.nodes.begin (); mni != g1.nodes.end (); mni++)
		DEBUG ("%d,", mni->first);
	DEBUG ("\ng2.nodes=");
	for (mni = g2.nodes.begin (); mni != g2.nodes.end (); mni++)
		DEBUG ("%d,", mni->first);
#endif

	// For one-to-one node matching of G1 and G2, the cardinality of S1 and
	// S2 should be same; if the cardinality is not the same, we should not
	// mark S1 and S2 as equivalent.
	if (s1.size () != s2.size ())
	{
		DEBUG ("\ns1.size != s2.size ()");
		return false;
	}

	map<state_index, state_index, state_order>::iterator pi;
	pi = equiv_state_pairs.find (s1); 
	// (S1,S2) is in EQUIV_STATE_PAIRS
	if (pi != equiv_state_pairs.end () && pi->second == s2)
		return true;
	// For one-to-one node matching of G1 and G2, only two states can be
	// equivalent; three states cannot be equivalent. Therefore, if S1 or
	// S2 are already matched with S3, then to find a node-to-node
	// matching, we should not mark three states, viz. S1,S2,S3 as equivalent.
	// (S1,*) is in EQUIV_STATE_PAIRS
	if (pi != equiv_state_pairs.end ())
	{
		DEBUG ("\n(S1,*) is in equiv_state_pairs");
		return false;
	}
	pi = equiv_state_pairs.find (s2);
	// (*,S2) is in EQUIV_STATE_PAIRS
	if (pi != equiv_state_pairs.end ())
	{
		DEBUG ("\n(S2,*) is in equiv_state_pairs");
		return false;
	}

	equiv_state_pairs[s1] = s2;
	equiv_state_pairs[s2] = s1;

	// Prepare out-edges of S1 and S2. In this HK algorithm, the out-edges
	// are deterministic, i.e. there is only one DFA state for every label.
	map<label, state_index> s1_out_edges;
	map<label, state_index> s2_out_edges;
	// Pass NULL for variable_data, since we do not want to ignore
	// temporary variables in this function.
	g1.stack->get_out_dfa_edges (g1.stack->get_node_id (), s1, s1_out_edges, g1.nodes);
	g2.stack->get_out_dfa_edges (g2.stack->get_node_id (), s2, s2_out_edges, g2.nodes);

	if (s1_out_edges.size () != s2_out_edges.size ())
	{
		DEBUG ("\ns1_out_edges.size () != s2_out_edges.size ()");
		return false;
	}

	// Recursively get equivalent states of the successor DFA nodes
	map<label, state_index>::iterator s1_ei;
	map<label, state_index>::iterator s2_ei;
	for (s1_ei = s1_out_edges.begin (), s2_ei = s2_out_edges.begin ();
		s1_ei != s1_out_edges.end ();
		s1_ei++, s2_ei++)
	{
		label l1 = s1_ei->first;
		label l2 = s2_ei->first;
		if (l1 != l2)
		{
			DEBUG ("\nl1 != l2");
			return false;
		}
		state_index s1_out = s1_ei->second;
		state_index s2_out = s2_ei->second;

		if (!get_equivalent_states (s1_out, s2_out, g1, g2, equiv_state_pairs))
			return false;
	}	

	// FIXME: Right now we are inserting pairs of states in
	// EQUIV_STATE_PAIRS in the ascending order of cardinality itself.
	// However, would it be faster if we insert first without imposing any
	// order, then create a copy of EQUIV_STATE_PAIRS which has the pairs
	// sorted by cardinality.

	return true;
}

/**
 * This function retrieves (S1,S2) state pair from EQUIV_STATE_PAIRS.
 * Then it maps every node N1 in S1 with a node N2 in S2 and stores the pairs
 * (N1,N2) in EQUIV_NODE_PAIRS.
 */

bool non_deterministic_simple_graph::
get_equivalent_nodes (map<state_index, state_index, state_order> & equiv_state_pairs, 
	map<node_index, node_index> & equiv_node_pairs)
{
	DEBUG ("\nget_equivalent_nodes ()");

	map<state_index, state_index, state_order>::iterator spi;
	for (spi = equiv_state_pairs.begin (); spi != equiv_state_pairs.end (); spi++)
	{
		state_index s1 = spi->first;
		state_index s2 = spi->second;
		if (s1.size () != s2.size ())
		{
			RESULT ("\nError: HK algorithm should have ensured equal cardinality of states");
			return false;
		}
		if (!map_equivalent_nodes (s1, s2, equiv_state_pairs, equiv_node_pairs))
			return false;
	}
	return true;
}

bool non_deterministic_simple_graph::
map_equivalent_nodes (state_index & s1, state_index & s2, 
	map<state_index, state_index, state_order> & equiv_state_pairs, 
	map<node_index, node_index> & equiv_node_pairs)
{
	DEBUG ("\nmap_equivalent_nodes ()");

#if DEBUG_CONTAINER
	state_index::iterator si;
	DEBUG ("\ns1=");
	for (si = s1.begin (); si != s1.end (); si++)
		DEBUG ("%d,", *si);
	DEBUG ("\ns2=");
	for (si = s2.begin (); si != s2.end (); si++)
	DEBUG ("%d,", *si);

	DEBUG ("\nequiv_state_pairs=");
	map<state_index, state_index, state_order>::iterator spi;
	for (spi = equiv_state_pairs.begin (); spi != equiv_state_pairs.end (); spi++)
	{
		DEBUG ("(");
		DEBUG ("{");
		state_index s = spi->first;
		for (si = s.begin (); si != s.end (); si++)
			DEBUG ("%d,", *si);
		DEBUG ("},");
		DEBUG ("{");
		s = spi->second;
		for (si = s.begin (); si != s.end (); si++)
			DEBUG ("%d,", *si);
		DEBUG ("}");
		DEBUG (")");

	}
	DEBUG ("\nequiv_node_pairs=");
	map<node_index, node_index>::iterator npi;
	for (npi = equiv_node_pairs.begin (); npi != equiv_node_pairs.end (); npi++)
	{
		DEBUG ("(%d,%d), ", npi->first, npi->second);
	}
#endif

	state_index::iterator n1i;
	for (n1i = s1.begin (); n1i != s1.end (); n1i++)
	{
		node_index n1 = *n1i;
		if (equiv_node_pairs.find (n1) != equiv_node_pairs.end ())
		// If N1 has already been mapped with say N2 in
		// EQUIV_NODE_PAIRS, then surely N2 would be present in S2,
		// because (N1,N2) is added to EQUIV_NODE_PAIRS only after
		// checking that all pairs in EQUIV_STATE_PAIRS also satisfy
		// this.
			continue;

		bool found = false;
		state_index::iterator n2i;
		for (n2i = s2.begin (); n2i != s2.end (); n2i++)
		{
			node_index n2 = *n2i;
			if (equiv_node_pairs.find (n2) != equiv_node_pairs.end ())
				continue;
			// FIXME: pass INDEX to IS_IN_LANGUAGE_SAME() so that
			// it checks (N1,N2) only in pairs of EQUIV_STATE_PAIRS
			// after INDEX, or pass to IS_IN_LANGUAGE_SAME()
			// EQUIV_STATE_PAIRS after INDEX.
			if (stack->is_in_language_same (n1, n2, equiv_state_pairs))
			{
				DEBUG ("\nInserted pair (%d,%d),(%d,%d)", n1, n2, n2, n1);
				equiv_node_pairs[n1] = n2;
				equiv_node_pairs[n2] = n1;
				found = true;
				break;
			}
		}
		if (found == false)
			return false;
	}
	return true;
}


#if 0
/**
 * The functions commented out below use permutation to map nodes in (S1,S2) of
 * EQUIV_STATE_PAIRS.
 */

bool non_deterministic_simple_graph::
get_equivalent_nodes (int index, 
	map<state_index, state_index, state_order> & equiv_state_pairs, 
	map<node_index, pair<node_index, int> > & equiv_node_pairs)
{
	DEBUG ("\nget_equivalent_nodes (index=%d)", index);

	DEBUG ("\nindex=%d, equiv_state_pairs.size=%d", index, equiv_state_pairs.size ());
	// INDEX starts from 0.
	if (index >= equiv_state_pairs.size ())
		return true;

	map<state_index, state_index, state_order>::iterator spi = equiv_state_pairs.begin ();
	std::advance (spi, index);
	state_index s1_unordered = spi->first;
	state_index s2_unordered = spi->second;

#if DEBUG_CONTAINER
	state_index::iterator si;
	DEBUG ("\ns1_unordered=");
	for (si = s1_unordered.begin (); si != s1_unordered.end (); si++)
		DEBUG ("%d,", *si);
	DEBUG ("\ns2_unordered=");
	for (si = s2_unordered.begin (); si != s2_unordered.end (); si++)
		DEBUG ("%d,", *si);
#endif

	// S1 should be an ordered list because we need to permute the order of
	// the elements in S1. Also, operator[] should be applicable on S1 and
	// S2 so that nodes from S1 and S2 can be picked up from the
	// corresponding positions.
	vector<node_index> s1 (s1_unordered.begin (), s1_unordered.end ());
	vector<node_index> s2 (s2_unordered.begin (), s2_unordered.end ());
#if DEBUG_CONTAINER
	vector<node_index>::iterator svi;
	DEBUG ("\ns1=");
	for (svi = s1.begin (); svi != s1.end (); svi++)
		DEBUG ("%d,", *svi);
	DEBUG ("\ns2=");
	for (svi = s2.begin (); svi != s2.end (); svi++)
		DEBUG ("%d,", *svi);
#endif

	// This function recursively calls GET_EQUIVALENT_NODES ().
	return permute_and_map_equivalent_nodes (s1, 0, s2, equiv_state_pairs, index, equiv_node_pairs);
}

/** 
 * Permutation algorithm: For each element from left to right, we generate all
 * the permutations of the remaining elements. We do this until we get to the
 * last element at which point there is only one possible order. So, given a
 * list: [1,2,3,4]. We generate all permutations that start with 1, then all
 * the permutations that start with 2, then with 3 and 4. This effectively
 * reduces the problem from one of finding permutations of a list of four
 * elements to a list of three elements, and so on.
 */
	
bool non_deterministic_simple_graph::
permute_and_map_equivalent_nodes (vector<node_index> & s1, int i,
	vector<node_index> & s2, 
	map<state_index, state_index, state_order> & equiv_state_pairs, 
	int index,
	map<node_index, pair<node_index, int> > & equiv_node_pairs)
{
	DEBUG ("\npermute_and_map_equivalent_nodes ()");

	if (i == s1.size ())
	{
#if DEBUG_CONTAINER
		vector<node_index>::iterator si;
		DEBUG ("\npermuted s1=<");
		for (si = s1.begin (); si != s1.end (); si++)
			DEBUG ("%d,",*si);
		DEBUG (">");
		DEBUG ("\ns2=<");
		for (si = s2.begin (); si != s2.end (); si++)
			DEBUG ("%d,",*si);
		DEBUG (">");
		DEBUG ("\nequiv_state_pairs=");
		map<state_index, state_index, state_order>::iterator spi;
		for (spi = equiv_state_pairs.begin (); spi != equiv_state_pairs.end (); spi++)
		{
			state_index::iterator si;
			DEBUG ("(");
			DEBUG ("{");
			state_index s = spi->first;
			for (si = s.begin (); si != s.end (); si++)
				DEBUG ("%d,", *si);
			DEBUG ("},");
			DEBUG ("{");
			s = spi->second;
			for (si = s.begin (); si != s.end (); si++)
				DEBUG ("%d,", *si);
			DEBUG ("}");
			DEBUG (")");

		}
		DEBUG ("\nequiv_node_pairs=");
		map<node_index, pair<node_index, int> >::iterator npi;
		for (npi = equiv_node_pairs.begin (); npi != equiv_node_pairs.end (); npi++)
		{
			DEBUG ("%d:(%d,%d), ", npi->second.second, npi->first, npi->second.first);
		}
#endif
		if (map_equivalent_nodes (s1, s2, index, equiv_node_pairs) &&
			get_equivalent_nodes (index+1, equiv_state_pairs, equiv_node_pairs))
				return true;

		// If based on node mapping done at INDEX, the >INDEX mappings
		// cannot be satisfied, we need to try out a different
		// permutation of mapping at INDEX.  It is important to undo
		// the mapping created by only this INDEX. Therefore, we need
		// to keep a track of as to which mapping was created in which
		// index.
		unmap_nodes (index, equiv_node_pairs);
	}
	else
	{
		for (int j = i; j < s1.size (); j++)
		{
			swap_nodes (s1, i, j);
			if (permute_and_map_equivalent_nodes (s1, i+1, s2, equiv_state_pairs, index, equiv_node_pairs))
				return true;
			swap_nodes (s1, i, j);
		}
	
	}
	return false;
}

bool non_deterministic_simple_graph::
map_equivalent_nodes (vector<node_index> & s1,
	vector<node_index> & s2, 
	int index,
	map<node_index, pair<node_index, int> > & equiv_node_pairs)
{
	DEBUG ("\nmap_equivalent_nodes ()");

	if (s1.size () != s2.size ())
	{
		RESULT ("\nError: Equivalent states S1 and S2 have different sizes.");
		return false;
	}
	for (int i = 0; i < s1.size (); i++)
	{
		node_index n1 = s1[i];
		node_index n2 = s2[i];
		if (equiv_node_pairs.find (n1) != equiv_node_pairs.end ())
		{
			pair<node_index, int> p = equiv_node_pairs[n1];
			// If ((N1,N2,*) is in EQUIV_NODE_PAIRS)
			if (p.first == n2)
			{
				DEBUG ("\nFound pair (%d,%d)", n1, n2);
				continue;
			}
			// If ((N1,*,*) is in EQUIV_NODE_PAIRS)
			DEBUG ("\nFound n1 %d, but not n2 %d", n1, n2);
			return false;
		}
		// If ((N2,*,*) is in EQUIV_NODE_PAIRS)
		if (equiv_node_pairs.find (n2) != equiv_node_pairs.end ())
		{
			DEBUG ("\nFound n2 %d, but not n1 %d", n2, n1);
			return false;
		}

		DEBUG ("\nInserted pair (%d,%d),(%d,%d)", n1, n2, n2, n1);
		equiv_node_pairs[n1] = make_pair (n2, index);
		equiv_node_pairs[n2] = make_pair (n1, index);
	}
	return true;
}

void non_deterministic_simple_graph::
unmap_nodes (int index,
	map<node_index, pair<node_index, int> > & equiv_node_pairs)
{
	DEBUG ("\nunmap_nodes (index=%d)", index);

	map<node_index, pair<node_index, int> >::iterator npi;
	for (npi = equiv_node_pairs.begin (); npi != equiv_node_pairs.end (); )
	{
		pair<node_index, int> p = npi->second;
		if (p.second != index)
		{
			npi++;
			continue;
		}
		DEBUG ("\nErasing (%d,%d)", npi->first, p.first);
		equiv_node_pairs.erase (npi++);
	}	
}

void non_deterministic_simple_graph::
swap_nodes (vector<node_index> & s, int i, int j)
{
	if (i == j)
		return;

	node_index n = s[i];
	s[i] = s[j];
	s[j] = n;
}
#endif

bool non_deterministic_simple_graph::
are_improper_nodes_okay ()
{
	set<node_index> improper_nodes;
	get_addressof_nodes (readonly_id, improper_nodes);
	get_addressof_nodes (stack_deref, improper_nodes);
	get_addressof_nodes (null_id, improper_nodes);
	get_addressof_nodes (undef_id, improper_nodes);

	set<node_index>::iterator ni;
	for (ni = improper_nodes.begin (); ni != improper_nodes.end (); ni++)
	{
		non_deterministic_simple_node * n = nodes[*ni];
		if (n->get_out_edge_list ().size ())
			RESULT ("\nError: Improper node %d has out edges", *ni);
	}	
}

/**
 * This function checks if IS_IN_VALUE_SAME () has rightly declared THIS and G
 * graphs as equivalent. For this it checks the theorem of HK algorithm for all
 * the pairs of nodes of EQUIV_NODE_PAIRS. Additionally, it checks if these
 * EQUIV_NODE_PAIRS are a superset of the equiv_node_pairs derived by
 * IS_INOUT_VALUE_SAME ().
 */ 

bool non_deterministic_simple_graph::
is_in_comparison_okay (non_deterministic_simple_graph & g, map<node_index, node_index> & equiv_node_pairs, map<state_index, state_index, state_order> & equiv_state_pairs)
{
	DEBUG ("\nis_in_comparison_okay ()");

	if (!is_every_node_paired (equiv_node_pairs))
		return false;
	if (!g.is_every_node_paired (equiv_node_pairs))
		return false;

	if (!equiv_state_pairs.size ())
	{
		RESULT ("\nError: equiv_state_pairs is empty");
		return false;
	}

	// Check that for every pair (n1,n2) in EQUIV_NODE_PAIRS taken as the
	// only non-final nodes of the respective graph, HK algorithm's theorem
	// is satisfied for the EQUIV_STATE_PAIRS. The theorem is that all the
	// sets of equivalent states should contain either all final or all
	// non-final states.
	map<node_index, node_index>::iterator npi;
	for (npi = equiv_node_pairs.begin (); npi != equiv_node_pairs.end (); npi++)
	{
		node_index n1 = npi->first;
		node_index n2 = npi->second;
		if (!stack->is_in_language_same (n1, n2, equiv_state_pairs))
		{
			RESULT ("\nError: equiv_node_pairs (%d,%d) are not equivalent", n1, n2);
			return false;
		}
	}

	// Note that IS_IN_VALUE_SAME (i.e. EQUIV_NODE_PAIRS derived from
	// EQUIV_STATE_PAIRS) is not equivalent to IS_INOUT_VALUE_SAME (i.e.
	// EQUIV_NODE_PAIRS derived from DFS with IS_IN_LANGUAGE_SAME). The
	// former imposes a weaker condition for the graph values to be same.
	// Therefore, we cannot use the latter to completely check if the
	// former is okay. In fact DFS with IS_IN_LANGUAGE_SAME is equivalent
	// to DFS with IS_IN_GRAPH_ISOMORPHIC. For example, 
	// G1 = (1,f,2),(1,f,3),(1,g,3),(2,f,4),(3,f,4)
	// G2 = (5,f,6),(5,f,7),(5,g,7),(7,f,8)
	// IS_IN_VALUE_SAME (G1,G2) is true. 
	// IS_INOUT_VALUE_SAME with IS_IN_LANGUAGE_SAME: (G1,G2) is false. 
	// IS_INOUT_VALUE_SAME with IS_IN_GRAPH_ISOMORPHIC (G1,G2) is false.
	
	// Check if EQUIV_NODE_PAIRS computed by IS_INOUT_VALUE_SAME (using
	// in_language and in_isomorphism) are a subset of the EQUIV_NODES_PAIRS
	// computed by IS_IN_VALUE_SAME.
	if (!is_in_comparison_weaker (g, equiv_node_pairs, equiv_state_pairs, false))
		return false;
	if (!is_in_comparison_weaker (g, equiv_node_pairs, equiv_state_pairs, true))
		return false;

	RESULT ("\nis_in_comparison_okay (%d, %d) \\m/", 
		stack->get_node_id (), g.stack->get_node_id ());
	return true;
}

/**
 * This function checks if equiv_node_pairs computed by IS_INOUT_VALUE_SAME ()
 * are a subset of EQUIV_NODE_PAIRS of IS_IN_VALUE_SAME ().
 */

bool non_deterministic_simple_graph::
is_in_comparison_weaker (non_deterministic_simple_graph & g, map<node_index, node_index> & equiv_node_pairs, map<state_index, state_index, state_order> & equiv_state_pairs, bool reverse_node_property)
{
	DEBUG ("\nis_in_comparison_weaker (node_property = %d, reverse_node_property = %d",
		node_property, reverse_node_property);
	map<node_index, node_index> new_equiv_node_pairs;
	bool new_is_same = stack->depth_first_comparison 
		(*g.stack, nodes, g.nodes, new_equiv_node_pairs, equiv_state_pairs, reverse_node_property);

#if DEBUG_CONTAINER
	map<node_index, node_index>::iterator npi;
	DEBUG ("\nnew_equiv_node_pairs=");
	for (npi = new_equiv_node_pairs.begin (); npi != new_equiv_node_pairs.end (); npi++)
		DEBUG ("(%d,%d),", npi->first, npi->second);

	if (!new_is_same)
	{
		DEBUG ("\nTHIS=");
		print_value (NULL);
		DEBUG ("\ng=");
		g.print_value (NULL);
		DEBUG ("\nDepth-first-comparison returns false. "); 
		DEBUG ("This is not an error because is_in_value_same() is a weaker comparison");
	}

	if (equiv_node_pairs.size () != new_equiv_node_pairs.size ())
	{
		DEBUG ("\nequiv_node_pairs size is different. ");
		DEBUG ("This is not an error because is_in_value_same() is a weaker comparison.");
	}
#endif
	
	// If (n1,n2) is in equiv_node_pairs of IS_INOUT_VALUE_SAME (), then it
	// should surely be in EQUIV_NODE_PAIRS. I am not sure. For the case
	// where IS_INOUT_VALUE_SAME () fails, it also does an undo of the
	// equiv_node_pairs wrongly saved. But does it do for all?
	map<node_index, node_index>::iterator new_pi;
	for (new_pi = new_equiv_node_pairs.begin (); new_pi != new_equiv_node_pairs.end (); new_pi++)
	{
		map<node_index, node_index>::iterator pi;
		pi = equiv_node_pairs.find (new_pi->first);
		if (pi == equiv_node_pairs.end ())
		{
			RESULT ("\nError: equiv_nodes_pairs first %d not found", new_pi->first);
			return false;
		}
		if (pi->second != new_pi->second)
		{
			RESULT ("\nError: equiv_nodes_pairs seconds %d and %d do not match", 
				pi->second, new_pi->second);
			return false;
		}
	}

	if (equiv_node_pairs.size () == new_equiv_node_pairs.size ())
		RESULT ("\nis_in_comparison_weaker (%d, %d) --- exact match \\m/", 
			stack->get_node_id (), g.stack->get_node_id ());
	else
		RESULT ("\nis_in_comparison_weaker (%d, %d) --- weaker \\m/", 
			stack->get_node_id (), g.stack->get_node_id ());

	return true;
}

/**
 * This function checks if IS_INOUT_VALUE_SAME () has rightly declared THIS and
 * G graphs as equivalent. For this it checks if every node of THIS graph
 * matches EQUIV_NODE_PAIRS[THIS] node in G graph (i.e. with the same in- and
 * out-edges). Note that this function does not check the same for every node
 * of G graph. Therefore, this function should be called again with G as THIS
 * graph.
 */

bool non_deterministic_simple_graph::
is_inout_comparison_okay (non_deterministic_simple_graph & g, map<node_index, node_index> & equiv_node_pairs)
{
	DEBUG ("\nis_inout_comparison_okay () --- in/out-edges");

	if (!is_every_node_paired (equiv_node_pairs))
		return false;

	// Check that the in- and out-edges of every node of THIS graph map to
	// the in- and out-edges of the matching node of G graph
	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		node_index this_node = ni->first;
		node_index matching_node = equiv_node_pairs[this_node];
		non_deterministic_simple_node * this_n = ni->second;
		non_deterministic_simple_node * g_n = g.nodes[matching_node];
		map<label, set<node_index> > this_out_edges = this_n->get_out_edge_list ();
		map<label, set<node_index> > g_out_edges = g_n->get_out_edge_list ();
		if (!this_n->is_edge_comparison_okay (matching_node, equiv_node_pairs, this_out_edges, g_out_edges))
		{
			DEBUG ("\nOut-edges of g1.%d and g2.%d are not same", this_node, matching_node);
			return false;
		}
		DEBUG ("\nOut-edges of g1.%d and g2.%d are same", this_node, matching_node);
		map<label, set<node_index> > this_in_edges = this_n->get_in_edge_list ();
		map<label, set<node_index> > g_in_edges = g_n->get_in_edge_list ();
		if (!this_n->is_edge_comparison_okay (matching_node, equiv_node_pairs, this_in_edges, g_in_edges))
		{
			DEBUG ("\nIn-edges of g1.%d and g2.%d are same", this_node, matching_node);
			return false;
		}
		DEBUG ("\nIn-edges of g1.%d and g2.%d are same", this_node, matching_node);
	}

	RESULT ("\nis_inout_comparison_okay (%d, %d) --- in/out-edges \\m/", 
		stack->get_node_id (), g.stack->get_node_id ());
	return true;
}

/**
 * This function checks if IS_INOUT_VALUE_SAME () has rightly declared THIS and
 * G graphs as equivalent. For this it re-runs IS_INOUT_VALUE_SAME () on
 * another node property and then compares its equiv_node_pairs with
 * EQUIV_NODE_PAIRS.
 */

bool non_deterministic_simple_graph::
is_inout_comparison_okay (non_deterministic_simple_graph & g, map<node_index, node_index> & equiv_node_pairs, map<state_index, state_index, state_order> & equiv_state_pairs)
{
	DEBUG ("\nis_inout_comparison_okay ()");

	if (!is_every_node_paired (equiv_node_pairs))
		return false;
	if (!g.is_every_node_paired (equiv_node_pairs))
		return false;

	map<node_index, node_index> new_equiv_node_pairs;
	// Re-run IS_INOUT_VALUE_SAME () with REVERSE_NODE_PROPERTY=true, so
	// that the algorithm is run with a different node property, and we can
	// compare the results. Note that IS_INOUT_VALUE_SAME () is same for
	// both in_language and in_isomorphism.

	// EQUIV_STATE_PAIRS has not been calculated if NODE_PROPERTY was
	// IN_ISOMORPHISM. But anyways recompute if it is empty.
	if (!equiv_state_pairs.size () &&
		!get_equivalent_states (g, equiv_state_pairs))
	{
		RESULT ("\nError: equiv_state_pairs cannot be computed");
		return false;
	}

	bool new_is_same = stack->depth_first_comparison 
		(*g.stack, nodes, g.nodes, new_equiv_node_pairs, equiv_state_pairs, true);
	if (!new_is_same)
	{
		DEBUG ("\nTHIS=");
		print_value (NULL);
		DEBUG ("\ng=");
		g.print_value (NULL);
		RESULT ("\nError: Depth-first-comparison returns false."); 
		return false;
	}

	if (equiv_node_pairs.size () != new_equiv_node_pairs.size ())
	{
		RESULT ("\nError: equiv_node_pairs size is different");
		return false;
	}
	
	map<node_index, node_index>::iterator p1i;
	map<node_index, node_index>::iterator p2i;
	for (p1i = equiv_node_pairs.begin (), p2i = new_equiv_node_pairs.begin (); 
		p1i != equiv_node_pairs.end ();
		p1i++, p2i++)
	{
		if (p1i->first != p2i->first)
		{
			RESULT ("\nError: equiv_nodes_pairs firsts do not match");
			return false;
		}
		if (p1i->second != p2i->second)
		{
			RESULT ("\nError: equiv_nodes_pairs seconds do not match");
			return false;
		}
	}

	RESULT ("\nis_inout_comparison_okay (%d, %d) \\m/", 
		stack->get_node_id (), g.stack->get_node_id ());
	return true;
}

/**
 * This function checks if every node of THIS graph is in EQUIV_NODE_PAIRS.
 */

bool non_deterministic_simple_graph::
is_every_node_paired (map<node_index, node_index> & equiv_node_pairs)
{
	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		node_index this_node = ni->first;
		if (equiv_node_pairs.find (this_node) == equiv_node_pairs.end ())
		{
			RESULT ("\nError: Node %d is not matched", this_node);
			return false;
		}
	}
	DEBUG ("\nEvery node of this graph is paired");
	return true;
}

/**
 * Checks if there exists a node which is indistinguishable to node NODEI, i.e.
 * it has wrongly been left unmerged with NODEI.
 */

bool non_deterministic_simple_graph::
is_node_unmerged (non_deterministic_simple_node & nodei)
{
	node_index nodei_id = nodei.get_node_id ();
	map<node_index, non_deterministic_simple_node *>::iterator nj;
	nj = nodes.find (nodei_id);
	nj++;
	for (; nj != nodes.end (); nj++)
	{
		non_deterministic_simple_node * nodej = nj->second;
		// Finding a matching property --- IS_IN_GRAPH_ISOMORPHIC()
		// (automorphism in this case) or IS_IN_LANGUAGE_SAME().

		// Here we do not change merging criterion whether or not it is
		// a loop merge. Therefore, FALSE.
		if (stack->is_node_property_same (nodei, *nodej, nodes, false))
		{
			RESULT ("\nError: Graph has not merged indistinguishable nodes %d and %d", 
				nodei.get_node_id (), nj->first);

			return true;
		}
	}
	return false;
}

bool non_deterministic_simple_graph::
is_graph_okay ()
{
	node_index stack_id = stack->get_node_id ();
	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		non_deterministic_simple_node * nodei = ni->second;

		DEBUG ("\nChecking node %d", ni->first);
		if (is_node_unmerged (*nodei))
			return false;

		if (nodei->is_node_nameless (stack_id))
		{
			RESULT ("\nError: Node %d is nameless", ni->first);
			return false;
		}

		if (nodei->is_node_useless (stack_id))
		{
			RESULT ("\nError: Node %d saves no information", ni->first);
			return false;
		}
	}

	DEBUG ("\nGraph is okay \\m/");
	return true;
}

/**
 * This function returns the all the access paths starting from node NODE_ID.
 */

// FIXME: Convert list<> to vector<>. With INT as element, vectors are
// faster since they gain locality benefits in cache.
void non_deterministic_simple_graph::
get_access_paths (node_index node_id, list<int> in_path, set<list<int> > & populated_paths, set<node_index> & gray_nodes, set<node_index> & black_nodes)
{
	DEBUG ("\nget_access_paths (%d, ...)", node_id);

	// Gray denotes that the node has been visited once and a revisit of a
	// gray node means that it is a cycle.
	if (gray_nodes.find (node_id) != gray_nodes.end ())
	{
		DEBUG ("\n%d is gray", node_id);
		in_path.push_back (-1);
		populated_paths.insert (in_path);
		return;
	}
	// Black denotes that the node has been visited and all its successors
	// have also been visited. A revisit of a black node means that it is a
	// duplicated path.
	if (black_nodes.find (node_id) != black_nodes.end ())
	{
		DEBUG ("\nRemoving %d from black", node_id);
		black_nodes.erase (node_id);
	}

	DEBUG ("\nMaking %d gray", node_id);
	gray_nodes.insert(node_id);

	non_deterministic_simple_node * this_n = nodes[node_id];
	map<label, set<node_index> > out_edges = this_n->get_out_edge_list ();
	if (!out_edges.size ())
		populated_paths.insert (in_path);

	map<label, set<node_index> >::iterator ei;
	for (ei = out_edges.begin (); ei != out_edges.end (); ei++)
	{
		label l = ei->first;
		set<node_index> out_nodes = ei->second;
		set<node_index>::iterator ni;
		for (ni = out_nodes.begin (); ni != out_nodes.end (); ni++)
		{
			list<int> path_out_node = in_path;
			path_out_node.push_back (l);
#if DEBUG_CONTAINER
			DEBUG ("\nInserted label %d: ", l);
			list<int>::iterator li;
			for (li = path_out_node.begin (); li != path_out_node.end (); li++)
				DEBUG ("%d.", *li);
#endif
			get_access_paths (*ni, path_out_node, populated_paths, gray_nodes, black_nodes);
#if DEBUG_CONTAINER
			DEBUG ("\nPopulated paths:");
			set<list<int> >::iterator pi;
			for (pi = populated_paths.begin (); pi != populated_paths.end (); pi++)
			{
				DEBUG ("\n");
				list<int> p = *pi;
				list<int>::iterator li;
				for (li = p.begin (); li != p.end (); li++)
					DEBUG ("%d.", *li);
			}
#endif
		}
	}
	// Marking node as black since all its successors have been visited.
	DEBUG ("\nTurning %d from gray to black", node_id);
	gray_nodes.erase (node_id);
	black_nodes.insert (node_id);
}

/**
 * This function finds the access paths that are reaching i.e. are aliased to
 * node NODE_ID.
 */

#define CYCLIC_ALIASES 1

void non_deterministic_simple_graph::
get_node_aliases (node_index node_id, list<int> out_path, set<list<int> > & populated_paths, set<node_index> & gray_nodes, set<node_index> & black_nodes)
{
	//DEBUG ("\nget_aliased_access_paths (%d, ...)", node_id);

	// Gray denotes that the node has been visited once and a revisit of a
	// gray node means that it is a cycle.
	if (gray_nodes.find (node_id) != gray_nodes.end ())
	{
		//DEBUG ("\n%d is gray", node_id);
		out_path.push_front (-1);
#if CYCLIC_ALIASES
		populated_paths.insert (out_path);
#endif
		return;
	}
	// Black denotes that the node has been visited and all its predecessors
	// have also been visited. A revisit of a black node means that it is a
	// duplicated path.
	if (black_nodes.find (node_id) != black_nodes.end ())
	{
		//DEBUG ("\nRemoving %d from black", node_id);
		black_nodes.erase (node_id);
	}

	//DEBUG ("\nMaking %d gray", node_id);
	gray_nodes.insert(node_id);

	non_deterministic_simple_node * this_n = nodes[node_id];
	map<label, set<node_index> > in_edges = this_n->get_in_edge_list ();
	if (!in_edges.size ())
		populated_paths.insert (out_path);

	map<label, set<node_index> >::iterator ei;
	for (ei = in_edges.begin (); ei != in_edges.end (); ei++)
	{
		label l = ei->first;
		set<node_index> in_nodes = ei->second;

		set<node_index>::iterator ni;
		for (ni = in_nodes.begin (); ni != in_nodes.end (); ni++)
		{
			list<int> path_in_node = out_path;

			// Do not consider OUT_PATH if L is a temporary
			// variable and NI is a root node.
			if (*ni == stack->get_node_id ())
			{
				csvarinfo_t variable = VEC_index (csvarinfo_t, program.variable_data, l);
				//if (variable && variable->decl && DECL_ARTIFICIAL(variable->decl))
				//	return;
			}
			path_in_node.push_front (l);

#if DEBUG_CONTAINER
			//DEBUG ("\nInserted label %d: ", l);
			list<int>::iterator li;
			for (li = path_in_node.begin (); li != path_in_node.end (); li++)
				;//DEBUG ("%d.", *li);
#endif
			get_node_aliases (*ni, path_in_node, populated_paths, gray_nodes, black_nodes);
#if DEBUG_CONTAINER
			//DEBUG ("\nPopulated paths:");
			set<list<int> >::iterator pi;
			for (pi = populated_paths.begin (); pi != populated_paths.end (); pi++)
			{
				list<int> p = *pi;
				list<int>::iterator li;
				for (li = p.begin (); li != p.end (); li++)
					;//DEBUG ("%d.", *li);
				//DEBUG (",");
			}
#endif
		}
	}
	// Marking node as black since all its predecessors have been visited.
	//DEBUG ("\nTurning %d from gray to black", node_id);
	gray_nodes.erase (node_id);
	black_nodes.insert (node_id);
}

/**
 * This function populates ACCESS_PATHS_MAP which is a map from each access
 * path in the graph to a set of node ids to which the access path reaches.
 */

void non_deterministic_simple_graph::
get_access_paths (map<list<int>, set<node_index> > & access_paths_map)
{
	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		RESULT ("\nNode %d: ", ni->first);
		list<int> out_path;
		set<list<int> > aliased_paths;
		set<node_index> gray_nodes;
		set<node_index> black_nodes;
		get_node_aliases (ni->first, out_path, aliased_paths, gray_nodes, black_nodes);
		set<list<int> >::iterator pi;
		for (pi = aliased_paths.begin (); pi != aliased_paths.end (); pi++)
		{
			list<int> path = *pi;
			access_paths_map[path].insert (ni->first);
		}
	}

//#if DEBUG_CONTAINER
	map<list<int>, set<node_index> >::iterator ami;
	for (ami = access_paths_map.begin (); ami != access_paths_map.end (); ami++)
	{
		RESULT ("\n");
		print_access_path (ami->first);
		RESULT (" == ");
		set<node_index>::iterator si;
		set<node_index> node_set = ami->second;
		for (si = node_set.begin (); si != node_set.end (); si++)
			RESULT ("%d,", *si);
	}
//#endif
}

/**
 * This function returns a compact representation of THIS graph. In a compact
 * representation every node is uniquely named by the stack variable name or
 * allocation site. Note that this merging of graphs produced by our analysis
 * does not produce results equivalent to conventional analysis; in order to
 * produce conventional analysis results we need to change IS_NODE_PROPERTY,
 * which would keep merging nodes with same names. For example,if {y=&x;x=&a;}
 * else{z=&x;x=&b;}w=*y; The last statement will make 'w' point to 'a' in our
 * analysis. A call to GET_CONVENTIONAL_GRAPH will also precisely say that w
 * points to only 'a'. However, conventional analysis will make 'w' point to
 * 'b' also.
 */

non_deterministic_simple_graph * non_deterministic_simple_graph::
get_compact_graph ()
{
	non_deterministic_simple_graph * compact_g = new non_deterministic_simple_graph;
	// Here we do not change merging criterion whether or not it is a loop
	// merge. Therefore, FALSE.
	compact_g->copy_value (*this, false);

	// Make the out-edges of only the root node deterministic. This will
	// merge nodes with the same name.
	compact_g->stack->make_edge_deterministic (compact_g->nodes, compact_g->stack->get_node_id ());
	compact_g->clean ();

	return compact_g;
}

bool non_deterministic_simple_graph::
is_reachable (label l1, label l2)
{
	node_index stack_id = stack->get_node_id ();
	set<node_index> s1;
	stack->get_destination_nodes (l1, stack_id, s1);
	set<node_index> s2;
	stack->get_destination_nodes (l2, stack_id, s2);

	// Get nodes reachable from L1 and L2
	set<node_index>::iterator ni;
	set<node_index> l1_reachable_nodes;
	for (ni = s1.begin (); ni != s1.end (); ni++)
	{
		non_deterministic_simple_node * n1 = nodes[*ni];
		n1->get_reachable_nodes (stack->get_node_id (), nodes, l1_reachable_nodes);
	}
	set<node_index> l2_reachable_nodes;
	for (ni = s2.begin (); ni != s2.end (); ni++)
	{
		non_deterministic_simple_node * n2 = nodes[*ni];
		n2->get_reachable_nodes (stack->get_node_id (), nodes, l2_reachable_nodes);
	}

	// Find if there is a node reachable both by L1 and L2
	set<node_index>::iterator li1;
	for (li1 = l1_reachable_nodes.begin (); li1 != l1_reachable_nodes.end (); li1++)
	{
		non_deterministic_simple_node * n1 = nodes[*li1];
		if (!stack->is_node_proper (*n1))
			continue;
		if (l2_reachable_nodes.find (*li1) != l2_reachable_nodes.end ())
			return true;
	}
	return false;
}

void non_deterministic_simple_graph::
get_reachable_roots (map<label, set<label> > & reachable_roots, map<label, set<label> > & program_reachable_roots)
{
	csvarinfo_t variable;
	map<label, set<node_index> > out_edges = stack->get_out_edge_list ();
	map<label, set<node_index> >::iterator ei;
	for (ei = out_edges.begin (); ei != out_edges.end (); ei++)
	{
		label l = ei->first;
		if (!program.is_proper_var (l))
			continue;
		variable = VEC_index (csvarinfo_t, program.variable_data, l);
		// if (!variable || !variable->decl)
		// if (variable && variable->decl && DECL_ARTIFICIAL (variable->decl))
		//	continue;
	
		set<node_index> out_nodes = ei->second;
		set<node_index> reachable_nodes;
		set<node_index>::iterator ni;
		for (ni = out_nodes.begin (); ni != out_nodes.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes[*ni];
			n->get_reachable_nodes (stack->get_node_id (), nodes, reachable_nodes);
		}

		set<label> nodes_names;
		get_nodes_names (reachable_nodes, nodes_names);
		reachable_roots[l].insert (nodes_names.begin (), nodes_names.end ());
		program_reachable_roots[l].insert (nodes_names.begin (), nodes_names.end ());
	}
}

void non_deterministic_simple_graph::
print_kill_nodes (set<node_index> & kill_nodes)
{
	if (!kill_nodes.size ())
		return;

	set<label> kill_names;
	get_nodes_names (kill_nodes, kill_names);
	set<label>::iterator vi;
	RESULT ("\nKilling out-edges of: ");
	for (vi = kill_names.begin (); vi != kill_names.end (); vi++)
	{
		csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, *vi);
		RESULT ("%s(%d),", v_info->name, *vi);
	}
}

void non_deterministic_simple_graph::
print_reachable_roots (map<label, set<label> > & reachable_roots)
{
	map<label, set<label> >::iterator r;
	for (r = reachable_roots.begin (); r != reachable_roots.end (); r++)
	{
		label l = r->first;
		csvarinfo_t variable1 = VEC_index (csvarinfo_t, program.variable_data, l);
		RESULT ("\n\t%s(%d) reaches: ", variable1->name, l);
		set<label> s = r->second;
		set<label>::iterator si;
		for (si = s.begin (); si != s.end (); si++)
		{
			csvarinfo_t variable2 = VEC_index (csvarinfo_t, program.variable_data, *si);
			RESULT ("%s(%d),", variable2->name, *si);
		}
	}
}

void non_deterministic_simple_graph::
get_root_aliases (map<label, set<label> > & root_aliases, map<label, set<label> > & program_root_aliases)
{
	csvarinfo_t variable;
	map<label, set<node_index> > out_edges = stack->get_out_edge_list ();
	map<label, set<node_index> >::iterator ei1;
	for (ei1 = out_edges.begin (); ei1 != out_edges.end (); ei1++)
	{
		label l1 = ei1->first;
		if (!program.is_proper_var (l1))
			continue;
		variable = VEC_index (csvarinfo_t, program.variable_data, l1);
		// if (!variable || !variable->decl)
		// if (variable && variable->decl && DECL_ARTIFICIAL (variable->decl))
		//	continue;

		map<label, set<node_index> >::iterator ei2;
		for (ei2 = out_edges.begin (); ei2 != out_edges.end (); ei2++)
		{
			label l2 = ei2->first;
			variable = VEC_index (csvarinfo_t, program.variable_data, l2);
			// if (!variable || !variable->decl)
			// if (variable && variable->decl && DECL_ARTIFICIAL (variable->decl))
			//	continue;

			if (l1 == l2)
				continue;
			if (is_reachable (l1, l2))
			{
				root_aliases[l1].insert (l2);
				program_root_aliases[l1].insert (l2);
			}
		}
	}
}

unsigned int non_deterministic_simple_graph::
print_root_aliases (map<label, set<label> > & root_aliases)
{
	unsigned int count_root_aliases = 0;
	map<label, set<label> >::iterator ri;
	for (ri = root_aliases.begin (); ri != root_aliases.end (); ri++)
	{
		label l1 = ri->first;
		RESULT ("\n\tRoot aliases: ");
		csvarinfo_t variable = VEC_index (csvarinfo_t, program.variable_data, l1);
		RESULT ("%s(%d), ", variable->name, l1);
	
		set<label> s2 = ri->second;
		count_root_aliases += s2.size ();

		set<label>::iterator si;
		for (si = s2.begin (); si != s2.end (); si++)
		{
			label l2 = *si;
			csvarinfo_t variable = VEC_index (csvarinfo_t, program.variable_data, l2);
			RESULT ("%s(%d), ", variable->name, l2);
		}
	}

	RESULT ("\n\tcount_root_aliases=%d", count_root_aliases);
	return count_root_aliases;
}

void non_deterministic_simple_graph::
print_access_path (list<int> path)
{
	list<int>::iterator li;
	for (li = path.begin (); li != path.end (); li++)
	{
		label l = *li;
		if (l == -1)
			// Kleene closure
			RESULT ("*");
		else if (li == path.begin ())
		{
			csvarinfo_t variable = VEC_index (csvarinfo_t, program.variable_data, l);
			RESULT ("%s(%d),", variable->name, l);
		}
		else
			RESULT ("%d,", l);
	}
}


void non_deterministic_simple_graph::
print_access_paths ()
{
	DEBUG ("\nprint_access_paths ()");
	list<int> in_path;
	set<list<int> > access_paths;
	set<node_index> gray_nodes;
	set<node_index> black_nodes;
	get_access_paths (stack->get_node_id (), in_path, access_paths, gray_nodes, black_nodes);
	set<list<int> >::iterator pi;
	for (pi = access_paths.begin (); pi != access_paths.end (); pi++)
	{
		RESULT ("\n");
		print_access_path (*pi);
	}
}

void non_deterministic_simple_graph::
get_aliases (set<set<list<int> > > & set_of_aliases, set<set<list<int> > > & program_aliases)
{
	DEBUG ("\nget_aliases ()");

	// In order to find out all the unique aliases, we keep storing the
	// alias-set of each node in SET_OF_ALIASES.

	map<node_index, non_deterministic_simple_node *>::iterator ni;
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		node_index nid = ni->first;
		non_deterministic_simple_node * n = ni->second;
		if (!stack->is_node_proper (*n))
			continue;
		list<int> out_path;
		set<list<int> > aliased_paths;
		set<node_index> gray_nodes;
		set<node_index> black_nodes;
		get_node_aliases (ni->first, out_path, aliased_paths, gray_nodes, black_nodes);
		// Skip nodes that do not represent any alias paths (these
		// nodes might have been storing temporary variable paths), or
		// nodes that have only the root variable pointing to them.
		if (aliased_paths.size () <= 1)
			continue;

		set_of_aliases.insert (aliased_paths);
		program_aliases.insert (aliased_paths);

#if DEBUG_CONTAINER
		RESULT ("\nNode %d: ", ni->first);
		set<list<int> >::iterator pi;
		for (pi = aliased_paths.begin (); pi != aliased_paths.end (); pi++)
		{
			RESULT ("(");
			print_access_path (*pi);
			RESULT ("),");
		}
#endif
	}
}

void non_deterministic_simple_graph::
print_aliases (set<set<list<int> > > & set_of_aliases)
{
	map<label, int> replicas;

	set<set<list<int> > >::iterator ssi;
	for (ssi = set_of_aliases.begin (); ssi != set_of_aliases.end (); ssi++)
	{
		set<list<int> > aliased_paths = *ssi;
		RESULT ("\n -- ");
		set<list<int> >::iterator pi;
		for (pi = aliased_paths.begin (); pi != aliased_paths.end (); pi++)
		{
			list<int> access_path = *pi;
			RESULT ("(");
			print_access_path (access_path);
			RESULT ("),");

			// If access path is a root variable
			if (access_path.size () == 1)
			{
				label v = *(access_path.begin ());
				if (replicas.find (v) != replicas.end ())
					replicas[v] += 1;
				else
					replicas[v] = 1;
			}
		}
	}

	map<label, int>::iterator r;
	for (r = replicas.begin (); r != replicas.end (); r++)
	{
		label v = r->first;
		int count = r->second;
		if (count <= 1)
			continue;
		csvarinfo_t variable = program.cs_get_varinfo (v);
		if (variable && variable->decl)
			RESULT ("\n\t%s(%d) is used in %d control flow paths", 
				variable->name, v, count);
	}
}

void non_deterministic_simple_graph::
get_nodes_names (set<node_index> & s, set<label> & names)
{
	node_index stack_id = stack->get_node_id ();

	set<node_index>::iterator ni;
	for (ni = s.begin (); ni != s.end (); ni++)
	{
		if (*ni == stack_id)
			continue;
		DEBUG ("\nget_node_name () of %d", *ni);
		non_deterministic_simple_node * n = nodes[*ni];
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

/**
 * This function gets all the points-to pairs in the form of <pointer, field,
 * pointee> tuples and stores them in POINTS_TO_PAIRS and PROGRAM_POINTS_TO_PAIRS.
 */

void non_deterministic_simple_graph::
get_points_to_pairs (map<pair<label, label>, set<label> > & points_to_pairs)
{
	map<label, set<node_index> > label_edges = stack->get_out_edge_list ();
	map<label, set<node_index> >::iterator li;
	for (li = label_edges.begin (); li != label_edges.end (); li++)
	{
		label name = li->first;
		set<node_index> s = li->second;
		get_points_to_pairs (s, points_to_pairs);
	}
}

void non_deterministic_simple_graph::
get_points_to_pairs (set<node_index> & s, map<pair<label, label>, set<label> > & points_to_pairs)
{
	set<node_index>::iterator ni;
	for (ni = s.begin (); ni != s.end (); ni++)
	{
		non_deterministic_simple_node * n = nodes[*ni];
		get_points_to_pairs (*n, points_to_pairs);
	}
}


void non_deterministic_simple_graph::
get_points_to_pairs (non_deterministic_simple_node & src, map<pair<label, label>, set<label> > & points_to_pairs)
{
	label stack_id = stack->get_node_id ();
	label src_name = src.get_node_name (stack_id);
	map<label, set<node_index> > out_edges = src.get_out_edge_list ();
	map<label, set<node_index> >::iterator ei;
	for (ei = out_edges.begin (); ei != out_edges.end (); ei++)
	{
		label l = ei->first;
		set<node_index> dests = ei->second;
		set<label> dest_names;
		get_nodes_names (dests, dest_names);
		points_to_pairs[make_pair (src_name, l)].insert (dest_names.begin (), dest_names.end ());
	}
}

void non_deterministic_simple_graph::
print_points_to_pairs (map<pair<label, label>, set<label> > & points_to_pairs, bool one_per_line)
{
	unsigned int count_pairs = 0;
	map<pair<label, label>, set<label> >::iterator pi;
	for (pi = points_to_pairs.begin (); pi != points_to_pairs.end (); pi++)
	{
		label pointer = pi->first.first;
		label field = pi->first.second;

		csvarinfo_t variable1;
		variable1 = VEC_index (csvarinfo_t, program.variable_data, pointer);
		if (!variable1 || !variable1->decl && !DECL_ARTIFICIAL (variable1->decl))
			continue;
	
		if (one_per_line)
		{
			set<label> pointees = pi->second;
			set<label>::iterator si;
			for (si = pointees.begin (); si != pointees.end (); si++)
			{
				csvarinfo_t variable2 = VEC_index (csvarinfo_t, program.variable_data, *si);
				// if (variable2 && variable2->decl)// && !DECL_ARTIFICIAL (variable2->decl))
				{
					// INFO ("\n<%s(%d),%d,", variable1->name, pointer, field);
					INFO ("\t<%s(%d),", variable1->name, pointer);
					INFO ("%s(%d)>", variable2->name, *si);
					// if (DECL_ARTIFICIAL (variable1->decl))
					//	INFO ("   --");
					INFO ("\n");
					count_pairs++;
				}
			}
		}
		else
		{
			//RESULT ("\n\t<%s(%d),%d>,{", variable1->name, pointer, field);
			RESULT ("\n\t<%s(%d),%d,{", variable1->name, pointer, field);
		
			set<label> pointees = pi->second;
			set<label>::iterator si;
			for (si = pointees.begin (); si != pointees.end (); si++)
			{
				csvarinfo_t variable2 = VEC_index (csvarinfo_t, program.variable_data, *si);
				// if (variable2 && variable2->decl)// && !DECL_ARTIFICIAL (variable2->decl))
				{
					RESULT ("%s(%d),", variable2->name, *si);
					count_pairs++;
				}
			}
			RESULT ("}>");
		}
	}
	
	if (!one_per_line)
		RESULT ("\n\tnum_points_to_pairs=%d", count_pairs);
}

float non_deterministic_simple_graph::
count_average_out_edges ()
{
	unsigned int number_of_nodes = stack->count_out_edges ();
	float number_of_out_edges = 0;
	map<label, set<node_index> >::iterator ei;
	map<label, set<node_index> > out_edges = stack->get_out_edge_list ();
	for (ei = out_edges.begin (); ei != out_edges.end (); ei++)
	{
		set<node_index> out_nodes = ei->second;
		set<node_index>::iterator ni;
		for (ni = out_nodes.begin (); ni != out_nodes.end (); ni++)
		{
			non_deterministic_simple_node * n = nodes[*ni];
			number_of_out_edges += n->count_out_edges ();
		}
	}
	if (!number_of_nodes)
		return number_of_out_edges;
	return number_of_out_edges / number_of_nodes;
}

void non_deterministic_simple_graph::
get_nodes_edges (unsigned int & max_num_nodes, float & max_avg_out_edges, bool print)	
{
	unsigned int num_nodes = stack->count_out_edges ();
	float avg_out_edges = count_average_out_edges ();
	if (max_num_nodes + max_avg_out_edges < num_nodes + avg_out_edges)
	{
		max_num_nodes = num_nodes;
		max_avg_out_edges = avg_out_edges;
	}
	if (!print)
		return;

	RESULT ("\n\tnum_nodes=%d, avg_out_edges=%.2f", num_nodes, avg_out_edges);

	map<label, set<node_index> > out_edges = stack->get_out_edge_list ();
	map<label, set<node_index> >::iterator ei;
	for (ei = out_edges.begin (); ei != out_edges.end (); ei++)
	{
		label l = ei->first;
		set<node_index> out_nodes = ei->second;
		if (out_nodes.size () > 1)
		{
			csvarinfo_t variable = program.cs_get_varinfo (l);
			RESULT ("\n\t%s(%d) is replicated %d times", 
				variable->name, l, out_nodes.size ());
		}
	}	
}

void non_deterministic_simple_graph::
get_graph_statistics (unsigned int & max_num_nodes, 
	float & max_avg_out_edges, 
	map<pair<label, label>, set<label> > & program_points_to_pairs, 
	map<label, set<label> > & program_root_aliases,
	set<set<list<int> > > & program_aliases,
	map<label, set<label> > & program_reachable_roots,
	bool print)
{
#if 0
	// Node-edge information
	get_nodes_edges (max_num_nodes, max_avg_out_edges, print);
#endif

	// Points-to pair information
	
	map<pair<label, label>, set<label> > points_to_pairs;
	get_points_to_pairs (points_to_pairs);
	if (print)
		print_points_to_pairs (points_to_pairs, false);
	// Copy all edges from points_to_pairs to program_points_to_pairs
	map<pair<label, label>, set<label> >::iterator pi;
	for (pi = points_to_pairs.begin (); pi != points_to_pairs.end (); pi++)
	{
		label src = pi->first.first;
		label l = pi->first.second;
		set<label> dests = pi->second;
		program_points_to_pairs[make_pair (src, l)].insert (dests.begin (), dests.end ());
	}

#if 0
	// Alias information

	set<set<list<int> > > set_of_aliases;
	get_aliases (set_of_aliases, program_aliases);
	if (print)
	{
		DEBUG ("\nOur graph:");
		print_aliases (set_of_aliases);
	}
	// DEBUG ("\nOur compact graph:");
	// non_deterministic_simple_graph * compact_g = get_compact_graph ();
	// compact_g->print_aliases (set_of_aliases, program_aliases);

	// Root alias information

	map<label, set<label> > root_aliases;
	get_root_aliases (root_aliases, program_root_aliases);
	if (print)
		print_root_aliases (root_aliases);

	// Compaction may introduce spurious root_aliases information. For
	// example, if {x=&y;z=&y;} else {x=&y;w=&y;} our graph =
	// {(x,n1)(y,n2)(y,n3)(z,n4)(w,n5)(n1,*,n2),(n1,*.n3)(n4,*,n2)(n5,*,n3)}.
	// Here w and z are not reachable from each other. However, after
	// compaction, i.e. after merging n2 and n3 which have the same name y,
	// we spuriously get that w and z are reachable.

	// map<label, set<label> > compact_root_aliases;
	// compact_g->print_root_aliases (compact_root_aliases);

	// Reachability

	map<label, set<label> > reachable_roots;
	get_reachable_roots (reachable_roots, program_reachable_roots);
	if (print)
		print_reachable_roots (reachable_roots);
#endif
}

void non_deterministic_simple_graph::
print_value (const char * file)
{
	struct timeval start;	
	start_timer (start);

//#if DEBUG_CONTAINER
	map<pair<label, label>, set<label> > points_to_pairs;
	get_points_to_pairs (points_to_pairs);
	print_points_to_pairs (points_to_pairs, false);
//#endif
	
	unsigned int n = 0;
	float e = 0;
	get_nodes_edges (n, e, true);

	DEBUG ("\nreceived addr of variable_data=%x", program.variable_data);
	DEBUG ("\nnon_deterministic_simple_graph::print_graph ()");
	DEBUG ("\nRoot node %d", stack->get_node_id ());
	DEBUG ("\nNumber of nodes=%d", nodes.size ());

	map<node_index, non_deterministic_simple_node *>::iterator ni;
#if DEBUG_CONTAINER
	DEBUG ("\nNodes: ");
	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		non_deterministic_simple_node * n = ni->second;
		DEBUG ("%d,", n->get_node_id ());
	}
#endif

	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		DEBUG ("\nprinting node %d", ni->first);
		non_deterministic_simple_node * n = ni->second;
		if (stack->get_node_id () == n->get_node_id ())
			n->print_node (file, nodes);
		else
			n->print_node (NULL, nodes);
	}

#if DEBUG_CONTAINER
	DEBUG ("\nForward edges done");

	for (ni = nodes.begin (); ni != nodes.end (); ni++)
	{
		non_deterministic_simple_node * n = ni->second;
		if (stack->get_node_id () == n->get_node_id ())
			n->print_node_reverse (file);
		else
			n->print_node_reverse (NULL);
	}
	
	DEBUG ("\nBackward edges done");
#endif
//	print_access_paths (file);
#if CHECK_CONTAINER
	// VARIABLE_DATA is passed by analysis only when THIS graph is in okay
	// state
	// is_graph_okay ();
#endif

#if STATISTICS_CONTAINER
	unsigned int n = 0;
	float e = 0;
	map<pair<label, label>, set<label> > program_points_to_pairs;	
	map<label, set<label> > program_root_aliases;
	set<set<list<int> > > program_aliases;
	map<label, set<label> > program_reachable_roots;
	get_graph_statistics (n, e, program_points_to_pairs, program_root_aliases, program_aliases, program_reachable_roots, true);
#endif

	stop_timer (start, print_value_stats);
}



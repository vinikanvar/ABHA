
/************************
 * @author Vini Kanvar
************************/

#include "points_to_analysis_fi.hh"
#include "langhooks.h"

#define LIVENESS_BASED 1

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

/**
 * BOUNDARY VALUE of each function:
 *
 * We need to add all locals to value_in in beginning so that they (and their
 * field nodes) remain available before the statement when required. Otherwise,
 * if there are lots of lhs nodes present in g_pt but none present in VALUE, we
 * will need to match APs of those lhs nodes with lhs expression to find the
 * right lhs node for the statement. 
 * To elaborate, following has to be done.
 * 	Find all lhs nodes from gPT
 * 		If not found in gPT 
 *			Call generate_addressof_node (lhs)
 *			Add new node to fresh nodes
 * 		Else
 *	 		If not found in value_in
 *				Use the lhs node from fresh nodes
 *			Else use it. 
 * SIMPLE solution (closer to semantics): 
 * 	Generate locals in fresh nodes, add to value_in, use as needed.
 *
 * However, heap field nodes are still generated on-the-fly (due to late type
 * discovery). These are explicitly added to VALUE_IN and fresh heap nodes for
 * future program points. 
 */


points_to_analysis_fi::
points_to_analysis_fi (bool is_val_context):
	pt_access_map (g_pt, g_ap), 
	forward_inter_procedural_analysis (is_val_context)
{
	tot_stmttouch = 0;
	tot_update_points = 0;
	tot_potaffreg = 0;
	tot_finalaffreg = 0;
}

points_to_analysis_fi::
~points_to_analysis_fi ()
{
	delete_context_aux_info ();
}

pt_fi_graph * points_to_analysis_fi::
get_g_pt ()
{
	return &g_pt;
}

ap_fi_graph * points_to_analysis_fi::
get_g_ap ()
{
	return &g_ap;
}

pt_access_fi_map * points_to_analysis_fi::
get_pt_access_map ()
{
	return &pt_access_map;
}

/**
 * A g_pt node is unused_heap if it is in fresh_heap_node and its ap_nodes
 * and ap_unbounded are empty. Note that a heap node in fresh_heap_node may not
 * be unused (i.e. its ap_nodes or ap_unbounded may be non-empty) if the node
 * is on-the-fly created heap field node.
 */

bool points_to_analysis_fi::
is_unused_heap_node (pt_node_index pnid)
{
	if (!g_pt.is_fresh_heap_node (pnid))
		return false;

	set<ap_node_index> ap_nodes = pt_access_map.get_ap_nodes (pnid);
	bool ap_unbounded = pt_access_map.get_ap_unbounded (pnid);

	if (!ap_nodes.size () && !ap_unbounded)
		return true;

	return false;
}

void points_to_analysis_fi:: 
generate_fresh_vars (set<label> & vars, pt_node_set & value) 
{ 
	DEBUG ("\ngenerate_fresh_vars()"); 

	int old_max_node_id = g_pt.get_max_node_id ();
 
	set<pt_node_index> var_nodes;
	g_pt.generate_addressof_nodes (vars, var_nodes);

	initialize_fresh_ans (old_max_node_id, value);

	// Retrieve from VAR_NODES those nodes that are in FRESH_NAMED_NODES and
	// add them to VALUE; FRESH_HEAP_NODES are already present in VALUE.
	g_pt.get_fresh_named_nodes (var_nodes);
	value.gen (var_nodes);
}

void points_to_analysis_fi::
generate_missing_vars (set<label> & vars,
	pt_node_set & value)
{
	// Check if value_in has VARS. This would be true if this function is
	// recursively called and VARS from previous context of this function
	// are being propagated. NOTE: We need to check for all VARS since in
	// recursive function call, due to bypassing, some VARS (locals) (that
	// are not reachable from globals/parameters) may not be passed to
	// START_BLOCK of this function.

	set<label> value_variables;
#if SUMM_K_CONSISTENT
	g_pt.get_all_names (value.pt_nodes, value_variables);
#else
	g_pt.get_nodes_names (value.pt_nodes, value_variables);
#endif

	set<label> missing_vars;
	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
	{
		label var = *vi;
		if (value_variables.find (var) != value_variables.end ())
			continue;

#if DEBUG_CONTAINER
		csvarinfo_t varinfo = program.cs_get_varinfo (var);
		DEBUG ("\ngenerating var node=%s(%d)", varinfo->name, var);
#endif
		missing_vars.insert (var);
	}

	generate_fresh_vars (missing_vars, value);
}


/**
 * This function adds to VALUE new local nodes if they are not already present
 * in VALUE.
 */

void points_to_analysis_fi::
generate_missing_locals (pt_node_set & value, 
	struct cgraph_node * curr_function)
{
	set<label> local_variables = program.get_local_variables (curr_function);
	DEBUG ("\ngot locals");

	if (!local_variables.size ())
		return;

	generate_missing_vars (local_variables, value);

#if INTERMEDIATE_RESULT
	RESULT ("\nLocals created, g_pt=");
	g_pt.print_graph (NULL);
#endif
}

void points_to_analysis_fi::
generate_missing_params (pt_node_set & value, 
	struct cgraph_node * curr_function)
{
	set<label> params = program.get_function_parameters (curr_function);
	DEBUG ("\ngot params");

	if (!params.size ())
		return;

	generate_missing_vars (params, value);
}

void points_to_analysis_fi::
generate_missing_globals (pt_node_set & value)
{
	DEBUG ("\ngenerate_missing_globals()");

	set<label> vars = program.get_global_heap_variables ();

	// Store new global nodes in g_pt.FRESH_NODES
	value.gen (g_pt.stack.get_node_id ());
	generate_missing_vars (vars, value);
}

void points_to_analysis_fi::
generate_fresh_heap_nodes (pt_node_set & value)
{		
	value.gen (g_pt.fresh_heap_nodes);
}

void points_to_analysis_fi::
initialize_fresh_ans (int old_max_node_id, 
	pt_node_set & value)
{
	// Check if current_max_node_id <= old_max_node_id
	if (g_pt.get_max_node_id () == old_max_node_id)
		return;
	if (g_pt.get_max_node_id () < old_max_node_id)
		RESULT ("\nError: curr_max_node_id=%d, old_max_node_id=%d",
			g_pt.get_max_node_id (), old_max_node_id);

	// If fresh nodes have been generated in g_pt, then initialize ANs, and
	// add fresh nodes to g_pt.FRESH_NODES.

	DEBUG ("\ninitialize_fresh_ans (old_max_node_id=%d)", old_max_node_id);
	set<pt_node_index> nvisit = g_pt.get_generated_nodes (old_max_node_id);
	value.gen (nvisit);

	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
	map<pt_node_index, access_name> new_pt_to_access_name; 
	map<pt_node_index, max_depth> new_pt_to_max_depth; 
	map<pt_node_index, pt_node_index> summ_cmpts_map;
	map<pt_node_index, bool> affected_nodes;
	set<pt_node_index> empty_set;
	def_stmt_set ds;
	label l = 0;

	// NREACH=NVISIT i.e. nodes reachable from NVISIT (newly created nodes)
	// are NVISIT only.  Therefore, we can simply set NREACH=NVISIT in
	// find_new_ans_and_affected_region(). But we have not done so in order
	// to keep NREACH inside that function which is required to compute
	// affected_nodes.

	// Compute EXT_BNDRY nodes whose APs do not change. In case of fresh
	// nodes, ext_bndry will be only the stack node. But in case of
	// on-the-fly created field nodes H.F (present in NVISIT), ext_bndry
	// will be the root node H.

	// During initialization, nvisit has following type of nodes:
	// (a) Unused stack nodes: their ap_nodes needs to be set to their
	// names.  This is important because the successor nodes create their
	// ap_nodes by appending the out-edge field to the stack node's
	// ap_nodes. 
	// (b) Unused heap nodes: their node_name_type needs to be set to their
	// names. This is important in order to differentiate between two heaps
	// of different types.
	// (c) on-the-fly generated heap field nodes: their newly discovered
	// node_name_type needs to be set. Their ap_nodes needs to be derived from
	// the ap_nodes already present on their root heap node.

	affected_nodes = find_new_ans_and_affected_region (nvisit, value, 
		empty_set, empty_set, l, ds, empty_set, empty_edges, empty_edges,
		new_pt_to_max_depth, summ_cmpts_map, new_pt_to_access_name);

#if SUMM_K_CONSISTENT
	pt_access_map.set_max_depth (affected_nodes, new_pt_to_max_depth);
#endif
	pt_access_map.set_access_name (affected_nodes, new_pt_to_access_name);
	g_pt.insert_fresh_nodes (affected_nodes);

#if DEBUG_CONTAINER
	DEBUG ("\nUpdated pt_access_map=");
	pt_access_map.print_map (NULL, NULL);
#endif
}

/** 
 * @returns the top data flow value of the lattice.  This is the default data
 * flow value.
 */

pt_node_set * points_to_analysis_fi::
initial_value ()
{
	// Initial value for each function is the set of fresh local nodes of
	// that function. Since this is function specific, we cannot insert
	// these nodes here.
	return new pt_node_set;
}

/**
 * Initialize all globals with null_id. But since we are not saving null_id
 * pointees, the boundary value is empty.
 */

pt_node_set * points_to_analysis_fi::
boundary_value ()
{
	FUNBEGIN ();

	pt_node_set * boundary = new pt_node_set ();

	generate_missing_globals (*boundary);

#if INTERMEDIATE_RESULT
	RESULT ("\nGlobals created, g_pt=");
	g_pt.print_graph (NULL);
#endif

	generate_missing_locals (*boundary, program.main_cnode);
	generate_missing_params (*boundary, program.main_cnode);

	RETURN (boundary);
	// return boundary;
}

void points_to_analysis_fi::
process_in_value (context<pt_node_set, variables> * current_context, basic_block current_block)
{
	// FIXME: This function takes a lot of percentage of the total analysis time.
	FUNBEGIN ();
	DEBUG ("\nprocess_in_value(block=%d)", current_block->index);

	pt_node_set * in_value = current_context->get_in_value (current_block);

#if GC_ON_THE_FLY
	if (!in_value)
		// This is not an error
		RETURN_VOID ();
		// return;
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
	kill_weak_access_nodes (*in_value);
#endif

#if FI_REANALYSIS
	set<pt_node_index>::iterator ni;
	context_index cid = current_context->get_context_id ();
	for (ni = in_value->pt_nodes.begin (); ni != in_value->pt_nodes.end (); ni++)
	{
		pt_node_index nid = *ni;
		in_value_to_blocks[nid].insert (make_pair (cid, current_block));
	}
#endif

	RETURN_VOID ();
}

/**
 * This function is called if edge srcid->destid is newly added to FI gPT. This
 * function checks if srcid and destid existed in old FS gPT. If yes, then it
 * adds the edge (i.e. the pair <srcid,destid>) to OLD_FS_NEW_FI_EDGES.
 */

#if FI_REANALYSIS
void points_to_analysis_fi::
add_old_fs_new_fi_edge (pt_node_index srcid,
	pt_node_index destid,
	unsigned int old_max_node_id,
	set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges)
{
	// If srcid is new FS gPT node
	if (srcid > old_max_node_id)
		return;
	// If destid is new FS gPT node
	if (destid > old_max_node_id)
		return;

	old_fs_new_fi_edges.insert (make_pair (srcid, destid));
}
#endif

/**
 * OLD_FS_NEW_FI_EDGES are the new edges added to FI information (gPT) between
 * old FS information (gPT nodes). This function finds the <context,block> that
 * will contain a new edge (of OLD_FS_NEW_FI_EDGES). It then adds the context
 * and the block to the worklist for reanalysis.
 */

#if FI_REANALYSIS
void points_to_analysis_fi::
reanalyse_fi_dept_blocks (set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges)
{
	set<pair<pt_node_index, pt_node_index> >::iterator ei;
	for (ei = old_fs_new_fi_edges.begin (); ei != old_fs_new_fi_edges.end (); ei++)
	{
		pt_node_index srcid = ei->first;
		pt_node_index destid = ei->second;
		// If srcid or destid is not found at any IN-block, then no
		// block needs reanalysis. This is not an error since
		// srcid/destid may exist during some intermediate analysis but
		// may not exist at any IN-block.
		if (in_value_to_blocks.find (srcid) == in_value_to_blocks.end ())
		{
			DEBUG ("\nsrcid=%d not found in in_value_to_blocks", srcid);
			continue;
		}
		if (in_value_to_blocks.find (destid) == in_value_to_blocks.end ())
		{
			DEBUG ("\ndestid=%d not found in in_value_to_blocks", destid);
			continue;
		}

		set<pair<context_index, basic_block> > src_context_blocks =
			in_value_to_blocks[srcid];
		set<pair<context_index, basic_block> > dest_context_blocks =
			in_value_to_blocks[destid];

		set<pair<context_index, basic_block> >::iterator scbi;
		for (scbi = src_context_blocks.begin (); scbi != src_context_blocks.end (); scbi++)
		{
			pair<context_index, basic_block> src_context_block = *scbi;
			
			// If both srcid and destid are not present at this
			// <context,block> then the new edge is not valid at
			// this program point. Therefore, no need to reanalyze
			// this block.
			if (dest_context_blocks.find (src_context_block) == dest_context_blocks.end ())
				continue;

			context_index src_cid = src_context_block.first;
			basic_block src_block = src_context_block.second;
			context<pt_node_set, variables> * src_context = get_context (src_cid);
			add_context_to_worklist (src_context);
			if (src_context->add_block_to_worklist (src_block))
			{
				// Print if block has been newly added.
				RESULT ("\nold_fs_new_fi_edge=%d->%d", srcid, destid);
				RESULT ("\nReanalyse context=%d, block=%d", src_context->get_context_id (), src_block->index);
			}
		}

	}
}
#endif

/** 
 * Retrieves a value context at the called function if it exists, and returns
 * the value after evaluation through the called function.
 * If the value context does not exist at the called function, this function
 * creates one, adds it to the set of contexts at the called function, and
 * returns the TOP value (as the evaluated value of the new created context,
 * since this has not yet been evaluated).
 */

void points_to_analysis_fi::
process_call_statement (context<pt_node_set, variables> * src_context, basic_block call_site)
{
	FUNBEGIN ();
/*
	pt_node_set * in_value1 = src_context->get_in_value (call_site);
	pt_node_set * in_value_copy1 = in_value1->copy_value (false);
	src_context->set_out_value (call_site, in_value_copy1);
	RETURN_VOID ();
	// return;
*/
	if (!src_context)
	{
		RESULT ("\nError: Current context is NULL\n");
		RETURN_VOID ();
		// return;
	}

	unsigned int block_type = ((block_information *)(call_site->aux))->get_block_type ();
	if (block_type & AUX_BLOCK)
	{
		copy_in_to_out (src_context, call_site);
		return;
	}

#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif

	set<struct cgraph_node *> dest_functions = get_called_functions (*src_context, call_site);
	if (!dest_functions.size ())
	{
		// Do not initialize OUT. This is an error. If function pointer
		// is to be assigned, then it should have been set before this
		// call only -- not after it.
		RESULT ("\nError: Cannot find called/destination function");

		pt_node_set * out_value = initial_value ();
		// generate_fresh_globals (*out_value);
		// struct cgraph_node * src_function = src_context->get_function ();
		// insert_fresh_locals (*out_value, src_function);
		src_context->set_out_value (call_site, out_value);
	
		RETURN_VOID ();
		// return;
	}

	pt_node_set * out_value = src_context->get_out_value (call_site);
	if (!out_value)
	{
		out_value = initial_value ();
	}
	// We do not change the old OUT value; we change a copy of the old OUT
	// value. This is because old OUT value saved in COPY_OLD_OUT_VALUE (in
	// ipa/forward_inter_procedural_analysis.cpp) should not be modified.
	else
	{
		DEBUG ("\nCreating new out_value");
		// Rohan Padhye: IN = OUT_pred U IN. Take self-meet to ensure
		// monotonic results.  IS_LOOP_MERGE = FALSE
		pt_node_set * out_value_copy = out_value->copy_value (false);
		out_value = out_value_copy;
	}

	src_context->set_out_value (call_site, out_value);

#if DEBUG_CONTAINER
	DEBUG ("\nValue at out of call-site");
	out_value->print_value (NULL);
#endif

	// Iterate over all functions pointed by a function pointer.
	set<cgraph_node *>::iterator fi;
	for (fi = dest_functions.begin (); fi != dest_functions.end (); fi++)
	{
		struct cgraph_node * dest_function = *fi;

#if DEBUG_CONTAINER
		const char * dest_function_name =
			IDENTIFIER_POINTER (DECL_NAME (dest_function->decl));
		DEBUG ("\nChecking context of function %s, src_context %d, call_site %d",
			dest_function_name, src_context->get_context_id (), call_site->index);
#endif

		// Every called function (via function pointer) has different
		// function parameters. Therefore, a different copy of
		// calling_value should be passed.

		pt_node_set * in_value = src_context->get_in_value (call_site);
		// IS_LOOP_MERGE = FALSE
		pt_node_set in_value_copy;
		in_value_copy.copy_value (*in_value, false);
#if DEBUG_CONTAINER
		DEBUG ("\nin_value_copy of function call (before function parameter mapping)");
		in_value_copy.print_value (NULL);
#endif

#if SKIP_EMPTY_CFG
		if (program.is_cfg_ptr_asgn_empty (dest_function))
		{
			out_value->copy_value (in_value_copy, false);
			continue;
		}
#endif

		// Map actual parameters to formal parameters
		process_function_arguments (src_context, call_site, &in_value_copy, dest_function);

#if INTERMEDIATE_RESULT
		DEBUG ("\ncalling_value + argument_mapping of function %s",
			cgraph_node_name (dest_function));
		// calling_value->print_value (NULL);
		g_pt.print_subgraph (NULL, in_value_copy.pt_nodes);
#endif

		// Propagate part of the value which is reachable from the
		// parameters of the function and global variables.  The
		// parameter-and-global-var-unreachable part is left with
		// IN_VALUE_COPY and the parameter-and-global-var-reachable
		// part is returned.
		// FIXME: Extract pointers reachable from variables which are
		// live in the called function rather than those that are
		// reachable from parameters.

		// Extract par_glob_reachable value from in_value_copy and not out_value_copy. 
		map<pt_node_index, pt_node_index> caller_clone;
		set<pt_node_index> int_bndry_nodes;
		pt_node_set * par_glob_reachable_value = 
			extract_par_glob_reachable_value (dest_function, in_value_copy, 	
				int_bndry_nodes, caller_clone);
		pt_node_set * calling_value = par_glob_reachable_value;
#if DEBUG_CONTAINER
		print_clone_map (caller_clone);
#endif

		// Generate locals of the called_function. These are required
		// for creating points-to pairs of the called function's
		// statements.  These need to be inserted after par_glob are
		// extracted. Otherwise, these will be marked as par_glob
		// unreachable and then not passed to the called function.
		generate_missing_locals (*calling_value, dest_function);
		// Generate fresh_heap_nodes -- free available heap nodes
		generate_fresh_heap_nodes (*calling_value);

#if INTERMEDIATE_RESULT
		RESULT ("\nin_value_copy left with par_glob-unreachable nodes = ");
		in_value_copy.print_value (NULL);
		DEBUG ("\nint_bndry_nodes=");
		set<pt_node_index>::iterator bi;
		for (bi = int_bndry_nodes.begin (); bi != int_bndry_nodes.end (); bi++)
			DEBUG ("%d,", *bi);
		RESULT ("\ncalling_value function %s: ", cgraph_node_name (dest_function));
		calling_value->print_value (NULL);
#endif

		// Process called context
		pt_node_set * function_out_value =
			process_destination_context (*src_context, call_site, dest_function, calling_value);

		if (!function_out_value)
			continue;
#if DEBUG_CONTAINER
		DEBUG ("\nfunction_out_value=");
		function_out_value->print_value (NULL);
#endif

		// Fetch from called context
		map<pt_node_index, set<pt_node_index> > * callee_clone = 
			(map<pt_node_index, set<pt_node_index> > *)
			src_context->get_dest_aux_info (call_site, dest_function);
		if (!callee_clone)
		{
			RESULT ("\nError: clone map of dest_context from src_context=%d,call_site=%d not found",
				src_context->get_context_id (), call_site->index);
			continue;
		}
#if DEBUG_CONTAINER
		DEBUG ("\nClone of callee function=%s", cgraph_node_name (dest_function));
		print_clone_map (*callee_clone);
#endif

		// caller_callee_context = returned by restore function.
		map<pt_node_index, set<pt_node_index> > caller_callee_clone;
		pt_node_set restored_out_value;
		caller_callee_clone = 
			restore_par_glob_unreachable_nodes (function_out_value->pt_nodes, 
			in_value_copy.pt_nodes, int_bndry_nodes, 
			restored_out_value, caller_clone, *callee_clone);

		append_clone_map (caller_callee_clone, *src_context);

		// FIXME: Add caller_callee_clone to current_context

		// Merge FUNCTION_OUT_VALUE and IN_VALUE_COPY
		// (par_glob-unreachable value).  This should happen before
		// processing return-received variable mapping as received
		// variable may be coming from IN_VALUE_COPY.  Copy
		// par_glob_unreachable value to out_value. In case the
		// statements after this function call are processed before the
		// value from the called function returns, then global variable
		// nodes will remain missing in the these statements (that are
		// after the function call). But that is okay. These statements
		// will be reprocessed when the value from the called function
		// returns.

		DEBUG ("\nCopied called context's out and par_glob-unreachable value to out");
		out_value->copy_value (restored_out_value, false);

		// Map returned value to receiving value.
		// process_return_value() does not kill the previous pointee of
		// the receiving variable (lhs) which was computed from the
		// previous called function (via function pointer).
		// FIXME: First delete previous pointees of lhs receiving
		// variable since process_return_value() does not kill edges.

		bool to_kill = false;
		// Kill if there is only one function call.
		if (dest_functions.size () == 1)
			to_kill = true;
		process_return_value (src_context, call_site, out_value, dest_function, to_kill);

#if INTERMEDIATE_RESULT
		RESULT ("\nout_value + return mapping of function %s",
			cgraph_node_name (dest_function));
		g_pt.print_subgraph (NULL, out_value->pt_nodes);
		out_value->print_value (NULL);
		// pt_node_set * out_value_pointer = src_context->get_out_value (call_site);
		// DEBUG ("\nout_value from out of call_site %d", call_site->index);
		// out_value_pointer->print_value (NULL);
#endif

		// Delete local variables in OUT_VALUE under the condition that
		// the SRC_CONTEXT has never been called by a context of
		// DEST_FUNCTION.
		// FIXME: Delete all variables whose address does not escape.
		// Delete all locals if SRC_CONTEXT has never been called by a
		// context of DEST_FUNCTION.

		map<pt_node_index, pt_node_index> new_clone;
		check_and_delete_local_variables (*src_context, dest_function, *out_value, &new_clone);
		append_clone_map (new_clone, *src_context);
#if DEBUG_CONTAINER
		DEBUG ("\ncheck_and_delete_local_variables:");
		out_value->print_value (NULL);
#endif

		// If there are multiple function pointees in a call-block, say
		// f1, f2, f3. Then contexts of f1, f2, f3 are added to the
		// worklist.  When END_BLOCK of f1 is processed, the
		// src_context is pushed onto the worklist. Therefore, blocks
		// after call_site in src_context are unnecessarily processed
		// before evaluating f2 and f3. Solution: Push src_context
		// before called contexts of src_context. This will also allow
		// the current_context to remain on top of worklist so that the
		// processing of current_context completes before
		// source_context.  FIXME: Confirm.
	}

	// Restrict Pout to Lout:
	// In a src_context, with local variable z, we could have a call:
	// fn(z); z is not passed to fn and is bypassed to point after the
	// call. PROCESS_PARSED_DATA() of the block deletes z if z is dead
	// after the call.
	// In a src_context, with local variable y, we could have a call:
	// fn(&y); y is passed to fn and is brought back to the point after
	// the call. We now need to delete this y if y is dead here after the
	// call.
	out_value = src_context->get_out_value (call_site);
#if DEBUG_CONTAINER
	DEBUG ("\nValue before deleting dead pointers");
	out_value->print_value (NULL);
#endif

#if LIVENESS_BASED
	// FIXME: For efficiency, compute dead vars only if out_value is non-empty
	set<pt_node_index> must_lhs_nodes;

	// Assume nodes reachable via incl_edges from live vars as live
	// (implicit liveness).
	// We need to assume reaching nodes also as live (implicit liveness).
	// map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
	// set<pt_node_index> empty_nodes;
	// get_live_data (*out_value, *src_context, call_site, 
	// 	empty_nodes, empty_edges, empty_edges, must_lhs_nodes);

	// Assume nodes reachable from live vars as live (implicit liveness). 
	get_live_data (*out_value, *src_context, call_site, must_lhs_nodes);

	if (must_lhs_nodes.size ())
	{
		// Perform cloning of pointees of nodes corresponding to VARIABLES.
		map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
		clone_and_update_subgraph (*out_value, must_lhs_nodes, 
			empty_edges, empty_edges, src_context, false, true);
	}
#endif
	out_value->clean ();

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
	kill_weak_access_nodes (*out_value);
#endif

	RETURN_VOID ();
}

/**
 * This function computes the points-to values at out of the block. In the end,
 * it restricts all the pointers to live variables. Note that we restrict only
 * the out value to liveness; in value is not restricted to liveness since
 * COMPUTE_IN() is not in control of DFA, but in control of IPA. 
 *
 * If the block is call block, only those argument-mappings in the block are
 * processed where the formal parameter belongs to CALLED_FUNCTION.
 */

bool points_to_analysis_fi::
process_parsed_data (context<pt_node_set, variables> * current_context, 
	basic_block current_block, 
	pt_node_set * calling_value, 
	bool to_kill)
{
	FUNBEGIN ();

	DEBUG ("\nprocess_parsed_data");

	list<pair<unsigned int, bool> > parsed_data_indices =
		((block_information *)(current_block->aux))->get_parsed_data_indices ();
	DEBUG ("\nFetched parsed data");

	unsigned int block_type = ((block_information *)(current_block->aux))->get_block_type ();
	DEBUG ("\nblock=%d type=%d", current_block->index, block_type);
	if (block_type & AUX_BLOCK)
	{
		copy_in_to_out (current_context, current_block);
		return true;
	}

	if (block_type & NORETURN_BLOCK)
	{
		bool is_out_initialized = true;
		current_context->set_out_value (current_block, initial_value ());
		DEBUG ("\nempty IN");
		return is_out_initialized;
	}

	set<pt_node_index> must_lhs_nodes;
	pt_node_set * value_in = current_context->get_in_value (current_block);
#if LIVENESS_BASED
	// FIXME: For efficiency, compute dead vars only if out_value is non-empty
	if (!(block_type & CALL_BLOCK)
		&& !(block_type & START_BLOCK)
		&& !parsed_data_indices.size ())
	{
		// Assume nodes reachable via incl_edges from live vars as live
		// (implicit liveness).
		// We need to assume reaching nodes also as live (implicit liveness).
		// map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
		// set<pt_node_index> empty_nodes;
		// get_live_data (*value_in, *current_context, current_block, 
		//	empty_nodes, empty_edges, empty_edges, must_lhs_nodes);

		// Assume nodes reachable from live vars as live (implicit liveness). 
		get_live_data (*value_in, *current_context, current_block, must_lhs_nodes);
	}
#endif
	// Reuse: Delete the value if it repeats at the predecessor program point.
	if (!(block_type & CALL_BLOCK) &&
		!(block_type & START_BLOCK) &&
		!parsed_data_indices.size () &&
		!must_lhs_nodes.size ())
	{
		DEBUG ("\nOptimum use");
		current_context->set_out_value (current_block, value_in);
		#if CHECK_CONTAINER || INTERMEDIATE_RESULT
		if (block_type & END_BLOCK)
		{
			RESULT ("\nEND BLOCK");
			print_fi_value ();
			RESULT ("\nEND BLOCK");
		}
		#endif

		bool is_out_initialized = true;
		RETURN (is_out_initialized);
		// return is_out_initialized;
	}

#if FORCED_MONOTONICITY
	pt_node_set * out_value = current_context->get_out_value (current_block);
	pt_node_set * copy_old_out_value = NULL;
	// If this is a call block, then VALUE represents the calling-value of
	// the block. We don't want to merge newly computed out-value in VALUE
	// with original calling-value in copy_old_out_value.
	if (out_value && !(block_type & CALL_BLOCK))
	{
		// IN = OUT_pred U IN. Take self-meet to ensure
		// monotonic results.  IS_LOOP_MERGE = FALSE
		copy_old_out_value = out_value->copy_value (false);
	}
#endif

	if (block_type & START_BLOCK)
	{
		DEBUG ("\nSTART_BLOCK");
		if (first_stmt (current_block))
		{
			RESULT ("\nError: start block is not empty");
			RETURN (false);
			// return false;
		}
		DEBUG ("\nNo statement found in START_BLOCK");
		bool is_out_initialized = true;

		map<pt_node_index, set<pt_node_index> > * clone = 
			new map<pt_node_index, set<pt_node_index> >;
		current_context->set_aux_info (clone);
		DEBUG ("\nClone of context=%d created", current_context->get_context_id ());

		copy_in_to_out (current_context, current_block);
		// In recursively called context, locals from previous
		// context of this function and fresh locals are both present.
		// The locals from previous context are important if their
		// address is escaped to a global (important because their
		// pointees may be used via the global in the current context).
		// The fresh locals are any way important for the current
		// context's information. But how much precision gain will it
		// give to separate locals of previous context and current
		// context? I don't know. Think. 
		// For now, we will use old locals already initialized in
		// process_function_arguments().
		
		// FIXME: Restore the following if more precision is required.
		// pt_node_set * value_out = current_context->get_out_value (current_block);
		// insert_fresh_locals (value_out, curr_function);

		RETURN (is_out_initialized);
		// return is_out_initialized;
	}

	// The OUT of CALL blocks is initialized in process_call_statement().
	// Initialize other blocks here.
	// if (block_type & END_BLOCK)
	//	current_context->set_out_value (current_block, initial_value ());
	if (!(block_type & CALL_BLOCK))
		copy_in_to_out (current_context, current_block);

	// We initialize OUT of all blocks even if OUT is only same as IN.
	bool is_out_initialized = true;

	pt_node_set * value;
	if (block_type & CALL_BLOCK && (value = calling_value));
	else
		value = current_context->get_out_value (current_block);

	set<pt_node_index> value_excl_out_edges;
	map<pt_node_index, map<label, set<pt_node_index> > > incl_in_edges;
	map<pt_node_index, map<label, set<pt_node_index> > > incl_out_edges;

	// Iterate in forward direction for points-to analysis
	list<pair<unsigned int, bool> >::iterator it;
	for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
	{
		unsigned int index = (*it).first;
		bool is_assignment = (*it).second;
		DEBUG ("\nParsed data: index %d, bool %d, ", index, is_assignment);
		if (is_assignment)
		{
			#if DEBUG_CONTAINER
			program.print_assignment_data (index);
			#endif

			// In points-to analysis, the links at IN are either
			// (a) killed by lhs and transferred through lhs to (out) VALUE, or
			// (b) transferred without change from IN TO (out) VALUE
			DEBUG ("\nTransferring and generating points-to for assignment statement");

			process_assignment_statement (*value, value_excl_out_edges, incl_in_edges, incl_out_edges,
				current_context, current_block, index, to_kill);
		}
		else
		{
			#if DEBUG_CONTAINER
			program.print_variable_data (index);
			#endif
			DEBUG ("\nNo need to process use statements for points-to analysis");
		}
	}

#if LIVENESS_BASED
	// If this is a call-block, then we do nothing more i.e. we keep VALUE
	// restricted to Lin only (instead of Lout) (which it already was).
	// This is because these values (even though dead in Lout i.e. after
	// the function call) might be reachable from actual parameter in the
	// called function. 
	// FIXME: We have retained variables which are reachable and which
	// reach the actual parameter. However, we need to retain only the
	// former; we can delete the latter if dead in Lout.

	// If this is not a call-block, then restrict OUT value to liveness
	// only after computing all the points-to values of the whole block.
	// Otherwise problem: for example, x=&y;z=x; block with only z live at
	// out. If we perform liveness-restriction after every points-to
	// computation, then x=&y will get deleted before z=x is processed.
	// Therefore, z=&y will not get derived.

	if (!(block_type & CALL_BLOCK))
	{
		// set<pt_node_index> must_lhs_nodes;
		must_lhs_nodes.clear ();

		// Assume nodes reachable via incl_edges from live vars as live
		// (implicit liveness).
		// We need to assume reaching nodes also as live (implicit liveness).
		// get_live_data (*value, *current_context, current_block, 
		//	value_excl_out_edges, incl_in_edges, incl_out_edges, must_lhs_nodes);

		// Assume nodes reachable from live vars as live (implicit liveness). 
		get_live_data (*value, *current_context, current_block, must_lhs_nodes);

		// Add must_lhs_nodes to value_excl_out_edges
		// Remove must_lhs_nodes from incl_in_edges and incl_out_edges
		populate_excl_edges (must_lhs_nodes, value_excl_out_edges, incl_in_edges, incl_out_edges, *value);
	}
#else
	value->clean ();
#endif

	// Clone (rename nodes) at end of block if either there are any
	// statements in the block or if there is anything dead.
	// We do not delete variable nodes themselves.
	if (parsed_data_indices.size () || value_excl_out_edges.size ())
		clone_and_update_subgraph (*value, value_excl_out_edges, 
			incl_in_edges, incl_out_edges, current_context, true, true);

#if FORCED_MONOTONICITY
	// If this is a call block, then VALUE represents the calling-value of
	// the block. We don't want to merge newly computed out-value in VALUE
	// with original calling-value in copy_old_out_value.
	if (value && copy_old_out_value && !(block_type & CALL_BLOCK))
	{
		bool is_loop_merge = ((block_information *)(current_block->aux))->get_loop_join ();
		value->copy_value (*copy_old_out_value, is_loop_merge);
	}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
	kill_weak_access_nodes (*value);
#endif

	#if CHECK_CONTAINER || INTERMEDIATE_RESULT
	if (block_type & END_BLOCK)
	{
		RESULT ("\nEND BLOCK");
		print_fi_value ();
		RESULT ("\nEND BLOCK");
	}
	#endif

	if (block_type & CALL_BLOCK)
		RETURN (is_out_initialized);
		// return is_out_initialized;

	// Reuse: Delete the value if it repeats at the predecessor program point.
	pt_node_set * value_out = current_context->get_out_value (current_block);
	if (value_out->is_value_same (*value_in))
	{
		DEBUG ("\nOptimum use");
		current_context->set_out_value (current_block, value_in);
	}

	RETURN (is_out_initialized);
	// return is_out_initialized;
}

bool points_to_analysis_fi::
process_assignment_statement (pt_node_set & value,
	context<pt_node_set, variables> * current_context,
	basic_block current_block,
	unsigned int assignment_data_index,
	bool to_kill)
{
	// TODO FIXME 
	return true;
}

#if SUMM_STMT_CLOSURE == 0
/**
 * input/output: value_excl_out_edges, incl_in_edges, incl_out_edges
 */

bool points_to_analysis_fi::
process_assignment_statement (pt_node_set & value,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	context<pt_node_set, variables> * current_context,
	basic_block current_block,
	unsigned int assignment_data_index,
	bool to_kill)
{
	FUNBEGIN ();

	DEBUG ("\nprocess_assignment_statement");

	constraint_t assignment = VEC_index (constraint_t, program.assignment_data, assignment_data_index);
	constraint_expr lhs = assignment->lhs;
	constraint_expr rhs = assignment->rhs;
#if DEBUG_CONTAINER
	DEBUG ("\n");
	program.print_assignment_data (assignment_data_index);
#endif

	// For x.f=&x, the following is true without type
	// Return if LHS equals RHS. This can happen due to pointer arithmetic.
	if (lhs.var == rhs.var && lhs.offset == rhs.offset && lhs.type == rhs.type)
		RETURN (true);
	        // return true;

	// If block has PHI statement, and ASSIGNMENT_DATA_INDEX is not the
	// first PHI constraint, then do not perform killing. PREVIOUS_PHI of
	// first phi statement will be found set, if there exists lhs=rhs phi
	// statement, in which case even the first phi statement should not
	// perform any killing.
	if (assignment->previous_phi)
	{
		DEBUG ("\nto_kill is set to false");
		to_kill = false;
	}

	#if DEBUG_CONTAINER
	DEBUG ("\npt_nodes value");
	value.print_value (NULL);
	#endif

	// In heap analysis, we create a fresh RHS and then merge it with
	// previously existing nodes, which refer to the same memory location
	// as the freshly created RHS. This is required because we want to add
	// the edge properties of the current RHS with the edges of the
	// previously existing RHS---which may involve materialization of the
	// previously existing RHS. 
	// We do not require this fresh creation of rhs in this _simple
	// analysis, which has no properties attached to fields/dereferences.

	// This WEAK_MUST_LHS_DEST_NODES is set of weak-must-pointers; Weak
	// because we are using points_to_analysis_simple which does not
	// include UNDEF/JUNK nodes

	generate_lhs_rhs_nodes (value, lhs, rhs, value_excl_out_edges, incl_in_edges, incl_out_edges, to_kill);

	// Annotate all pointers with statement id, i.e. do not restrict to
	// x->f=... type (lhs.type == DEREF) of statements only. Cyclic data
	// structures also need this statement id. e.g. x.f=&y; y.f=&x; in a
	// loop.
	def_stmt_set ds;
#if SUMM_STMT_CLOSURE
	// if (lhs.type == DEREF)
		ds.insert (assignment_data_index);
	// else
		// AP_ACYLIC_FI_GRAPH assumes non-empty DS.
		// Although DONT_CARE is not explicitly included in gAP edges.
		// ds.insert (DONT_CARE);
#endif
	RETURN (true);
}
#endif

void points_to_analysis_fi::
generate_lhs_rhs_nodes (pt_node_set & value,
	constraint_expr & lhs,
	constraint_expr & rhs,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	bool to_kill)
{
	FUNBEGIN ();

	// May/must lhs/rhs of this stateement considering 
	// (VALUE - VALUE_EXCL_OUT_EDGES) U VALUE_INCL_EDGES.
	set<pt_node_index> must_lhs_nodes;
	set<pt_node_index> may_lhs_nodes;
	set<pt_node_index> rhs_nodes;

	// FIXME: For efficiency, do not generate nodes of all the variables in
	// the beginning of the function.  We generate a variable node
	// on-the-fly when its address is taken. For lhs=&rhs, both lhs and rhs
	// nodes are generated. For other cases, lhs=rhs, *lhs=rhs, and
	// lhs=*rhs, we do not generate a new rhs variable. For *lhs=&rhs, rhs
	// is generated only if the pointee of lhs already existing.

//	if (lhs.pointer_arithmetic || rhs.pointer_arithmetic)
//		return;
	// Assume all pointer arithmetic happen only on arrays. Ignoring
	// pointer arithmetic on fields of structures.
	if (lhs.pointer_arithmetic)
		lhs.offset = 0;
	if (rhs.pointer_arithmetic)
		rhs.offset = 0;

	generate_rhs_nodes (value, rhs, rhs_nodes, value_excl_out_edges, incl_in_edges, incl_out_edges);
	bool is_rhs_non_empty = rhs_nodes.size ();
	generate_lhs_nodes (value, lhs, may_lhs_nodes, must_lhs_nodes, 
		value_excl_out_edges, incl_in_edges, incl_out_edges, is_rhs_non_empty);

	if (!to_kill)
	{
		DEBUG ("\nto_kill is false. Clear must_lhs_nodes");
		must_lhs_nodes.clear ();
	}

	pt_fi_node::get_nodes_valid_at_point (rhs_nodes, value.pt_nodes);
	pt_fi_node::get_nodes_valid_at_point (may_lhs_nodes, value.pt_nodes);
	pt_fi_node::get_nodes_valid_at_point (must_lhs_nodes, value.pt_nodes);

	// If lhs is not generated. Then we should not unnecessarily clone rhs.
	if (!may_lhs_nodes.size ())
		rhs_nodes.clear ();

#if DEBUG_CONTAINER
	set<pt_node_index>::iterator pi;
	DEBUG ("\nMay LHS:");
	for (pi = may_lhs_nodes.begin (); pi != may_lhs_nodes.end (); pi++)
		DEBUG ("%d,", *pi);
	DEBUG ("\nLHS-offset=%d", lhs.offset);
	DEBUG ("\nRHS:");
	for (pi = rhs_nodes.begin (); pi != rhs_nodes.end (); pi++)
		DEBUG ("%d,", *pi);
	if (must_lhs_nodes.size ())
		DEBUG ("\nmust LHS %d:", lhs.var);
	for (pi = must_lhs_nodes.begin (); pi != must_lhs_nodes.end (); pi++)
		DEBUG ("%d,", *pi);
#endif

	// Add must_lhs_nodes to value_excl_out_edges
	// Remove must_lhs_nodes from incl_in_edges and incl_out_edges
	populate_excl_edges (must_lhs_nodes, value_excl_out_edges, incl_in_edges, incl_out_edges, value);

	// Add may_lhs_nodes->ASTERISK->rhs_nodes to incl_in_edges and incl_out_edges
	populate_incl_edges (may_lhs_nodes, rhs_nodes, incl_in_edges, incl_out_edges, value);

	RETURN_VOID ();
}

/**
 * This function generates the rhs nodes for the variable RHS in RHS_NODES.
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: rhs_nodes
 */

void points_to_analysis_fi::
generate_rhs_nodes (pt_node_set & value,
	constraint_expr & rhs,
	set<pt_node_index> & rhs_nodes,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
#if UNSOUND_ARRAY
	csvarinfo_t rvar = program.cs_get_varinfo (rhs.var);
	if (rvar && rvar->decl && 
		TREE_CODE(rvar->decl) == VAR_DECL && 
		TREE_CODE (TREE_TYPE (rvar->decl)) == ARRAY_TYPE)
	{
		RESULT ("\nSkipping rhs array");
		return;
	}
#endif

	// This function takes the constraint_expr in parameter by reference.
	// Therefore, later if we want we could modify offset to 0.
	program.handle_unknown_offset (rhs);

	switch (rhs.type)
	{
	// lhs=rhs or lhs=&(rhs->f)
	// or
	// *lhs=rhs or lhs->f=rhs or *lhs=&(rhs->f) or lhs->f=&(rhs->f)
	case SCALAR:
	{
		DEBUG ("\nrhs.type == SCALAR");

#if MERGE_NON_POINTER_FIELDS
		// Ignore ...=&(lhs->f) case since (for efficiency) we are not
		// explicating non-pointer fields, which means fields are not
		// addressable.
		if (rhs.offset)
		{
			csvarinfo_t rinfo = program.cs_get_varinfo (rhs.var);
			RESULT ("\nIGNORE &(rhs=%s(%d)->f=%d)", rinfo->name, rinfo->id, 
				rhs.offset);
			break;
		}
#endif

		// Will generate undef node if it is required
		// On-the-fly heap field H.F nodes are connected
		// to those H that are valid at program point.
#if MERGE_NON_POINTER_FIELDS
		list<unsigned int> offset_sequence;
		offset_sequence.push_back (rhs.offset);
		generate_pointer_nodes (value, rhs.var, &offset_sequence, rhs_nodes,
			value_excl_out_edges, incl_in_edges, incl_out_edges);
#else
		generate_pointer_nodes (value, rhs.var, rhs.offset_sequence, rhs_nodes,
			value_excl_out_edges, incl_in_edges, incl_out_edges);
#endif

		break;
	}

	// lhs=&rhs
	// or
	// *lhs=&rhs or lhs->f=&rhs
	case ADDRESSOF:
	{
		DEBUG ("\nrhs.type == ADDRESSOF");
		// Throw Error if offset is non-zero. We have not handled such a case.
		if (rhs.offset)
			RESULT ("\nError: We did not expect ADDRESSOF with dereference of rhs");

#if MERGE_NON_POINTER_FIELDS
		// Do not allow taking address of member field
		csvarinfo_t rinfo = program.cs_get_varinfo (rhs.var);
		if (rinfo->offset)
		{
			RESULT ("\nIGNORE &(rhs=%s(%d))", rinfo->name, rinfo->id);
			break;
		}
		// FIXME: Do not allow dereferencing a pointee with non-zero offset
#endif

		// Note: rhs.var needs to stored on the edge from stack node to
		// this new node. This edge helps in finding this node again
		// from the stack node the next time.

		if (program.heap_var (rhs.var))
		{
			g_pt.generate_fresh_addressof_nodes (rhs.var, rhs_nodes);
			if (rhs_nodes.size () != 1)
			{
				RESULT ("\nError: There can be only one fresh node for %d", rhs.var);
			}
		}
		else
			g_pt.generate_addressof_nodes (rhs.var, rhs_nodes);

		#if DEBUG_CONTAINER
		DEBUG ("\nmalloc rhs_nodes=");
		set<pt_node_index>::iterator ni;
		for (ni = rhs_nodes.begin (); ni != rhs_nodes.end (); ni++)
			DEBUG ("%d,", *ni);
		#endif

		break;
	}
	// lhs=*rhs or lhs=rhs->f
	// or
	// *lhs=*rhs or lhs->f=rhs->f or ...
	// Such a statement exists in mcf benchmark.
	// Function suspend_impl <bb 13> *new_arc_6 = *arc_7;
	case DEREF:
	{
		DEBUG ("\nrhs.type == DEREF");

#if MERGE_NON_POINTER_FIELDS
		list<unsigned int> offset_sequence;
		offset_sequence.push_back (rhs.offset);
		g_pt.generate_deref_nodes (rhs.var, &offset_sequence, rhs_nodes,
			value_excl_out_edges, incl_in_edges, incl_out_edges);
#else
		g_pt.generate_deref_nodes (rhs.var, rhs.offset_sequence, rhs_nodes,
			value_excl_out_edges, incl_in_edges, incl_out_edges);
#endif

		break;
	}

	default:
		RESULT ("\nError: rhs.type cannot hold a fourth type");
		break;
	}
}

/**
 * This function populates lhs nodes for the variable LHS in MAY_LHS_NODES and
 * MUST_LHS_NODES, and generates any required nodes provided IS_RHS_NON_EMPTY
 * is true.
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: must_lhs_nodes, rhs_nodes
 */

void points_to_analysis_fi::
generate_lhs_nodes (pt_node_set & value,
	constraint_expr & lhs,
	set<pt_node_index> & may_lhs_nodes,
	set<pt_node_index> & must_lhs_nodes,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	bool is_rhs_non_empty)
{
#if UNSOUND_ARRAY
	csvarinfo_t lvar = program.cs_get_varinfo (lhs.var);
	if (lvar && lvar->decl && 
		TREE_CODE(lvar->decl) == VAR_DECL && 
		TREE_CODE (TREE_TYPE (lvar->decl)) == ARRAY_TYPE)
	{
		RESULT ("\nSkipping lhs array");
		return;
	}
#endif

	// This function takes the constraint_expr in parameter by reference.
	// Therefore, later if we want we could modify offset to 0.
	program.handle_unknown_offset (lhs);

	switch (lhs.type)
	{
	// lhs=...
	case SCALAR:
	{
		DEBUG ("\nlhs.type == SCALAR");

		// Throw Error if offset is non-zero. We have not handled such a case.
		if (lhs.offset)
			RESULT ("\nError: We did not expect SCALAR with dereference of lhs");

		g_pt.get_addressof_nodes (lhs.var, must_lhs_nodes);

		// If rhs node is present, generate an lhs node.
		DEBUG ("\nis_rhs_non_empty=%d", is_rhs_non_empty);
		if (is_rhs_non_empty)
			g_pt.generate_addressof_nodes (lhs.var, may_lhs_nodes);

		break;
	}

	// lhs->f=... or *lhs=...
	case DEREF:
	{
		DEBUG ("\nlhs.type == DEREF");

#if STRONG_UPDATES
#if MERGE_NON_POINTER_FIELDS
		list<unsigned int> offset_sequence;
		offset_sequence.push_back (lhs.offset);
		g_pt.get_must_pointer_nodes (lhs.var, &offset_sequence, must_lhs_nodes, 
			value_excl_out_edges, incl_in_edges, incl_out_edges, value.pt_nodes);
#else
		g_pt.get_must_pointer_nodes (lhs.var, lhs.offset_sequence, must_lhs_nodes, 
			value_excl_out_edges, incl_in_edges, incl_out_edges, value.pt_nodes);
#endif
#endif
#if DEBUG_CONTAINER
		set<pt_node_index>::iterator ni;
		DEBUG ("\nmust_lhs_nodes=");
		for (ni = must_lhs_nodes.begin (); ni != must_lhs_nodes.end (); ni++)
			DEBUG ("%d,", *ni);
#endif

		if (is_rhs_non_empty)
		{
			DEBUG ("\nFor lhs->f=... rhs_nodes is non-empty");

			// If rhs node is present, get/generate an lhs node
			// VARIABLE.*.FIELD.
			// On-the-fly heap field H.F nodes are connected
			// to those H that are valid at program point.
#if MERGE_NON_POINTER_FIELDS
			list<unsigned int> offset_sequence;
			offset_sequence.push_back (lhs.offset);
			generate_pointer_nodes (value, lhs.var, &offset_sequence, may_lhs_nodes,
				value_excl_out_edges, incl_in_edges, incl_out_edges);		
#else
			generate_pointer_nodes (value, lhs.var, lhs.offset_sequence, may_lhs_nodes,
				value_excl_out_edges, incl_in_edges, incl_out_edges);		
#endif
		}

		break;
	}

	case ADDRESSOF:
		RESULT ("\nError: Lvalue error.");
		break;

	default:
		RESULT ("\nError: rhs.type cannot hold a fourth type");
		break;
	}
}
	
void points_to_analysis_fi::
populate_excl_edges (set<pt_node_index> & must_lhs_nodes, 
	set<pt_node_index> & value_excl_out_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, 
	pt_node_set & value)
{
	// Add must_lhs_nodes to value_excl_out_edges
	value_excl_out_edges.insert (must_lhs_nodes.begin (), must_lhs_nodes.end ());

	// Remove must_lhs_nodes from incl_in_edges and incl_out_edges
#if PULL_ACCESS_NAMES 
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator ei;
	for (ei = incl_in_edges.begin (); ei != incl_in_edges.end (); ei++)
	{
		pt_node_index dest_nid = ei->first;
		map<label, set<pt_node_index> > in_edges = ei->second;
		if (in_edges.find (ASTERISK) == in_edges.end ())
			continue;
		set<pt_node_index> in_nodes = in_edges[ASTERISK];
		set<pt_node_index>::iterator ni;
		for (ni = in_nodes.begin (); ni != in_nodes.end (); ni++)
		{
			pt_node_index in_nid = *ni;
			if (must_lhs_nodes.find (in_nid) == must_lhs_nodes.end ())
				continue;
			
			incl_in_edges[dest_nid][ASTERISK].erase (in_nid);
			if (!incl_in_edges[dest_nid][ASTERISK].size ())
				incl_in_edges[dest_nid].erase (ASTERISK);
			if (!incl_in_edges[dest_nid].size ())
				incl_in_edges.erase (dest_nid);
		}
	}	
#else
	set<pt_node_index>::iterator nli;
	for (nli = must_lhs_nodes.begin (); nli != must_lhs_nodes.end (); nli++)
	{
		pt_node_index mln = *nli;
		if (incl_out_edges.find (mln) == incl_out_edges.end ())
			continue;
		incl_out_edges[mln].erase (ASTERISK);
		if (!incl_out_edges[mln].size ())
			incl_out_edges.erase (mln);
	}
#endif
}

void points_to_analysis_fi::
populate_incl_edges (set<pt_node_index> & may_lhs_nodes, 
	set<pt_node_index> & rhs_nodes, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges, 
	pt_node_set & value)
{
	// Add may_lhs_nodes->ASTERISK->rhs_nodes to incl_in_edges and incl_out_edges
#if PULL_ACCESS_NAMES 
	set<pt_node_index>::iterator ri;
	#pragma omp parallel for
	for (ri = rhs_nodes.begin (); ri != rhs_nodes.end (); ri++)
	{
		pt_node_index rnid = *ri;
		incl_in_edges[rnid][ASTERISK].insert (may_lhs_nodes.begin (), may_lhs_nodes.end ());
	}
#else
	set<pt_node_index>::iterator li;
	#pragma omp parallel for
	for (li = may_lhs_nodes.begin (); li != may_lhs_nodes.end (); li++)
	{
		pt_node_index lnid = *li;
		incl_out_edges[lnid][ASTERISK].insert (rhs_nodes.begin (), rhs_nodes.end ());		
	}
#endif
}

/**
 * This function fetches nodes pointed by VARIABLE.*.FIELD. It generates nodes
 * (for example, undef, V.FIELD nodes) as per requirement in THIS graph. 
 *
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: pointer_nodes
 */

void points_to_analysis_fi::
generate_pointer_nodes (pt_node_set & value,
	label var, 
	list<label> * field_sequence, 
	set<pt_node_index> & pointer_nodes,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	DEBUG ("\ngenerate_pointer_nodes(var=%d)", var);

	// Get VARIABLE
	set<pt_node_index> addr_nodes;
	g_pt.get_addressof_nodes (var, addr_nodes);

	// Get VARIABLE.*
	set<pt_node_index> dest_nodes;
	g_pt.get_destination_nodes (addr_nodes, ASTERISK, dest_nodes,
		value_excl_out_edges, incl_in_edges, incl_out_edges);
	#if DEBUG_CONTAINER
	DEBUG ("\ndest_nodes.size()=%d", dest_nodes.size ());
	DEBUG ("\nFetched dest nodes=");
	set<pt_node_index>::iterator ni;
	for (ni = dest_nodes.begin (); ni != dest_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
	#endif

	pt_fi_node::get_nodes_valid_at_point (dest_nodes, value.pt_nodes);

	#if DEBUG_CONTAINER
	DEBUG ("\nvalid dest_nodes.size()=%d", dest_nodes.size ());
	DEBUG ("\nFetched valid dest nodes=");
	for (ni = dest_nodes.begin (); ni != dest_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
	#endif

	if (!field_sequence)
	{
		pointer_nodes = dest_nodes;
		#if DEBUG_CONTAINER
		DEBUG ("\npointer_nodes=");
		for (ni = pointer_nodes.begin (); ni != pointer_nodes.end (); ni++)
			DEBUG ("%d,", *ni);
		#endif

		return;
	}

	// Generate VARIABLE.*.FIELD
	// Get type of node being dereferenced. This is required if a heap
	// field node needs to be created on-the-fly.
	csvarinfo_t var_info = VEC_index (csvarinfo_t, program.variable_data, var);
	list<label>::iterator fi;
	for (fi = field_sequence->begin (); fi != field_sequence->end (); fi++)
	{
		DEBUG ("\ngenerate_field_nodes (field=%d)", *fi);
		pointer_nodes.clear ();

		// Parameters of generate_field_nodes ()

		// Parameter 1: DEST_VAR = variable to be dereferenced, i.e.
		// the pointee of VAR. Note that if DEST_VAR is a field
		// variable, then decl of csvarinfo of DEST_VAR is the decl of
		// root of the field.  We need to use get_decl(csvarinfo of
		// DEST_VAR) to get decl of field instead of decl of root.

		// Parameter 2: ideally this should be the typecasted type of
		// VAR.FIELD_SEQUENCE processed so far. 
		// E.g. in MEM[(new_type) VAR].offset, ideally parameter 2
		// should be new_type. But this information is not saved in
		// constraint_expr and VAR saves its original declared type
		// only. Therefore, we are sending type of VAR only as
		// parameter 2.

		// If pointer var type /= pointee type, and pointer var type /=
		// void *, then we typecast. In short, cases where only pointer
		// and pointee types matter, are handled.
		// However, if pointee variable type /= typecasted type /=
		// pointer var type, then we do not typecast. In short, cases
		// where typecasted type matters, are not handled.

		// FIXME:
		// Save typecasted type of VAR in constraint_expr and pass that
		// as parameter 2.

		// Typecasting needs to be done once. Then for the remaining
		// field sequence, correct field node is found connected via
		// gpt field edges.
		if (fi == field_sequence->begin ())
		{
			set<pt_node_index>::iterator di;
			// Call clone_and_update_subgraph() on every dest_node
			// so that each dest_node has a new copy of field
			// nodes.
			for (di = dest_nodes.begin (); di != dest_nodes.end (); di++)
				generate_field_nodes (value, *di, var_info->decl, *fi, pointer_nodes,
					value_excl_out_edges, incl_in_edges, incl_out_edges);
		}
		else
		{
			// Parameter 2 of generate_field_nodes() should be type
			// of pointer to field sequence processed so far. But
			// since now dest_nodes are already typecasted as per
			// VAR, we do not need to typecast any more.
			g_pt.get_field_nodes (dest_nodes, *fi, pointer_nodes,
				value_excl_out_edges, incl_in_edges, incl_out_edges);
			// If get_field_nodes() leaves some nodes unprocessed in dest_nodes
			if (dest_nodes.size ())
			{
				RESULT ("\nError: Field=%d in sequence not found on dest_nodes", *fi);
			}
		}

		dest_nodes = pointer_nodes;
	}
	#if DEBUG_CONTAINER
	DEBUG ("\npointer_nodes=");
	for (ni = pointer_nodes.begin (); ni != pointer_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
	#endif
}

/**
 * For typecasting case which needs on-the-fly field node generation, it does
 * the following:
 *
 * Adds newly generated nodes to VALUE and FRESH_NODES.
 *
 * Initializes on-the-fly created heap field variable nodes.  Here nodes to be
 * processed are those generated (H.F, H.G) where H is a fresh (already
 * existing as fresh) node and H.F and H.G are freshly added fields of a
 * typecast of H.

 * When H is typecasted, we do not change access name of H. We change only the
 * decl of node_name_type of access name of H. Changing access name of H would lead
 * to cloning of all typecasts of H into the desired type.  This would lead to
 * too much cloning and is redundant because all typecasts of H have the same
 * in-edges and differ only by their type.  Also, the clone of H would continue
 * to be pointed by H var from stack node, although its node_name_type will be H';
 * therefore, gPT in-edges of H and its clone will be exactly same.  Any way,
 * with/without cloning of H, in either case, we will have to explicitly add
 * field edges from H (or its clone) to H.F, H.G.
 *
 * input: value_excl_out_edges, incl_in_edges, incl_out_edges
 * output: field_nodes
 */

void points_to_analysis_fi::
generate_field_nodes (pt_node_set & value, 
	pt_node_index src_node, 
	tree src_pointer_type,
	label field, 
	set<pt_node_index> & field_nodes,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	DEBUG ("\ngenerate_field_nodes(src_node=%d,field=%d)", src_node, field);

	set<pt_node_index> field_nodes_temp;
	g_pt.get_field_nodes (src_node, src_pointer_type, field, field_nodes_temp,
		value_excl_out_edges, incl_in_edges, incl_out_edges);
	pt_fi_node::get_nodes_valid_at_point (field_nodes_temp, value.pt_nodes);
	// field_nodes.insert (field_nodes_temp.begin (), field_nodes_temp.end ());
	merge_set (field_nodes_temp, field_nodes);

	#if DEBUG_CONTAINER
	set<pt_node_index>::iterator fi;
	DEBUG ("\nsrc_node=%d,field=%d,get_field_nodes=", src_node, field);
	for (fi = field_nodes_temp.begin (); fi != field_nodes_temp.end (); fi++)
		DEBUG ("%d,", *fi);
	#endif

	// If field node is not present, or src_node is not connected to the
	// field nodes, or the src_node is connected to only those field_nodes
	// that are not valid in VALUE, then generate field nodes and create
	// gen_incl_in_field_edges.

	// When src_node is already connected to heap field nodes, it is
	// possible that the heap field nodes are not in VALUE. This is
	// possible when src_node=mymalloc where only root (void * type) is
	// assigned --- all heap fields (of all typecasts) are not added to
	// VALUE. Now, when void* heap has been typecasted, all heap field
	// nodes of the typecasted type need to be added to VALUE. This is also
	// possible when the field nodes are actually valid at some other
	// program point.

	if (!field_nodes_temp.size ())
	{
		// on-the-fly generated heap-field nodes will get included in VALUE
		// since we account for max_node_id here itself.
		int old_max_node_id = g_pt.get_max_node_id ();

		// Newly generated field edges are added to incl_in_edges/incl_out_edges
		g_pt.generate_field_nodes (src_node, src_pointer_type, field, field_nodes_temp, 
			incl_in_edges, incl_out_edges);
		// field_nodes.insert (field_nodes_temp.begin (), field_nodes_temp.end ());
		merge_set (field_nodes_temp, field_nodes);

		// Since newly generated nodes are added to set of valid nodes,
		// we do not need to consider incl_edges while calling
		// get_nodes_valid_at_point().
		initialize_fresh_ans (old_max_node_id, value);

		#if DEBUG_CONTAINER
		DEBUG ("\nsrc_node=%d,field=%d,generate_field_nodes=", src_node, field);
		for (fi = field_nodes_temp.begin (); fi != field_nodes_temp.end (); fi++)
			DEBUG ("%d,", *fi);
		#endif

		// It is an error if neither field nodes are found nor new
		// field edges are created. However, if our static analysis
		// erroneously points VAR to a different type, then neither
		// will be found, which is not an error in that case.
		if (!field_nodes_temp.size () && !incl_in_edges.size () && !incl_out_edges.size ())
			RESULT ("\nError: Field node neither found nor edge created for src_node=%d,field=%d",
			        src_node, field);
	}

	// If src_node already had field nodes of typecasted type, fetch
	// connected field nodes. This is wrong because src_node may be
	// connected to field nodes being used some where else and these may
	// not be clones of fresh nodes. Basically, on-the-fly field connection
	// should be made only with fresh field nodes.

	// if (!incl_in_field_edges.size ())
	// {
	//	if (!field_nodes_temp.size ())
	//		return;
	//
	//	// Nothing is to be done if any of the field_nodes is already
	//	// present in VALUE.
	//	for (fi = field_nodes_temp.begin (); fi != field_nodes_temp.end (); fi++)
	//		if (value.is_element (*fi))
	//		        return;
	//	
	//	// If none of the found field nodes is in VALUE, then add all
	//	// the connected field nodes to VALUE.
	//	
	//	// src_node has the typecasted type. Get all connected fields
	//	// of same type and add to VALUE (for in case they were not
	//	// present earlier).
	//	set<pt_node_index> all_field_nodes;
	//	g_pt.get_field_nodes (src_node, all_field_nodes);
	//	value.gen (all_field_nodes);
	//
	//	return;
	// }

	// If src_node does not have heap field nodes of typecasted type
	DEBUG ("\nNew field edges need to be added from src_node=%d", src_node);

//	// Clone gPT with field edges from src_node to fresh field nodes.
//	set<pt_node_index> ngen;
//	set<pt_node_index> nkill;
//	set<pt_node_index> empty_set;
//	def_stmt_set empty_ds;
//	map<pt_node_index, pt_node_index> clone;
//
//	#if DEBUG_CONTAINER
//	DEBUG ("\nValue before new field edges=");
//	value.print_value (NULL);
//	#endif
//	clone_and_update_subgraph (value, empty_set, empty_set, ASTERISK, empty_ds, empty_set, 
//		incl_in_field_edges, incl_out_field_edges, ngen, nkill, clone);
//
//	// Add newly cloned field nodes 
//	value.gen (ngen);
//	// TODO: check if this can ever happen. check if
//	// clone_and_update_subgraph() is called at out of block (rather than
//	// stmt) then no problem.
//
//	// Do not remove already existing gpt field edges from other typecasts
//	// of original heap because their aliases may get used when the
//	// original heap is typecasted again.
//
//	// Once connected, then retrieve the field nodes. No need to pass the
//	// typecasted type since now the type of original heap (src_node) has
//	// been transformed to the typecasted type.
//	// This may not be error: Actually in static analysis VAR may be
//	// wrongly made to point to a different type of heap which should not
//	// be typecasted, or VAR may be pointing to heap.n.64+64 (field heap
//	// node) but field typecasting has not been handled.

	if (!g_pt.get_field_nodes (src_node, field, field_nodes,
		value_excl_out_edges, incl_in_edges, incl_out_edges))
	{
		if (g_pt.is_heap_node (src_node))
		{
			RESULT ("\nError: Field=%d not found on heap src_node=%d even after typecast",
				field, src_node);
		}
		else
		{
			RESULT ("\nError:! Field=%d not found on stack src_node=%d even after typecast",
				field, src_node);
		}
		RESULT ("\nsrc_pointer_type=");
		print_node (dump_file, 0, src_pointer_type, 0);
	}
}

/**
 * Add to assignment_data of the CALL_SITE, mappings of actual parameters to
 * formal parameters of CALLED_FUNCTION. Then process them and delete the
 * mappings if the CALL_SITE is a function pointer call.
 */

void points_to_analysis_fi::
process_function_arguments (context<pt_node_set, variables> * src_context,
	basic_block call_site, 
	pt_node_set * value, 
	struct cgraph_node * called_function)
{
	FUNBEGIN ();

	DEBUG ("\nprocess_function_arguments()");

	if (!value)
	{
		RESULT ("\nError: Null value");
		RETURN_VOID ();
		// return;
	}

	// Functions process_function_arguments() and process_return_value()
	// cannot distinguish between argument and return-value mappings; for
	// example in the case of recursion, both lhs and rhs may be from the
	// same function. Therefore, for a call block we clear all assignment
	// mappings (for both direct and function pointer calls) before and
	// after adding new assignments.
	((block_information *)(call_site->aux))->erase_assignment_indices ();
	

#if DEBUG_CONTAINER
	DEBUG ("\nParsed data of bb=%d before adding arguments", call_site->index);
	program.print_parsed_data (call_site);
#endif

	// Create mappings on-the-fly
	struct cgraph_node * src_function = src_context->get_function ();
	// This function always fetches/creates a new map entry in assignment
	// pool.
	program.map_function_pointer_arguments (src_function, call_site, called_function);

	// Generate params of the called_function. These are required for
	// creating points-to pairs of the called function's parameters.
	DEBUG ("\ninserting params");
	generate_missing_params (*value, called_function);

	// We do not want to assume that lhs receiving variable and rhs
	// returned variable are scalars. Therefore, we call
	// process_parsed_data().
	process_parsed_data (src_context, call_site, value);

#if DEBUG_CONTAINER
	DEBUG ("\nParsed data of bb=%d after adding arguments", call_site->index);
	program.print_parsed_data (call_site);
#endif

	// Erase the mappings
	((block_information *)(call_site->aux))->erase_assignment_indices ();

	RETURN_VOID ();
}

/**
 * Add to assignment_data of the CALL_SITE, mapping of returned value of
 * CALLED_FUNCTION to the received value. Then process them and delete the
 * mappings if the CALL_SITE is a function pointer call.
 */

void points_to_analysis_fi::
process_return_value (context<pt_node_set, variables> * src_context, 
	basic_block call_site, 
	pt_node_set * value, 
	struct cgraph_node * called_function,
	bool to_kill)
{
	FUNBEGIN ();

	DEBUG ("\nprocess_return_values()");

	if (!value)
	{
		DEBUG ("\nNUll value");
		RETURN_VOID ();
		// return;
	}

	// Functions process_function_arguments() and process_return_value()
	// cannot distinguish between argument and return-value mappings; for
	// example in the case of recursion, both lhs and rhs may be from the
	// same function. Therefore, for a call block we clear all assignment
	// mappings (for both direct and function pointer calls) before and
	// after adding new assignments.
	((block_information *)(call_site->aux))->erase_assignment_indices ();

	// Create mappings on-the-fly
	struct cgraph_node * src_function = src_context->get_function ();
	basic_block end_block = program.get_end_block_of_function (called_function);
	// Find return blocks before end_block. There could be more than one
	// return blocks (e.g. test-cases/test31b.c).
	edge e;
	edge_iterator ei;
	FOR_EACH_EDGE (e, ei, end_block->preds)
	{
		basic_block return_block = e->src;
		DEBUG ("\nEnd block %d, return block %d", end_block->index, return_block->index);

		// This function always fetches/creates a new map entry in
		// assignment pool.
		program.map_return_value (call_site, src_function, return_block, called_function);
	}

	// We do not want to assume that lhs receiving variable and rhs
	// returned variable are scalars. Therefore, we call
	// process_parsed_data().
	// We set TO_KILL=false, so that the pointee of the receiving variable
	// (lhs) from the previous called function (via function pointer) is
	// not killed.
	process_parsed_data (src_context, call_site, value, to_kill);

#if DEBUG_CONTAINER
	DEBUG ("\nParsed data of bb=%d after adding return values", call_site->index);
	program.print_parsed_data (call_site);
#endif

	// Erase the mappings
	((block_information *)(call_site->aux))->erase_assignment_indices ();

	RETURN_VOID ();
}

void points_to_analysis_fi::
get_live_data (pt_node_set & out_value, 
	context<pt_node_set, variables> & current_context, 
	basic_block current_block,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<pt_node_index> & must_lhs_nodes)
{
	FUNBEGIN ();

	DEBUG ("\nget_live_data based on reachability");
	// The return variable is live at IN of return block and dead at IN and OUT of
	// END_BLOCK. We do not want to kill it at IN of END_BLOCK because
	// otherwise the caller function will get called context's value
	// without the return variable (because context's value is picked from
	// IN of END_BLOCK). We do not want to kill it at OUT of END_BLOCK
	// because whether or not is_value_same is true depends on OUT value. 

	unsigned int bt = ((block_information *)(current_block->aux))->get_block_type ();
	if (program.is_pred_of_end_block (current_block) || (bt & END_BLOCK))
		RETURN_VOID ();

#if DEBUG_CONTAINER
	DEBUG ("\nOUT_VALUE=");
	print_value (out_value);
#endif

	variables * out_liveness = get_live_out_value (current_context, current_block);
	if (!out_liveness)
	{
		RESULT ("\nError: out_liveness not found");
		return;
	}
#if DEBUG_CONTAINER
	DEBUG ("\nOUT_LIVENESS=");
	out_liveness->print_value (NULL);
#endif

	set<pt_node_index> live_var_nodes;
	set<pt_node_index> src_nids;
	src_nids.insert (g_pt.stack.get_node_id ());
	set<label>::iterator li;
	for (li = out_liveness->live_vars.begin (); 
		li != out_liveness->live_vars.end (); li++)
	{
		g_pt.get_destination_nodes (src_nids, *li, live_var_nodes, out_value.pt_nodes,
			value_excl_out_edges, incl_in_edges, incl_out_edges);
	}
	set<pt_node_index>::iterator ni;
#if DEBUG_CONTAINER
	DEBUG ("\nlive_var_nodes=");
	for (ni = live_var_nodes.begin (); ni != live_var_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif
	

	// FIXME: get_reachable_nodes() should consider value_excl_out_edges
	set<pt_node_index> empty_nodes; 
	DEBUG ("\nFetching live reachable nodes");
	set<pt_node_index> live_nodes =
		g_pt.get_reachable_nodes (live_var_nodes,
			empty_nodes, empty_nodes, incl_in_edges, incl_out_edges, out_value.pt_nodes);
#if DEBUG_CONTAINER
	DEBUG ("\nFetched live reachable nodes=");
	for (ni = out_value.pt_nodes.begin (); ni != out_value.pt_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif

	for (ni = out_value.pt_nodes.begin (); ni != out_value.pt_nodes.end (); ni++)
	{
		pt_node_index nid = *ni;
		if (live_nodes.find (nid) != live_nodes.end ())
			continue;
		if (g_pt.is_fresh_heap_node (nid))
			continue;
		// if (g_pt.is_heap_node (nid))
		//	continue;
		must_lhs_nodes.insert (nid);
	}

	#if INTERMEDIATE_RESULT
	RESULT ("\nFetch dead var nodes = ");
	set<pt_node_index>::iterator ki;
	for (ki = must_lhs_nodes.begin (); ki != must_lhs_nodes.end (); ki++)
		RESULT ("%d,", *ki);
	#endif
	
	RETURN_VOID ();
}

void points_to_analysis_fi::
get_live_data (pt_node_set & out_value, 
	context<pt_node_set, variables> & current_context, 
	basic_block current_block,
	set<pt_node_index> & must_lhs_nodes)
{
	FUNBEGIN ();

	DEBUG ("\nget_live_data");
	// The return variable is live at IN of return block and dead at IN and OUT of
	// END_BLOCK. We do not want to kill it at IN of END_BLOCK because
	// otherwise the caller function will get called context's value
	// without the return variable (because context's value is picked from
	// IN of END_BLOCK). We do not want to kill it at OUT of END_BLOCK
	// because whether or not is_value_same is true depends on OUT value. 

	unsigned int bt = ((block_information *)(current_block->aux))->get_block_type ();
	if (program.is_pred_of_end_block (current_block) || (bt & END_BLOCK))
		RETURN_VOID ();

	set<label> dead_variables = 
		get_dead_variables (out_value, current_context, current_block);
	// Killing pointer information of dead variables is like
	// killing must_lhs_nodes.

	// Killing a variable has the same effect as killing must-points-to
	// pairs of lhs variable.
	#if INTERMEDIATE_RESULT
	RESULT ("\nDead vars=");
	set<label>::iterator vi;
	for (vi = dead_variables.begin (); vi != dead_variables.end (); vi++)
	{
		csvarinfo_t var = program.cs_get_varinfo (*vi);
		RESULT ("%s(%d),", var->name, *vi);
	}
	#endif

	g_pt.get_nodes (dead_variables, out_value.pt_nodes, must_lhs_nodes);

	#if INTERMEDIATE_RESULT
	RESULT ("\nFetch dead var nodes = ");
	set<pt_node_index>::iterator ki;
	for (ki = must_lhs_nodes.begin (); ki != must_lhs_nodes.end (); ki++)
		RESULT ("%d,", *ki);
	#endif
	
	RETURN_VOID ();
}

variables * points_to_analysis_fi::
get_live_out_value (context<pt_node_set, variables> & current_context, 
	basic_block current_block)
{
	DEBUG ("\nget_live_out_value()");
	context<variables, pt_node_set> * dept_context = get_dependent_context (&current_context);
	if (!dept_context)
	{
		RESULT ("\nError: No dependent context to find dead pointers");
		return NULL;;
	}
	
	variables * out_liveness = dept_context->get_out_value (current_block);
	if (!out_liveness)
		RESULT ("\nError: Block %d is unreachable by dept_context", 
			current_block->index);
	return out_liveness;
}

set<unsigned int> points_to_analysis_fi::
get_callees_global_defs (struct cgraph_node * function)
{
	variables * callee_value = get_dependent_context_in_value (function);

	set<unsigned int> callees_global_defs = callee_value->get_callees_global_defs ();
	return callees_global_defs;
}

set<unsigned int> points_to_analysis_fi::
get_callees_global_uses (struct cgraph_node * function)
{
	variables * callee_value = get_dependent_context_in_value (function);

	set<unsigned int> callees_global_uses = callee_value->get_callees_global_uses ();
	return callees_global_uses;
}

/**
 * This function fetches dead variables from Lout of the CURRENT_BLOCK. Using
 * this set, it returns the pointer variables in VALUE which are dead. 
 */

set<variable_id> points_to_analysis_fi::
get_dead_variables (pt_node_set & value, 
	context<pt_node_set, variables> & current_context, 
	basic_block current_block)
{
	FUNBEGIN ();

	DEBUG ("\nget_dead_variables()");

	variables * out_liveness = get_live_out_value (current_context, current_block);

	struct cgraph_node * function = current_context.get_function ();
	set<variable_id> all_variables;
	program.get_local_variables (function, all_variables);

	inter_procedural_analysis<variables, pt_node_set> * dept_analysis = get_dependent_analysis ();

	set<variable_id> dead_variables;
	if (out_liveness)
		dead_variables = out_liveness->get_dead_variables (all_variables);
	else
		dead_variables = all_variables;

	RETURN (dead_variables);
	// return dead_variables;

	// The following would have been required if we would have deleted the
	// node also. But since we will retain the dead node and delete only
	// the out-edges of the dead node, we need not worry about a live
	// in-edge.

	// Remove from dead_variables i.e. mark those variables as live which
	// are pointed by a live pointer.
	// set<pt_node_index> dead_nodes = 
	//	g_pt.get_nodes (dead_variables, value.pt_nodes);
	// set<pt_node_index> dead_value_nodes = 
	//	g_pt.get_dead_value_nodes (dead_nodes, value.pt_nodes);

	// A variable is dead if it is structurally also dead i.e. all the
	// member fields of the structure to which it belongs are also dead.
	// get_structurally_dead_variables() should work on variables retained
	// by get_dead_value_variables() because the latter marks some new
	// variables as live (removes some from dead_variables) which should
	// further generate the liveness of their field offsets (remove more
	// variables from dead_value_variables).
	// g_pt.get_structurally_dead_variables (dead_value_nodes, value.pt_nodes);

	// return dead_value_nodes;
}


set<struct cgraph_node *> points_to_analysis_fi::
get_called_functions (context<pt_node_set, variables> & src_context, 
	basic_block call_site, 
	tree function_pointer)
{
	// RESULT ("\nFunction pointer:\n");
	// print_node (dump_file, "", SSAVAR (function_pointer), 0);
	struct cgraph_node * src_function = src_context.get_function ();
	csvarinfo_t fp_info = program.cs_get_vi_for_tree (function_pointer, call_site, src_function);
#if INTERMEDIATE_RESULT
	RESULT ("\nFunction pointer: %s(%d)", fp_info->name, fp_info->id);
#endif
		
	pt_node_set * in_value = src_context.get_in_value (call_site);
	set<label> called_function_ids = g_pt.get_pointees (fp_info->id, in_value->pt_nodes);
#if INTERMEDIATE_RESULT
	RESULT ("\nFunction pointees: ");
#endif
	set<struct cgraph_node *> called_functions;
	set<label>::iterator fi;
	for (fi = called_function_ids.begin (); fi != called_function_ids.end (); fi++)
	{
		csvarinfo_t called_function_info = VEC_index (csvarinfo_t, program.variable_data, *fi);
		if (!called_function_info)
		{
			RESULT ("\nError: Function pointer is not pointing to function");
			continue;
		}
		tree called_function_decl = called_function_info->decl;
		if (!called_function_decl || TREE_CODE (called_function_decl) != FUNCTION_DECL)
		{
			RESULT ("\nError: Function pointer is not pointing to function");
			continue;
		}
#if INTERMEDIATE_RESULT
		RESULT ("%s(%d), ", called_function_info->name, *fi);
#endif
		struct cgraph_node * called_function = cgraph_get_node (called_function_decl);
		// Ensure that the function is not a library function.
		if (DECL_STRUCT_FUNCTION (called_function->decl))
			called_functions.insert (called_function);
	}

	return called_functions;
}

/** 
 * Extracts the part of the value which is reachable from any function parameter
 * or a global variable. We should not extract argument reachable variables,
 * but parameter reachable variables since argument has no role to play in the
 * called function unless it is accessible from the parameter, in which case
 * parameter reachable variables will still suffice.
 *
 * @returns: int_bndry_nodes
 * @returns: caller_clone
 */

pt_node_set * points_to_analysis_fi::
extract_par_glob_reachable_value (struct cgraph_node * dest_function, 
	pt_node_set & value_in,
	set<pt_node_index> & int_bndry_nodes,
	map<pt_node_index, pt_node_index> & caller_clone)
{
	FUNBEGIN ();

//	pt_node_set * par_glob_reachable_value = boundary_value ();

	DEBUG ("\nextract_par_glob_reachable_value ()");
	set<unsigned int> par_glob_vars;

	set<unsigned int> function_parameters = 
		program.get_function_parameters (dest_function);
	merge_set (function_parameters, par_glob_vars);

	// FIXME: Exclude function names, otherwise local function pointers are
	// unnecessarily propagated since they point to global variables (i.e.
	// function names). There propagation is unnecessary because there is
	// no precision gain of replicating function name nodes.
	// FIXME: Exclude local function pointers. They do not get excluded
	// since their pointees (i.e. function names) are global variables.

	// Does not include heap locations
	// Note: In access based analysis we have included only global
	// variables and not heap variables. This is because the effect on
	// precision will be the same. In allocation site based analysis, we
	// have spuriously included both global and heap variables because
	// otherwise precision improvement on bzip2 is less .
	set<unsigned int> global_vars = program.get_global_variables ();
	merge_set (global_vars, par_glob_vars);

	// SIDE EFFECT ANALYSIS
	// Instead of passing all global reachable variables,
	// Pass all callees_global_uses and their reachable vars to the callee.
	//set<unsigned int> callees_global_uses = get_callees_global_uses (dest_function);
	//merge_set (callees_global_uses, par_glob_vars);
	// Pass all callees_global_defs but not vars reachable from it.
	//set<unsigned int> callees_global_defs = get_callees_global_defs (dest_function);
	//g_pt.get_nodes (callees_global_defs, value_in.pt_nodes, par_glob_reachable_nodes);
	// Since we do not want nodes reachable from callees_global_defs, we
	// need to exclude edges while computing clone_and_update_subgraph().
	// However, even when we ran SIDE_EFFECT_ANALYSIS=1 with nodes
	// reachable from both callees_global_uses and callees_global_defs,
	// still hmmer and h264ref (src-orig) did not terminate.


#if DEBUG_CONTAINER
	set<unsigned int>::iterator vi;
	DEBUG ("\nGlobals + function parameters of function %s:", cgraph_node_name (dest_function));
	for (vi = par_glob_vars.begin (); vi != par_glob_vars.end (); vi++)
		DEBUG ("%d, ", *vi);
#endif

	// This fetches nodes reachable from PAR_GLOB_VARS. It excludes fields
	// that are unreachable.
	set<pt_node_index> par_glob_reachable_nodes = 
		g_pt.get_reachable_nodes (par_glob_vars, value_in.pt_nodes);

	pt_node_set * par_glob_reachable_value = new pt_node_set;
	par_glob_reachable_value->gen (par_glob_reachable_nodes);
#if DEBUG_CONTAINER
	value_in.print_value (NULL);
	DEBUG ("\nPar_glob reachable nodes: ");
	for (ni = par_glob_reachable_nodes.begin (); ni != par_glob_reachable_nodes.end (); ni++)
		DEBUG ("%d, ", *ni);
#endif

	// Find nodes from PAR_GLOB_REACHABLE_NODES whose predecessor nodes are
	// in VALUE_IN and not in PAR_GLOB_REACHABLE_NODES. These are the nodes
	// whose APs will change.

	label l = 0;
	set<pt_node_index> empty_set;
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;

	// Include stack node in par_glob_reachable_nodes so that
	// int_bndry_nodes does not include nodes whose in-adjoining node is a
	// stack node.
	par_glob_reachable_nodes.insert (g_pt.stack.get_node_id ());
	int_bndry_nodes = g_pt.get_int_bndry_nodes (par_glob_reachable_nodes,
		empty_set, empty_set, l, empty_set, empty_edges, empty_edges, value_in.pt_nodes);

#if DEBUG_CONTAINER
	DEBUG ("\nint_bndry_nodes=");
	for (ni = int_bndry_nodes.begin (); ni != int_bndry_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif

	empty_set.clear ();
	empty_edges.clear ();
	def_stmt_set empty_ds;

	clone_and_update_subgraph (*par_glob_reachable_value, empty_set, empty_set,
		0, empty_ds, int_bndry_nodes, empty_edges, empty_edges, caller_clone); 

	// Kill from VALUE_IN all nodes in PAR_GLOB_VARS. 
	value_in.kill (par_glob_reachable_nodes);
	// value_in.gen (int_bndry_nodes);
	value_in.gen (g_pt.stack.get_node_id ());

#if DEBUG_CONTAINER
	DEBUG ("\nvalue left with par_glob-unreachable nodes");
	value_in.print_value (NULL);
	DEBUG ("\nExtracted graph with par_glob-unreachable nodes");
	par_glob_reachable_value->print_value (NULL);
#endif

	RETURN (par_glob_reachable_value);
	// return par_glob_reachable_value;
}

/** 
 * This function adds PAR_GLOB_UNREACHABLE_NODES and CALLEE_OUT_VALUE to
 * RESTORED_OUT_VALUE. It first transforms nodes in PAR_GLOB_UNREACHABLE_NODES
 * uses clones created by CALLER_CLONE and CALLEE_CLONE. Then it merges the
 * information into RESTORED_OUT_VALUE.
 */

map<pt_node_index, set<pt_node_index> > points_to_analysis_fi::
restore_par_glob_unreachable_nodes (set<pt_node_index> & callee_out_value,
	set<pt_node_index> & par_glob_unreachable_nodes,
	set<pt_node_index> & int_bndry_nodes,
	pt_node_set & restored_out_value,
	map<pt_node_index, pt_node_index> & caller_clone,
	map<pt_node_index, set<pt_node_index> > & callee_clone)
{
	FUNBEGIN ();

	DEBUG ("\nrestore_par_glob_unreachable_nodes");
#if DEBUG_CONTAINER
	DEBUG ("\npar_glob_unreachable_nodes=");
	set<pt_node_index>::iterator ni;
	for (ni = par_glob_unreachable_nodes.begin (); ni != par_glob_unreachable_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif

	// Merge caller_clone into callee_clone
	map<pt_node_index, pt_node_index>::iterator ci;
	#pragma omp parallel for
	for (ci = caller_clone.begin (); ci != caller_clone.end (); ci++)
		callee_clone[ci->first].insert (ci->second);

#if DEBUG_CONTAINER
	DEBUG ("\ncaller + callee clone");
	print_clone_map (callee_clone);
#endif

	// Prepare clone map of nodes relevant to call block
	map<pt_node_index, set<pt_node_index> > transitive_call_clone;

	// destination node, label, set of source nodes
	map<pt_node_index, map<label, set<pt_node_index> > > cloned_unreachable_in_edges;
	map<pt_node_index, map<label, set<pt_node_index> > > cloned_unreachable_out_edges;

	// Apply caller_callee_clone transitively on out-edges of
	// par_glob_unreachable_nodes to reach the transformed state (i.e. in
	// callee_out_value). 
	// FIXME: For efficiency, iterate over int_bndry_nodes and clone those
	// in-edges that are from par_glob_unreachable_nodes.
	set<pt_node_index>::iterator ui;
	for (ui = par_glob_unreachable_nodes.begin (); ui != par_glob_unreachable_nodes.end (); ui++)
	{
		pt_node_index uid = *ui;
		DEBUG ("\npar_glob_unreachable_node=%d", uid);
		if (uid == g_pt.stack.get_node_id ())
			continue;

		// Consider edges from UID to int_bndry_nodes.
		g_pt.clone_out_edges (uid, int_bndry_nodes, callee_clone, callee_out_value, 
			transitive_call_clone, cloned_unreachable_in_edges, cloned_unreachable_out_edges);
	}

	// Call clone_and_update_subgraph(). For this do the following.

	// Set restored_out_value as callee_out_value and
	// par_glob_unreachable_nodes. We will clone this using
	// clone_and_update_subgraph().
	set<pt_node_index> value_in_nodes;
	// value_in_nodes.insert (callee_out_value.begin (), callee_out_value.end ());
	merge_set (callee_out_value, value_in_nodes);
	// value_in_nodes.insert (par_glob_unreachable_nodes.begin (), par_glob_unreachable_nodes.end ());
	merge_set (par_glob_unreachable_nodes, value_in_nodes);
	restored_out_value.gen (value_in_nodes);

	set<pt_node_index> empty_set;
	def_stmt_set empty_ds;
	map<pt_node_index, pt_node_index> clone;

	// Perform cloning of destination nodes in unreachable edges 
	clone_and_update_subgraph (restored_out_value, empty_set, empty_set, 0, empty_ds, empty_set, 
		cloned_unreachable_in_edges, cloned_unreachable_out_edges, clone);

	DEBUG ("\ndone restoring unreachable nodes");

	#pragma omp parallel for
	for (ci = clone.begin (); ci != clone.end (); ci++)
		transitive_call_clone[ci->first].insert (ci->second);

	RETURN (transitive_call_clone);
	// return transitive_call_clone;
}


/** 
 * Since points-to analysis is a forwards analysis, we want to delete both the
 * local and formal parameters, since neither of them will be used by the
 * calling function. 
 */
 
void points_to_analysis_fi::
delete_local_variables (struct cgraph_node * src_function, 
	struct cgraph_node * function, 
	pt_node_set & out_value,
	void * new_clone)
{
	// FIXME: THIS context is not being called by a context of FUNCTION.
	// Instead of deleting locals of only FUNCTION, can we delete all
	// locals (even those other than FUNCTION) -- perhaps after checking
	// that there is no context of other that other function calling this
	// context..

	DEBUG ("\ndelete_local_variables");
	set<variable_id> local_variables;
	program.get_local_variables (function, local_variables);
	program.get_function_parameters (function, local_variables);

#if DEBUG_CONTAINER
	set<variable_id>::iterator vi;
	DEBUG ("\nLocal+parameter variables: ");
	for (vi = local_variables.begin (); vi != local_variables.end (); vi++)
		DEBUG ("%d, ", *vi);
#endif

	// Remove from OUT_VALUE all local_variable nodes. If any global
	// variable was pointing to a local or was being pointed by a local,
	// then such points-to pairs become absent in OUT_VALUE.
	// However, in removing the points-to pairs, it is important to retain
	// cloned globals (i.e. those not pointed by a local) in OUT_VALUE.
	// However, in the process of cloning, we will redundantly clone locals
	// too (i.e. those not pointed by a local).

	if (!new_clone)
	{
		RESULT ("\nError: new_clone is NULL");
		return;
	}
	map<pt_node_index, pt_node_index> * typecasted_new_clone = 
		(map<pt_node_index, pt_node_index> *) new_clone;
	delete_nodes_and_info (local_variables, out_value, *typecasted_new_clone);
}

/**
 * This function fetches nodes corresponding to VARIABLES in OUT_VALUE. It then
 * kills the out-points-to pairs of these nodes. This killing causes cloning of
 * the pointee nodes. It replaces these pointee nodes with their clones in
 * OUT_VALUE. Finally, it deletes nodes corresponding to VARIABLES from
 * OUT_VALUE. 
 * FIXME: This function does some redundant work in the following case: if node
 * corresponding to VARIABLES (which is to be any way deleted) is also a
 * pointee, then this function will redundantly clone that node too. 
 */

void points_to_analysis_fi::
delete_nodes_and_info (set<label> & variables, 
	pt_node_set & out_value,
	map<pt_node_index, pt_node_index> & new_clone)
{
	DEBUG ("\ndelete_nodes_and_info");
	// Delete pointer information of VARIABLES.
	// Killing a variable has the same effect as killing must-points-to
	// pairs of lhs variable.
	#if INTERMEDIATE_RESULT
	RESULT ("\nDead vars=");
	set<label>::iterator vi;
	for (vi = variables.begin (); vi != variables.end (); vi++)
	{
		csvarinfo_t var = program.cs_get_varinfo (*vi);
		RESULT ("%s(%d),", var->name, *vi);
	}
	#endif

	set<pt_node_index> value_excl_out_edges;
	g_pt.get_nodes (variables, out_value.pt_nodes, value_excl_out_edges);

	#if INTERMEDIATE_RESULT
	RESULT ("\nFetch dead var nodes = ");
	set<pt_node_index>::iterator ki;
	for (ki = value_excl_out_edges.begin (); ki != value_excl_out_edges.end (); ki++)
		RESULT ("%d,", *ki);
	#endif

	if (!value_excl_out_edges.size ())
		return;

	set<pt_node_index> empty_set;
	def_stmt_set empty_ds;
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;

	// Perform cloning of pointees of nodes corresponding to VARIABLES.
	clone_and_update_subgraph (out_value, empty_set, value_excl_out_edges, 
		ASTERISK, empty_ds, empty_set, empty_edges, empty_edges, new_clone);

	// Remove from OUT_VALUE all VARIABLE nodes. We need to fetch VARIABLE nodes
	// again because out_value now contains clones of VARIABLE nodes
	// (value_excl_out_edges) and ngen and nkill cannot be used to identify the
	// clones since they contain both value_excl_out_edges and global nodes.
	set<pt_node_index> dead_nodes;
	g_pt.get_nodes (variables, out_value.pt_nodes, dead_nodes);
	out_value.kill (dead_nodes);

	#if INTERMEDIATE_RESULT
	RESULT ("\nDelete local var nodes on return = ");
	for (ki = dead_nodes.begin (); ki != dead_nodes.end (); ki++)
		RESULT ("%d,", *ki);
	#endif
}

#if SUMM_STMT_CLOSURE == 0
void points_to_analysis_fi::
clone_and_update_subgraph (pt_node_set & value,
	set<pt_node_index> & value_excl_out_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	context<pt_node_set, variables> * current_context,
	bool to_gen_fresh_heap,
	bool to_append_clone)
{
	FUNBEGIN ();

	set<pt_node_index> empty_nodes;
	def_stmt_set empty_ds;
	map<pt_node_index, pt_node_index> clone;

	// Generate at IN. This is required if block is processed and a new
	// fresh node is generated on-the-fly. Then if IN is reprocessed, the
	// on-the-fly fresh node will not be found at IN. This was creating an
	// error in sjeng.
	if (to_gen_fresh_heap)
	{
		// Generate fresh_heap_nodes -- free available heap nodes
		generate_fresh_heap_nodes (value);
		// Add stack node -- required for cases where VALUE_OUT is empty and
		// fresh_heap_nodes added should have a root stack node.
		value.gen (g_pt.stack.get_node_id ());
	
		#if INTERMEDIATE_RESULT
		RESULT ("\nfresh_heap_nodes=");
		set<pt_node_index>::iterator ni;
		for (ni = g_pt.fresh_heap_nodes.begin (); ni != g_pt.fresh_heap_nodes.end (); ni++)
			RESULT ("%d,", *ni);
		#endif
	}

	clone_and_update_subgraph (value, empty_nodes, value_excl_out_edges, 
		ASTERISK, empty_ds, empty_nodes, incl_in_edges, incl_out_edges, clone);

	if (to_append_clone)
		append_clone_map (clone, *current_context);

	if (to_gen_fresh_heap)
	{
		// Generate fresh_heap_nodes -- free available heap nodes
		generate_fresh_heap_nodes (value);
		// Add stack node -- required for cases where VALUE_OUT is empty and
		// fresh_heap_nodes added should have a root stack node.
		value.gen (g_pt.stack.get_node_id ());
	
		#if INTERMEDIATE_RESULT
		RESULT ("\nfresh_heap_nodes=");
		set<pt_node_index>::iterator ni;
		for (ni = g_pt.fresh_heap_nodes.begin (); ni != g_pt.fresh_heap_nodes.end (); ni++)
			RESULT ("%d,", *ni);
		#endif
	}

	#if DEBUG_CONTAINER
	DEBUG ("\nValue before gen,kill");
	value.print_value (NULL);
	#endif

	RETURN_VOID ();
}
#endif

/**
 * out: ngen, nkill, clone
 */

void points_to_analysis_fi::
clone_and_update_subgraph (pt_node_set & value_in,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	def_stmt_set ds,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	map<pt_node_index, pt_node_index> & clone)
{
	FUNBEGIN ();

#if FILTER_EXISTING_EDGES
	g_pt.keep_new_edges (value_in.pt_nodes, must_lptr, lptr, l, rpte, incl_in_edges, incl_out_edges);
#endif

	// We do not initialize ginfo.AP' with ginfo.AP, but populate it
	// whenever access name of a gPT node in ginfo.AP changes.
	map<pt_node_index, access_name> new_pt_to_access_name; 
	map<pt_node_index, max_depth> new_pt_to_max_depth; 
	map<pt_node_index, pt_node_index> summ_cmpts_map; 

#if DEBUG_CONTAINER
	DEBUG ("\nOriginal g_ap");
	g_ap.print_graph (NULL);
#endif

	// Save OLD_MAX_NODE_ID. New nodes (i.e. clones) are then added by
	// CLONE_NODES().
	int old_max_node_id = g_pt.get_max_node_id ();

	// This is AINFO.REGION of the formulations
	map<pt_node_index, bool> affected_nodes;
	clone = clone_nodes (value_in, lptr, must_lptr, l, ds, rpte, incl_in_edges, incl_out_edges,
			new_pt_to_max_depth, summ_cmpts_map, new_pt_to_access_name, affected_nodes);

#if SUMM_K_CONSISTENT
	#if DEBUG_CONTAINER
	pt_access_map.print_summ_cmpts_map (summ_cmpts_map);
	#endif
#endif

	// Insert cloned edges between nodes of affected nodes and nodes in
	// VALUE_IN U RPTE
#if FI_REANALYSIS
	// Collect newly created edges with old source and old destination gPT
	// nodes i.e. gPT nodes with id <= OLD_MAX_NODE_ID.
#endif
	set<pair<pt_node_index, pt_node_index> > old_fs_new_fi_edges;
	clone_edges (clone, value_in, lptr, must_lptr, l, rpte, incl_in_edges, incl_out_edges, 
		affected_nodes, old_max_node_id, old_fs_new_fi_edges);

#if FI_REANALYSIS
	// Add contexts and blocks that need reanalysis because
	// old_fs_new_fi_edges are added.
	#if DEBUG_CONTAINER
	map<pt_node_index, pt_fi_node *>::iterator gni;
	DEBUG ("\nnodes<=id=%d = ", old_max_node_id);
	for (gni = g_pt.nodes.begin (); gni != g_pt.nodes.end (); gni++)
	{
		pt_node_index nid = gni->first;
		if (nid <= old_max_node_id)
			DEBUG ("%d,", nid);
	}
	DEBUG ("\nnodes>id=%d = ", old_max_node_id);
	for (gni = g_pt.nodes.begin (); gni != g_pt.nodes.end (); gni++)
	{
		pt_node_index nid = gni->first;
		if (nid > old_max_node_id)
			DEBUG ("%d,", nid);
	}
	#endif

	reanalyse_fi_dept_blocks (old_fs_new_fi_edges);
#endif

#if DEBUG_CONTAINER
	DEBUG ("\nclone_and_update_subgraph, g_pt");
	g_pt.print_graph (NULL);
#endif

#if CHECK_CONTAINER
//	pt_access_map.is_pt_access_map_okay (g_ap);
#endif

	set<pt_node_index> ngen;
	set<pt_node_index> nkill;

	// Set nkill to affected nodes
	// nkill.insert (affected_nodes.begin (), affected_nodes.end ());
	// merge_set (affected_nodes, nkill);
	map<pt_node_index, bool>::iterator ani;
	for (ani = affected_nodes.begin (); ani != affected_nodes.end (); ani++)
	{
		pt_node_index knid = ani->first;
		nkill.insert (knid);
	} 

	// Set ngen to cloned nodes of affected nodes
	DEBUG ("\nngen clones=");
	for (ani = affected_nodes.begin (); ani != affected_nodes.end (); ani++)
	{
		DEBUG ("clone[%d]=%d,", ani->first, clone[ani->first]);
		ngen.insert (clone[ani->first]);
	}

#if INTERMEDIATE_RESULT
	set<pt_node_index>::iterator ni;
	RESULT ("\nnkill=");
	for (ni = nkill.begin (); ni != nkill.end (); ni++)
		RESULT ("%d,", *ni);
	RESULT ("\nngen=");
	for (ni = ngen.begin (); ni != ngen.end (); ni++)
		RESULT ("%d,", *ni);
#endif

	// Replace pointees with their clones.
	value_in.kill (nkill);
	value_in.gen (ngen);

#if DEBUG_CONTAINER
	for (ni = nkill.begin (); ni != nkill.end (); ni++)
		pt_access_map.print_submap (*ni, g_ap);
	for (ni = ngen.begin (); ni != ngen.end (); ni++)
		pt_access_map.print_submap (*ni, g_ap);
#endif

	DEBUG ("\nend of clone_and_update_subgraph()");

	RETURN_VOID ();
}

map<pt_node_index, pt_node_index> points_to_analysis_fi::
clone_nodes (pt_node_set & value_in,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	def_stmt_set ds,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	map<pt_node_index, max_depth> & new_pt_to_max_depth, 
	map<pt_node_index, pt_node_index> & summ_cmpts_map, 
	map<pt_node_index, access_name> & new_pt_to_access_name,
	map<pt_node_index, bool> & affected_nodes)
{
	FUNBEGIN ();

	DEBUG ("\nclone_nodes ()");

	set<pt_node_index> nvisit;
	set<pt_node_index> nreach;
	set<pt_node_index> ext_bndry;

	// Compute NVISIT.
	nvisit = g_pt.find_visit_nodes (lptr, must_lptr, l, rpte, 
		incl_in_edges, incl_out_edges, value_in.pt_nodes);

#if DEBUG_CONTAINER
	DEBUG ("\nnvisit=");
	set<pt_node_index>::iterator ni;
	for (ni = nvisit.begin (); ni != nvisit.end (); ni++)
		DEBUG ("%d,", *ni);
#endif

	affected_nodes = find_new_ans_and_affected_region (nvisit, value_in,  
		lptr, must_lptr, l, ds, rpte, incl_in_edges, incl_out_edges,
		new_pt_to_max_depth, summ_cmpts_map, new_pt_to_access_name);

#if DEBUG_CONTAINER
	DEBUG ("\nUpdated new_pt_to_access_name");
	pt_access_map.print_map (new_pt_to_access_name);
	DEBUG ("\nUpdated g_ap");
	g_ap.print_graph (NULL);
	DEBUG ("\nAffected nodes=");
	map<pt_node_index, bool>::iterator ai;
	for (ai = affected_nodes.begin (); ai != affected_nodes.end (); ai++)
		DEBUG ("%d,", ai->first);
#endif

	// Create a map of affected_nodes to their clones.
	map<pt_node_index, pt_node_index> clone = 
		get_node_clones (affected_nodes, new_pt_to_max_depth, summ_cmpts_map, new_pt_to_access_name);

	RETURN (clone);
	// return clone;
}

map<pt_node_index, pt_node_index> points_to_analysis_fi::
get_node_clones (map<pt_node_index, bool> & affected_nodes,
	map<pt_node_index, max_depth> & new_pt_to_max_depth,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	FUNBEGIN ();

	DEBUG ("\nget_node_clones()");

	map<pt_node_index, pt_node_index> clone;
	pt_node_index stack_id = g_pt.stack.get_node_id ();

	map<pt_node_index, bool>::iterator ani;
	for (ani = affected_nodes.begin (); ani != affected_nodes.end (); ani++)
	{
		pt_node_index anid = ani->first;
		DEBUG ("\nget_node_clone (anid=%d)", anid);

		set<pt_node_index> empty_set;
		access_name * new_access_name = 
			pt_access_map.get_access_name (anid, empty_set, summ_cmpts_map, new_pt_to_access_name);
		access_name new_an;
		if (!new_access_name)
			new_access_name = &new_an;
#if DEBUG_CONTAINER
		DEBUG ("\nnew_ap of pt_nid=%d=", anid);
		new_access_name->print (NULL);
#endif

		pt_node_index cid = pt_access_map.find_clone (*new_access_name);
		DEBUG ("\nfind_clone(anid=%d)=%d", anid, cid);

		if (!cid)
		{
#if SUMM_K_CONSISTENT
			max_depth new_max_depth = 
				pt_access_map.get_max_depth (anid, empty_set, new_pt_to_max_depth);
#else
			max_depth new_max_depth = 0;
#endif
			cid = generate_clone (*new_access_name, new_max_depth);
			DEBUG ("\ngenerate_clone(anid=%d)=%d", anid, cid);
		}

		DEBUG ("\nSetting existing clone[anid=%d]=cid=%d", anid, cid);
		clone[anid] = cid;
	}

#if DEBUG_CONTAINER
	DEBUG ("\nClones=");
	map<pt_node_index, pt_node_index>::iterator ci;
	for (ci = clone.begin (); ci != clone.end (); ci++)
		DEBUG ("(%d,%d),", ci->first, ci->second);
#endif

	RETURN (clone);
	// return clone;
}

pt_node_index points_to_analysis_fi::
generate_clone (access_name & new_access_name, max_depth new_max_depth)
{
	/*
	// This function creates a new g_pt node as clone of nid. However,
	// before creating a new node, it matches if new_pt_to_access_name[nid]
	// has already been generated in clone[].  This could happen if
	// value_in={z->x->a,y->x->b,a,b} and statement is x=&a.  Then a
	// pointed by z.* and x gets pointed by z.*,y.*,x and the lone a also
	// gets pointed by z.*,y.*.x i.e. new_pt_to_access_name becomes same.

	// However, we now we update access_name_to_pt immediately after
	// creating a new clone node; therefore,
	// pt_access_map::find_matching_pt() will be able to find if the access
	// name has already been created in clone[]. so the following is not
	// required.

	pt_node_index cid = 0;
	bool is_new_clone_present = false;
	map<pt_node_index, pt_node_index>::iterator ci;
	for (ci = clone.begin (); ci != clone.end (); ci++)
	{
		pt_node_index pnid = ci->first;
		access_name p_access_name = 
			pt_access_map.get_access_name (pnid, empty_set, new_pt_to_access_name);
		if (n_access_name.is_same (p_access_name))
		{
			is_new_clone_present = true;
			cid = clone[pnid];
			DEBUG ("\nReusing clone[pnid=%d]=cid=%d for nid=%d",
				pnid, cid, nid);
			break;
		}
	}

	if (!is_new_clone_present)
	*/	

	pt_fi_node * new_clone = new pt_fi_node (g_pt.nodes);
	pt_node_index cid = new_clone->get_node_id ();
	DEBUG ("\ngenerated clone=%d", cid);
#if SUMM_K_CONSISTENT
	pt_access_map.set_max_depth (cid, new_max_depth);
	DEBUG ("\nmax_depth=%d", new_max_depth);
	if (new_max_depth == SUMM_K_CONSISTENT)
		new_clone->set_is_summary_node ();
#endif
	pt_access_map.set_access_name (cid, new_access_name);

	return cid;
}

/**
 * This function returns clone of the nodes which are valid at VALUE_IN and
 * whose clones are not unused-heap-nodes. CLONED_NODES is the set of
 * AFFECTED_NODES i.e. nodes whose clone is saved in CLONE.
 */

pt_fi_node * points_to_analysis_fi::
get_valid_clone (pt_node_index nid,
	set<pt_node_index> & value_in,
	map<pt_node_index, bool> & cloned_nodes,
	map<pt_node_index, pt_node_index> & clone)
{
	FUNBEGIN ();

	DEBUG ("\nget_valid_clone(nid=%d)", nid);

	if (!pt_fi_node::is_node_valid_at_point (nid, value_in))
	{
		DEBUG ("\nnid=%d not valid at point", nid);
		RETURN (NULL);
		// return NULL;
	}

	pt_fi_node * clone_n = NULL;
	pt_node_index clone_nid = 0;

	// If the node has not been cloned, then the node is a clone of itself.
	if (cloned_nodes.find (nid) != cloned_nodes.end ())
		clone_nid = clone[nid];
	else
		clone_nid = nid;

	clone_n = g_pt.nodes[clone_nid];
	DEBUG ("\nclone(nid=%d)=%d", nid, clone_nid);

	if (is_unused_heap_node (clone_nid))
	{
		// An edge to a unused-heap-node can never get added. This is
		// because then access path of the unused-heap-node would not
		// remain empty.

		// get_valid_clone() may return NULL for fresh heap nodes.
		// However this is not an error: when we deal with a group of
		// statements, stmt 1 may point to a fresh heap node, stmt 2
		// may have an out-edge from the fresh heap node, stmt 3 may
		// kill the pointer to the fresh heap node. Overall, stmt 2
		// causes out-edge from fresh heap node.

		DEBUG ("\nDont add edge from fresh-heap-node=%d", clone_nid);
		RETURN (NULL);
		// return NULL;
	}
	DEBUG ("\nget_valid_clone(nid=%d)=%d", nid, clone_nid);

	RETURN (clone_n);
	// return clone_n;
}

/**
 * AFFECTED_NODES : nodes whose APs change due to Egen and Ekill or
 * NEW_IN_EDGES. These nodes and are in VALUE_IN or a newly created at the
 * program point.
 * output: NEW_PT_TO_ACCESS_NAME
 * @return AFFECTED_NODES
 */

map<pt_node_index, bool> points_to_analysis_fi::
find_new_ans_and_affected_region (set<pt_node_index> & nvisit,
	pt_node_set & value_in,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	def_stmt_set ds,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	map<pt_node_index, max_depth> & new_pt_to_max_depth, 
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	FUNBEGIN ();

	tot_update_points++;
	// Old pointees of l-value of left hand side + r-value of right hand side
	tot_stmttouch += nvisit.size ();

	// Compute NREACH
	set<pt_node_index> nreach;
#if RESET_ACCESS_NAMES
	nreach = g_pt.get_reachable_nodes (nvisit, 
		lptr, rpte, incl_in_edges, incl_out_edges, value_in.pt_nodes);
#endif

	tot_potaffreg += nreach.size ();

#if DEBUG_CONTAINER
	DEBUG ("\nnreach=");
	set<pt_node_index>::iterator ni;
	for (ni = nreach.begin (); ni != nreach.end (); ni++)
		DEBUG ("%d,", *ni);
#endif

	// Compute EXT_BNDRY of NREACH
	set<pt_node_index> ext_bndry;
#if RESET_ACCESS_NAMES
	ext_bndry = g_pt.get_ext_bndry_nodes (nreach, 
		lptr, must_lptr, l, rpte, incl_in_edges, incl_out_edges, value_in.pt_nodes); 
#endif

#if DEBUG_CONTAINER
	DEBUG ("\next_bndry=");
	for (ni = ext_bndry.begin (); ni != ext_bndry.end (); ni++)
		DEBUG ("%d,", *ni);
	DEBUG ("\nvalid nodes=");
	value_in.print_value (NULL);
#endif

	// NVISIT does not include NREACH (nodes reachable from NVISIT). It is
	// more efficient to find max_depth and access name starting from
	// NVISIT and then moving in BFS, as compared to covering all nodes in
	// NREACH in random order.

	set<set<pt_node_index> > summ_cmpts;
#if SUMM_K_CONSISTENT
	// Find max_depth and summ_cmpts using Ekill and Egen
	find_new_summ_cmpts (nvisit, ext_bndry, value_in,  
		lptr, must_lptr, l, rpte, incl_in_edges,
		new_pt_to_max_depth, summ_cmpts);

	pt_access_map.compute_summ_cmpts_map (summ_cmpts, summ_cmpts_map);

	#if DEBUG_CONTAINER
	DEBUG ("\nfind_new_ans_and_affected_region, g_pt");
	g_pt.print_graph (NULL);
	DEBUG ("\nnew_pt_to_max_depth:");
	pt_access_map.print_max_depth_map (new_pt_to_max_depth);
	pt_access_map.print_summ_cmpts (summ_cmpts);
	pt_access_map.print_summ_cmpts_map (summ_cmpts_map);
	#endif
#endif

	// Find nodes whose APs change due to Ekill and Egen
#if PULL_ACCESS_NAMES
#if PULL_BOUNDARY
	set<pt_node_index> empty_set;
	pull_new_ans (nvisit, ext_bndry, value_in,  
		lptr, must_lptr, l, ds, rpte, incl_in_edges, incl_out_edges,
		empty_set, summ_cmpts, summ_cmpts_map, new_pt_to_access_name);
#else
	if (nreach.size () >= PULL_REV_PO)
	{
		FILE * stat_file = fopen (STAT_FILE, "a");
		fprintf (stat_file, "nreach=%d, ", nreach.size ());
		fclose (stat_file);
		pull_new_ans_rev_po (nreach, ext_bndry, value_in,  
			lptr, must_lptr, l, ds, rpte, incl_in_edges, incl_out_edges,
			summ_cmpts, summ_cmpts_map, new_pt_to_access_name);
	}
	else
		pull_new_ans (nvisit, ext_bndry, value_in,  
			lptr, must_lptr, l, ds, rpte, incl_in_edges, incl_out_edges,
			summ_cmpts, summ_cmpts_map, new_pt_to_access_name);
#endif

#else
#if PUSH_FROM_ROOT
	// Push from root node in breadth first order
	pt_node_index stack_nid = g_pt.stack.get_node_id ();
	push_an_subgraph (stack_nid, ext_bndry, nreach, value_in,  
		lptr, must_lptr, l, ds, rpte, incl_out_edges,
		summ_cmpts, summ_cmpts_map, new_pt_to_access_name);
#else
	// Push new ANs from ext_bndry in breadth first order
	push_new_an_subgraph (ext_bndry, ext_bndry, nreach, value_in,  
		lptr, must_lptr, l, ds, rpte, incl_out_edges,
		summ_cmpts, summ_cmpts_map, new_pt_to_access_name);
#endif

#endif

#if DEBUG_CONTAINER
	DEBUG ("\nnew_pt_to_access_name=");
	pt_access_map.print_map (new_pt_to_access_name);
#endif

	map<pt_node_index, bool> affected_nodes;
	pt_access_map.find_affected_region (nreach, summ_cmpts_map, new_pt_to_access_name,
		affected_nodes);

	tot_finalaffreg += affected_nodes.size ();

	RETURN (affected_nodes);
	// return affected_nodes;
}

/**
 * This function computes NEW_PT_TO_MAX_DEPTH of the affected nodes. Here
 * NVISIT is already in VALUE_IN.
 * output: NEW_PT_TO_MAX_DEPTH
 */

#if SUMM_K_CONSISTENT
void points_to_analysis_fi::
find_new_summ_cmpts (set<pt_node_index> & nvisit,
	set<pt_node_index> & ext_bndry,
	pt_node_set & value_in,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, max_depth> & new_pt_to_max_depth,
	set<set<pt_node_index> > & summ_cmpts)
{
	set<pt_node_index>::iterator vni;
#if DEBUG_CONTAINER
	DEBUG ("\nfind_new_summ_cmpts=");
	for (vni = nvisit.begin (); vni != nvisit.end (); vni++)
		DEBUG ("%d,", *vni);
#endif

	set<pt_node_index> succ_nodes;

	for (vni = nvisit.begin (); vni != nvisit.end (); vni++)
	{
		pt_node_index vnid = *vni;
		DEBUG ("\nfind_new_summ_cmpts(node=%d)", vnid);

		#if CHECK_CONTAINER
		if (!pt_fi_node::is_node_valid_at_point (vnid, value_in.pt_nodes))
		{
			label v = g_pt.get_node_name (vnid);
			csvarinfo_t var = VEC_index (csvarinfo_t, program.variable_data, v);
			RESULT ("\nError: nvisit node=%d, var=%s(%d) not valid", vnid, var->name, v);
			continue;
		}
		#endif

		// Do not uncomment the following. Even if a node has been
		// considered, it should be reconsidered if the max_depth of
		// its predecessors have changed. We stop the recursion only
		// when the max_depth does not change.
		// Do not consider PNID if it has already been considered.
		// if (affected_nodes.find (vnid) != affected_nodes.end ())
		//	continue;

		#if CHECK_CONTAINER
		if (g_pt.nodes.find (vnid) == g_pt.nodes.end ())
		{
			RESULT ("\nError: pt-node=%d not found", vnid);
			continue;
		}
		#endif

		pt_fi_node * pn = g_pt.nodes[vnid];

		// Compute new max_depth of PNID due to Egen and Ekill
		bool has_max_depth_changed = 
			compute_new_summ_cmpts (*pn, ext_bndry, value_in, lptr, must_lptr, l, rpte, 
				incl_in_edges, new_pt_to_max_depth, summ_cmpts);
		DEBUG ("\nnode=%d, new_max_depth=%d, has_max_depth_changed=%d", 
			vnid, new_pt_to_max_depth[vnid], has_max_depth_changed);

		// Process successors of PN only if max_depth of PN has
		// changed; no need to process successors if only summ_cmpt
		// involving PN has changed. This is because if the max_depth
		// has not changed, then max_depth of successors will not
		// change because of PN; if summ_cmpt of PN has changed, then
		// merge_summ_cmpts() has automatically updated summ_cmpt for
		// successors (which are already with summ_cmpt of PN). 
		if (!has_max_depth_changed)
			continue;

		// HAS_MAX_DEPTH_CHANGED is the difference between two
		// iterations of the fixed point computation of
		// NEW_PT_TO_MAX_DEPTH. A node is in AFFECTED_NODE if its
		// original max_depth in PT_TO_MAX_DEPTH is different from its
		// max_depth in NEW_PT_TO_MAX_DEPTH.  Therefore, AFFECTED_NODES
		// needs to be computed after fixed point value of
		// NEW_PT_TO_MAX_DEPTH has been computed.

		// affected_nodes.insert (vnid);

		// Get successors of new_affected_nodes using E, Egen, and incl_in_edges.
		// This is different from formulations in the following sense:
		// The formulations cover all nodes reachable from Ekill and
		// Egen via Erel (which is (edges-Ekill)UEgen) and
		// incl_in_edges. Here we cover all nodes reachable from Ekill
		// and Egen via Egen and incl_in_edges. But this will not
		// include any spurious node in the processing since a node
		// reachable via Ekill already gets covered by default.
		pn->get_out_adj_nodes (lptr, rpte, incl_in_edges, succ_nodes, value_in.pt_nodes);
	}

	// Breadth-first

#if DEBUG_CONTAINER
	DEBUG ("\nfind_new_summ_cmpts succ =");
	for (vni = succ_nodes.begin (); vni != succ_nodes.end (); vni++)
		DEBUG ("%d,", *vni);
#endif

	if (succ_nodes.size ())
		find_new_summ_cmpts (succ_nodes, ext_bndry, value_in, 
			lptr, must_lptr, l, rpte, incl_in_edges, 
			new_pt_to_max_depth, summ_cmpts);
}
#endif

void points_to_analysis_fi::
dfs_nodes_rev_po (pt_node_index pt_nid,
	set<pt_node_index> & visited,
	list<pt_node_index> & nodes_rev_po,
	pt_node_set & value_in,
	set<pt_node_index> & nreach,
	set<pt_node_index> & lptr,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges)
{
	if (visited.find (pt_nid) != visited.end ())
		return;
	visited.insert (pt_nid);

	if (!pt_fi_node::is_node_valid_at_point (pt_nid, value_in.pt_nodes))
		return;

	pt_fi_node * pn = g_pt.nodes[pt_nid];
	set<pt_node_index> succ_nodes;
	pn->get_out_adj_nodes (lptr, rpte, incl_in_edges, incl_out_edges,
			succ_nodes, value_in.pt_nodes);
	set<pt_node_index>::iterator si;
	for (si = succ_nodes.begin (); si != succ_nodes.end (); si++)
	{
		pt_node_index snid = *si;
		dfs_nodes_rev_po (snid, visited, nodes_rev_po, value_in, nreach, 
			lptr, rpte, incl_in_edges, incl_out_edges);
	}
	
	if (nreach.find (pt_nid) != nreach.end ())
		nodes_rev_po.push_front (pt_nid);
}

pt_node_index points_to_analysis_fi::
get_next_node (map<unsigned int, pt_node_index> & nreach_worklist)
{
	DEBUG ("\nget_next_node ");
	map<unsigned int, pt_node_index>::iterator ni;
	for (ni = nreach_worklist.begin (); ni != nreach_worklist.end (); ni++)
	{
		pt_node_index nid = ni->second;
		if (nid)
		{
			nreach_worklist.erase (ni);
			DEBUG ("nid=%d", nid);
			return nid;
		}
	}
	DEBUG ("nid=0");
	return 0;
}

/**
 * This function computes NEW_PT_TO_ACCESS_NAME of the affected nodes. Here
 * NREACH is already in VALUE_IN.
 * output: NEW_PT_TO_ACCESS_NAME
 */

void points_to_analysis_fi::
pull_new_ans_rev_po (set<pt_node_index> & nreach,
	set<pt_node_index> & ext_bndry,
	pt_node_set & value_in,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	def_stmt_set ds,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<set<pt_node_index> > & summ_cmpts,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	RESULT ("\npull_new_ans_rev_po()");

	pt_node_index stack_nid = g_pt.stack.get_node_id ();
	set<pt_node_index> empty_vis_nodes;
	list<pt_node_index> nodes_rev_po_list;
	dfs_nodes_rev_po (stack_nid, empty_vis_nodes, nodes_rev_po_list,
		value_in, nreach, lptr, rpte, incl_in_edges, incl_out_edges);

	list<pt_node_index>::iterator noi;
#if DEBUG_CONTAINER
	DEBUG ("\nnodes_rev_po_list=");
	for (noi = nodes_rev_po_list.begin (); noi != nodes_rev_po_list.end  (); noi++)
		DEBUG ("%d,", *noi);
#endif
	
	map<unsigned int, pt_node_index> nreach_worklist;
	map<pt_node_index, unsigned int> nodes_rev_po;
	unsigned int order;
	DEBUG ("\n(nodes,order)=");
	for (noi = nodes_rev_po_list.begin (), order = 0; 
		noi != nodes_rev_po_list.end (); 
		noi++, order++)
	{
		pt_node_index nid = *noi;
		DEBUG ("(%d,%d),", nid, order);
		nreach_worklist[order] = nid;
		nodes_rev_po[nid] = order;
	}
	
	pull_new_ans_rev_po (nreach_worklist, nodes_rev_po, ext_bndry, value_in, 
		lptr, must_lptr, l, ds, rpte, incl_in_edges, incl_out_edges,
		summ_cmpts, summ_cmpts_map, new_pt_to_access_name);
}

void points_to_analysis_fi::
pull_new_ans_rev_po (map<unsigned int, pt_node_index> & nreach_worklist,
	map<pt_node_index, unsigned int> & nodes_rev_po,
	set<pt_node_index> & ext_bndry,
	pt_node_set & value_in,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	def_stmt_set ds,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<set<pt_node_index> > & summ_cmpts,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	pt_node_index vnid = 0;
	while (vnid = get_next_node (nreach_worklist))
	{
		DEBUG ("\npull_new_ans(node=%d)", vnid);

		#if CHECK_CONTAINER
		if (!pt_fi_node::is_node_valid_at_point (vnid, value_in.pt_nodes))
		{
			label v = g_pt.get_node_name (vnid);
			csvarinfo_t var = VEC_index (csvarinfo_t, program.variable_data, v);
			RESULT ("\nError: nvisit node=%d, var=%s(%d) not valid", vnid, var->name, v);
			continue;
		}
		#endif

		#if CHECK_CONTAINER
		if (g_pt.nodes.find (vnid) == g_pt.nodes.end ())
		{
			RESULT ("\nError: pt-node=%d not found", vnid);
			continue;
		}
		#endif

		pt_fi_node * pn = g_pt.nodes[vnid];

		// Compute new APs of PNID due to Egen and Ekill
		set<pt_node_index> empty_set;
		bool has_changed = 
			pull_new_an (*pn, ext_bndry, value_in, lptr, must_lptr, l, ds, rpte, 
				incl_in_edges, empty_set, summ_cmpts_map, new_pt_to_access_name);
		DEBUG ("\nnode=%d, has_changed=%d", vnid, has_changed);

		if (!has_changed)
			continue;

		set<pt_node_index> succ_nodes;
		pn->get_out_adj_nodes (lptr, rpte, incl_in_edges, incl_out_edges,
			succ_nodes, value_in.pt_nodes);

#if DEBUG_CONTAINER
		DEBUG ("\npull_new_ans succ =");
		set<pt_node_index>::iterator vni;
		for (vni = succ_nodes.begin (); vni != succ_nodes.end (); vni++)
			DEBUG ("%d,", *vni);
#endif
	
		set<pt_node_index>::iterator si;
		for (si = succ_nodes.begin (); si != succ_nodes.end (); si++)
		{
			pt_node_index snid = *si;
			unsigned int order = nodes_rev_po[snid];
			DEBUG("\nSet nreach_worklist[order=%d]=snid=%d", order, snid);
			nreach_worklist[order] = snid;
		}
	}
}


/**
 * This function computes NEW_PT_TO_ACCESS_NAME of the affected nodes. Here
 * NVISIT is already in VALUE_IN.
 * output: NEW_PT_TO_ACCESS_NAME
 */

void points_to_analysis_fi::
pull_new_ans (set<pt_node_index> & nvisit,
	set<pt_node_index> & ext_bndry,
	pt_node_set & value_in,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	def_stmt_set ds,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<pt_node_index> & ext_bndry_pulled_nodes,
	set<set<pt_node_index> > & summ_cmpts,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	FUNBEGIN ();

	set<pt_node_index>::iterator vni;
#if DEBUG_CONTAINER
	DEBUG ("\npull_new_ans=");
	for (vni = nvisit.begin (); vni != nvisit.end (); vni++)
		DEBUG ("%d,", *vni);
#endif

	set<pt_node_index> changed_nvisit;
	set<pt_node_index> succ_nodes;

	for (vni = nvisit.begin (); vni != nvisit.end (); vni++)
	{
		pt_node_index vnid = *vni;
		DEBUG ("\npull_new_ans(node=%d)", vnid);

		#if CHECK_CONTAINER
		if (!pt_fi_node::is_node_valid_at_point (vnid, value_in.pt_nodes))
		{
			label v = g_pt.get_node_name (vnid);
			csvarinfo_t var = VEC_index (csvarinfo_t, program.variable_data, v);
			RESULT ("\nError: nvisit node=%d, var=%s(%d) not valid", vnid, var->name, v);
			continue;
		}
		#endif

		// Do not uncomment the following. Even if a node has been
		// considered, it should be reconsidered if the APs of its
		// predecessors have changed. We stop the recursion only when
		// the APs do not change.
		// Do not consider PNID if it has already been considered.
		// if (affected_nodes.find (vnid) != affected_nodes.end ())
		//	continue;

		#if CHECK_CONTAINER
		if (g_pt.nodes.find (vnid) == g_pt.nodes.end ())
		{
			RESULT ("\nError: pt-node=%d not found", vnid);
			continue;
		}
		#endif

		pt_fi_node * pn = g_pt.nodes[vnid];

		// Compute new APs of PNID due to Egen and Ekill
		bool has_changed = 
			pull_new_an (*pn, ext_bndry, value_in, lptr, must_lptr, l, ds, rpte, incl_in_edges, 
				ext_bndry_pulled_nodes, summ_cmpts_map, new_pt_to_access_name);
		DEBUG ("\nnode=%d, has_changed=%d", vnid, has_changed);

		if (!has_changed)
			continue;

		// HAS_CHANGED is the difference between two iterations of the
		// fixed point computation of NEW_PT_TO_ACCESS_NAME. A node is
		// in AFFECTED_NODE if its original AP in PT_TO_ACCESS_NAME is
		// different from its AP in NEW_PT_TO_ACCESS_NAME. Therefore,
		// AFFECTED_NODES needs to be computed after fixed point value
		// of NEW_PT_TO_ACCESS_NAME has been computed.

		// affected_nodes.insert (vnid);

		// Get successors of new_affected_nodes using E, Egen, and incl_in_edges.
		// This is different from formulations in the following sense:
		// The formulations cover all nodes reachable from Ekill and
		// Egen via Erel (which is (edges-Ekill)UEgen) and
		// incl_in_edges. Here we cover all nodes reachable from Ekill
		// and Egen via Egen and incl_in_edges. But this will not
		// include any spurious node in the processing since a node
		// reachable via Ekill already gets covered by default.
#if SUMM_K_CONSISTENT
		// If PN is in a summ_cmpt then all nodes in the summ_cmpt should be reprocessed.
		pt_node_index pnid = pn->get_node_id ();
		if (summ_cmpts_map.find (pnid) != summ_cmpts_map.end ())
		{
			set<pt_node_index> summ_cmpt_nodes = pt_access_map.get_summ_cmpt (pnid, summ_cmpts);
			// succ_nodes.insert (summ_cmpt_nodes.begin (), summ_cmpt_nodes.end ());
			merge_set (summ_cmpt_nodes, succ_nodes);
		}
		else	
			pn->get_out_adj_nodes (lptr, rpte, incl_in_edges, incl_out_edges,
				succ_nodes, value_in.pt_nodes);
#else
		changed_nvisit.insert (vnid);
		// pn->get_out_adj_nodes (lptr, rpte, incl_in_edges, incl_out_edges,
		//	succ_nodes, value_in.pt_nodes);
#endif
	}

#if SUMM_K_CONSISTENT == 0
	g_pt.get_out_adj_nodes (changed_nvisit, lptr, rpte, incl_in_edges, incl_out_edges,
		succ_nodes, value_in.pt_nodes);
#endif

	// Breadth-first

#if DEBUG_CONTAINER
	DEBUG ("\npull_new_ans succ =");
	for (vni = succ_nodes.begin (); vni != succ_nodes.end (); vni++)
		DEBUG ("%d,", *vni);
#endif

	if (succ_nodes.size ())
		pull_new_ans (succ_nodes, ext_bndry, value_in, 
			lptr, must_lptr, l, ds, rpte, incl_in_edges, incl_out_edges,
			ext_bndry_pulled_nodes, summ_cmpts, summ_cmpts_map, new_pt_to_access_name);

	RETURN_VOID ();
}

#if PULL_ACCESS_NAMES == 0
/**
 * This function computes NEW_PT_TO_ACCESS_NAME of the affected nodes and
 * propagates AN starting from PT_NID. Here EXT_BNDRY is already in VALUE_IN.
 * This function pushes AN of nodes not in NREACH once (i.e. until they are in
 * EXT_VIS_NODES). This function pushes AN of each node in NREACH until it
 * keeps changing.
 * output: NEW_PT_TO_ACCESS_NAME
 */

void points_to_analysis_fi::
push_an_subgraph (pt_node_index pt_nid,
	set<pt_node_index> & ext_bndry,
	set<pt_node_index> & nreach,
	pt_node_set & value_in,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	def_stmt_set ds,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<set<pt_node_index> > & summ_cmpts,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	set<pt_node_index> empty_new_succ_nodes;
	set<pt_node_index> empty_ext_vis_nodes;
	push_an_subgraph (pt_nid, empty_new_succ_nodes, empty_ext_vis_nodes, ext_bndry, nreach, value_in,
		lptr, must_lptr, l, ds, rpte, 
		incl_out_edges, summ_cmpts, summ_cmpts_map, new_pt_to_access_name);

	if (empty_new_succ_nodes.size ())
		RESULT ("\nError: All succ nodes of push_an_subgraph() are not processed");
}
#endif

#if PULL_ACCESS_NAMES == 0
void points_to_analysis_fi::
push_an_subgraph (pt_node_index pt_nid,
	set<pt_node_index> & new_succ_nodes,
	set<pt_node_index> & ext_vis_nodes,
	set<pt_node_index> & ext_bndry,
	set<pt_node_index> & nreach,
	pt_node_set & value_in,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	def_stmt_set ds,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<set<pt_node_index> > & summ_cmpts,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	DEBUG ("\npush_new_ans(pt_nid=%d)", pt_nid);

	if (!pt_fi_node::is_node_valid_at_point (pt_nid, value_in.pt_nodes))
		return;

	if (ext_vis_nodes.find (pt_nid) != ext_vis_nodes.end ())
		return;
	// Add this node to ext_vis_nodes if it is an external node
	if (nreach.find (pt_nid) == nreach.end ())
		ext_vis_nodes.insert (pt_nid);

	// Compute new APs of PNID due to Egen and Ekill
	pt_fi_node * pn = g_pt.nodes[pt_nid];
	push_an_edge (*pn, new_succ_nodes, ext_bndry, nreach, value_in, 
		lptr, must_lptr, l, ds, rpte, 
		incl_out_edges, summ_cmpts_map, new_pt_to_access_name);
	DEBUG ("\nnode=%d, num of new succ nodes=%d", pt_nid, new_succ_nodes.size ());

	// Breadth-first

#if DEBUG_CONTAINER
	DEBUG ("\npush_new_ans succ (%d) =", pt_nid);
	set<pt_node_index>::iterator vni;
	for (vni = new_succ_nodes.begin (); vni != new_succ_nodes.end (); vni++)
		DEBUG ("%d,", *vni);
#endif

	// We cannot do the following as new_succ_nodes keeps changing since it
	// is common to all recursive calls of push_an_subgraph(). It needs to
	// be made common so that same node is not processed more than once
	// unnecessarily along two different chains of recursive calls.
	// for (ni = new_succ_nodes.begin (); ni != new_succ_nodes.end (); ni++)
	while (new_succ_nodes.size ())
	{
		set<pt_node_index>::iterator ni;
		ni = new_succ_nodes.begin ();
		pt_node_index nid = *ni;
		new_succ_nodes.erase (ni);
		push_an_subgraph (nid, new_succ_nodes, ext_vis_nodes, ext_bndry, nreach, value_in, 
			lptr, must_lptr, l, ds, rpte, incl_out_edges, 
			summ_cmpts, summ_cmpts_map, new_pt_to_access_name);
	}
}
#endif

#if PULL_ACCESS_NAMES == 0
/**
 * This function computes NEW_PT_TO_ACCESS_NAME of the affected nodes in
 * NVISIT. Here EXT_BNDRY is already in VALUE_IN. It pushes only new ANs.
 * output: NEW_PT_TO_ACCESS_NAME
 */

void points_to_analysis_fi::
push_new_an_subgraph (set<pt_node_index> & nvisit,
	set<pt_node_index> & ext_bndry,
	set<pt_node_index> & nreach,
	pt_node_set & value_in,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	def_stmt_set ds,
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	set<set<pt_node_index> > & summ_cmpts,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	set<pt_node_index>::iterator vni;
#if DEBUG_CONTAINER
	DEBUG ("\npush_new_ans=");
	for (vni = nvisit.begin (); vni != nvisit.end (); vni++)
		DEBUG ("%d,", *vni);
#endif

	set<pt_node_index> changed_succ_nodes;

	for (vni = nvisit.begin (); vni != nvisit.end (); vni++)
	{
		pt_node_index vnid = *vni;
		DEBUG ("\npush_new_ans(node=%d)", vnid);

		#if CHECK_CONTAINER
		if (!pt_fi_node::is_node_valid_at_point (vnid, value_in.pt_nodes))
		{
			label v = g_pt.get_node_name (vnid);
			csvarinfo_t var = VEC_index (csvarinfo_t, program.variable_data, v);
			RESULT ("\nError: nvisit node=%d, var=%s(%d) not valid", vnid, var->name, v);
			continue;
		}
		#endif

		#if CHECK_CONTAINER
		if (g_pt.nodes.find (vnid) == g_pt.nodes.end ())
		{
			RESULT ("\nError: pt-node=%d not found", vnid);
			continue;
		}
		#endif

		// If vnid is neither in NREACH nor in EXT_BNDRY, then do not
		// process it. We need to push AN of only EXT_BNDRY and NREACH
		// nodes. This check is also required because, otherwise
		// pt_access_map.get_access_name() on vnid will fetch AN from
		// new_pt_to_access_name and will not find it (as
		// push_an_edge() skips computation of AN of nodes outside
		// NREACH).
		if (ext_bndry.find (vnid) == ext_bndry.end () &&
			nreach.find (vnid) == nreach.end ())	
			continue;

		pt_fi_node * pn = g_pt.nodes[vnid];

		// Compute new APs of PNID due to Egen and Ekill
		push_an_edge (*pn, changed_succ_nodes, ext_bndry, nreach, value_in, 
			lptr, must_lptr, l, ds, rpte, 
			incl_out_edges, summ_cmpts_map, new_pt_to_access_name);
		DEBUG ("\nnode=%d, num of changed nodes=%d", vnid, changed_succ_nodes.size ());
	}

	// Breadth-first

#if DEBUG_CONTAINER
	DEBUG ("\npush_new_ans succ =");
	for (vni = changed_succ_nodes.begin (); vni != changed_succ_nodes.end (); vni++)
		DEBUG ("%d,", *vni);
#endif

	if (changed_succ_nodes.size ())
		push_new_an_subgraph (changed_succ_nodes, ext_bndry, nreach, value_in, 
			lptr, must_lptr, l, ds, rpte, incl_out_edges, 
			summ_cmpts, summ_cmpts_map, new_pt_to_access_name);
}
#endif

/**
 * This function clones edges between n1 and n2, where at least one of n1 and
 * n2 is in AFFECTED_NODES and both of them are in VALUE_IN or LPTR or RPTE.
 * The map CLONE saves the clones of only such nodes. Therefore, if a clone of
 * such a node is saved in the map, then without doing any check, we can
 * perform edge cloning.
 *
 * Do not add an edge from/to heap nodes that have AP=0. Ideally all fresh heap
 * nodes should have AP=0. But on-the-fly generated heap field nodes do not
 * have AP=0 but these need to be added to fresh heap nodes.
 *
 * This function also stores OLD_FS_NEW_FI_EDGES: the new edges added to FI
 * information (gPT) between old FS information (gPT nodes). Whether the new
 * edge is between old gPT nodes can be determined using OLD_MAX_NODE_ID. 
 */

void points_to_analysis_fi::
clone_edges (map<pt_node_index, pt_node_index> & clone,
	pt_node_set & value_in,
	set<pt_node_index> & lptr,
	set<pt_node_index> & must_lptr,
	label l,
	set<pt_node_index> & rpte, 
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	map<pt_node_index, bool> & affected_nodes,
	unsigned int old_max_node_id,
	set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges)
{
	FUNBEGIN ();

	DEBUG ("\nclone_edges()");
	pt_node_index stack_id = g_pt.stack.get_node_id ();

	// Since newly generated field nodes are added to value_in
	// (valid_nodes), we do not need to consider incl_edges while calling
	// get_nodes_valid_at_point() or is_node_valid_at_point().
	set<pt_node_index> valid_nodes;
	valid_nodes.insert (value_in.pt_nodes.begin (), value_in.pt_nodes.end ());

	// Clone edges attached to AFFECTED_NODES via in- and out-edges.
 
	// get_valid_clone() may return NULL for fresh heap nodes. However this
	// is not an error: when we deal with a group of statements, stmt 1 may
	// point to a fresh heap node, stmt 2 may have an out-edge from the
	// fresh heap node, stmt 3 may kill the pointer to the fresh heap node.
	// Overall, stmt 2 causes out-edge from fresh heap node.

	map<pt_node_index, bool>::iterator ani;
	for (ani = affected_nodes.begin (); ani != affected_nodes.end (); ani++)
	{
		pt_node_index anid = ani->first;
		DEBUG ("\nAffected node=%d", anid);
		pt_fi_node * an = g_pt.nodes[anid];
		pt_fi_node * clone_an = get_valid_clone (anid, valid_nodes, affected_nodes, clone);
		if (!clone_an)
			continue;

		// Clone in- and out-edges of N in g_pt except those in Ekill

		map<label, set<pt_node_index> >::iterator ei;
		map<label, set<pt_node_index> > ine;

		// Get in nodes (excluding due to Ekill) of ANID
		ine = an->get_in_edge_list ();
		for (ei = ine.begin (); ei != ine.end (); ei++)
		{
			label inl = ei->first;
			set<pt_node_index> inn = ei->second;
			set<pt_node_index>::iterator ni;
			for (ni = inn.begin (); ni != inn.end (); ni++)
			{
				pt_node_index in_nid = *ni;
				DEBUG ("\nin-edge %d->l=%d->%d", in_nid, inl, anid);

				// Ekill
				if (must_lptr.find (in_nid) != must_lptr.end ()	&& l == inl)
					continue;
				pt_fi_node * clone_in_n = get_valid_clone (in_nid, valid_nodes, affected_nodes, clone);
				if (!clone_in_n)
					continue;
				DEBUG ("\nCloned in-edge %d->l=%d->%d", 
					clone_in_n->get_node_id (), inl, clone_an->get_node_id ());
				if (clone_in_n->insert_edge (inl, *clone_an, stack_id))
					#if FI_REANALYSIS
					add_old_fs_new_fi_edge (clone_in_n->get_node_id (), clone_an->get_node_id (), 
						old_max_node_id, old_fs_new_fi_edges);
					#else
					;
					#endif
			}
		}

		// Get out nodes (excluding due to Ekill) of ANID
		map<label, set<pt_node_index> > oute = an->get_out_edge_list ();
		for (ei = oute.begin (); ei != oute.end (); ei++)
		{
			label outl = ei->first;

			// Ekill
			if (must_lptr.find (anid) != must_lptr.end () && l == outl)
				continue;

			set<pt_node_index> outn = ei->second;
			set<pt_node_index>::iterator ni;
			for (ni = outn.begin (); ni != outn.end (); ni++)
			{
				pt_node_index out_nid = *ni;
				DEBUG ("\nout-edge %d->l=%d->%d", anid, outl, out_nid);
				pt_fi_node * clone_out_n = get_valid_clone (out_nid, valid_nodes, affected_nodes, clone);
				if (!clone_out_n)
					continue;
				DEBUG ("\nCloned out-edge %d->l=%d->%d", 
					clone_an->get_node_id (), outl, clone_out_n->get_node_id());
				if (clone_an->insert_edge (outl, *clone_out_n, stack_id))
					#if FI_REANALYSIS
					add_old_fs_new_fi_edge (clone_an->get_node_id (), clone_out_n->get_node_id (), 
						old_max_node_id, old_fs_new_fi_edges);
					#else
					;
					#endif
			}
		}
	}	

	// It is possible that an edge needs to be created from L to R but the
	// access paths of neither L nor R change i.e. L and R are not
	// AFFECTED_NODES. Therefore, clone edges in Egen (lptr to rpte) and
	// incl_in_edges.

	// Clone edges: LPTR->L->RPTE
	set<pt_node_index>::iterator lni;
	for (lni = lptr.begin (); lni != lptr.end (); lni++)
	{
		pt_node_index lnid = *lni;
		pt_fi_node * clone_ln = get_valid_clone (lnid, valid_nodes, affected_nodes, clone);
		// This can happen e.g. if lnid is a fresh heap node 
		if (!clone_ln)
		{
			// This is an error since lptr can never be fresh heap node
			DEBUG ("\nlptr=%d does not have valid clone", lnid);
			DEBUG ("\nlptr=%d->l=%d->rpte=", lnid, l);
			set<pt_node_index>::iterator rni;
			for (rni = rpte.begin (); rni != rpte.end (); rni++)
				DEBUG ("%d,", *rni);
			continue;
		}

		set<pt_node_index>::iterator rni;
		for (rni = rpte.begin (); rni != rpte.end (); rni++)
		{
			pt_node_index rnid = *rni;
			DEBUG ("\nEgen %d->l=%d->rpte=%d", lnid, l, rnid);
			pt_fi_node * clone_rn = get_valid_clone (rnid, valid_nodes, affected_nodes, clone);
			if (!clone_rn)
			{
				RESULT ("\nError: rpte=%d should be valid", rnid);
				continue;
			}
			DEBUG ("\nCloned edge lptr=%d->l=%d->rpte=%d", 
				clone_ln->get_node_id (), l, clone_rn->get_node_id ());
			if (clone_ln->insert_edge (l, *clone_rn, stack_id))
				#if FI_REANALYSIS
				add_old_fs_new_fi_edge (clone_ln->get_node_id (), clone_rn->get_node_id (), 
					old_max_node_id, old_fs_new_fi_edges);
				#else
				;
				#endif
		}
	}

#if PULL_ACCESS_NAMES
	// Clone NEW_IN_EDGES
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator ine;
	for (ine = incl_in_edges.begin (); ine != incl_in_edges.end (); ine++)
	{
		pt_node_index dst_nid = ine->first;
		pt_fi_node * clone_dn = get_valid_clone (dst_nid, valid_nodes, affected_nodes, clone);
		// This may not be an error since incl_in_edges may be for
		// fresh node that ultimately also remains fresh: when we deal
		// with a group of statements, stmt 1 may point to a fresh heap
		// node, stmt 2 may have an out-edge from the fresh heap node,
		// stmt 3 may kill the pointer to the fresh heap node. Overall,
		// stmt 2 causes out-edge to fresh heap node.
		if (!clone_dn)
		{
#if DEBUG_CONTAINER
			set<pt_node_index>::iterator vi;
			DEBUG ("\nvalid_nodes=");
			for (vi = valid_nodes.begin (); vi != valid_nodes.end (); vi++)
				DEBUG ("%d,", *vi);
			DEBUG ("\ndst=%d of incl_in_edges is invalid/unused", dst_nid);
#endif
			continue;
		}

		map<label, set<pt_node_index> > e = ine->second;
		map<label, set<pt_node_index> >::iterator ei;
		for (ei = e.begin (); ei != e.end (); ei++)
		{
			label inl = ei->first;
			set<pt_node_index> srcs = ei->second;
			set<pt_node_index>::iterator si;
			for (si = srcs.begin (); si != srcs.end (); si++)
			{
				pt_node_index src_nid = *si;
				pt_fi_node * clone_sn = get_valid_clone (src_nid, valid_nodes, affected_nodes, clone);
				if (!clone_sn)
				{
					DEBUG ("\nsrc=%d of incl_in_edges should be valid", src_nid);
					continue;
				}
				DEBUG ("\nin-edge %d->l=%d->%d", src_nid, inl, dst_nid);
				DEBUG ("\nCloned in-edge %d->l=%d->%d", 
					clone_sn->get_node_id (), inl, clone_dn->get_node_id ());
			
				if (clone_sn->insert_edge (inl, *clone_dn, stack_id))
					#if FI_REANALYSIS
					add_old_fs_new_fi_edge (clone_sn->get_node_id (), clone_dn->get_node_id (), 
						old_max_node_id, old_fs_new_fi_edges);
					#else
					;
					#endif
			}
		}
	}

#else
	// Clone NEW_OUT_EDGES
	map<pt_node_index, map<label, set<pt_node_index> > >::iterator oute;
	for (oute = incl_out_edges.begin (); oute != incl_out_edges.end (); oute++)
	{
		pt_node_index src_nid = oute->first;
		pt_fi_node * clone_sn = get_valid_clone (src_nid, valid_nodes, affected_nodes, clone);
		if (!clone_sn)
		{
			DEBUG ("\nsrc=%d of incl_out_edges should be valid", src_nid);
			continue;
		}

		map<label, set<pt_node_index> > e = oute->second;
		map<label, set<pt_node_index> >::iterator ei;
		for (ei = e.begin (); ei != e.end (); ei++)
		{
			label outl = ei->first;
			set<pt_node_index> dsts = ei->second;
			set<pt_node_index>::iterator di;
			for (di = dsts.begin (); di != dsts.end (); di++)
			{
				pt_node_index dst_nid = *di;
				pt_fi_node * clone_dn = get_valid_clone (dst_nid, valid_nodes, affected_nodes, clone);
				if (!clone_dn)
				{
					RESULT ("\nError: dst=%d of incl_out_edges should be valid", dst_nid);
					continue;
				}
				DEBUG ("\nout-edge %d->l=%d->%d", src_nid, outl, dst_nid);
				DEBUG ("\nCloned out-edge %d->l=%d->%d", 
					clone_sn->get_node_id (), outl, clone_dn->get_node_id ());
			
				if (clone_sn->insert_edge (outl, *clone_dn, stack_id))
					#if FI_REANALYSIS
					add_old_fs_new_fi_edge (clone_sn->get_node_id (), clone_dn->get_node_id (), 
						old_max_node_id, old_fs_new_fi_edges);
					#else
					;
					#endif
			}
		}
	}
#endif

	RETURN_VOID ();
}

/**
 * in: NEW_PT_TO_MAX_DEPTH
 * out: NEW_PT_TO_MAX_DEPTH
 */

#if SUMM_K_CONSISTENT
void points_to_analysis_fi::
compute_new_summ_cmpts (set<pt_node_index> & nvisit,
	set<pt_node_index> & ext_bndry,
	pt_node_set & value_in,
	set<pt_node_index> & lptr, 
	set<pt_node_index> & must_lptr, 
	label l, 
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, max_depth> & new_pt_to_max_depth, 
	set<set<pt_node_index> > & summ_cmpts)
{
	DEBUG ("\ncompute_new_summ_cmpts (set of rpte)");

	set<pt_node_index>::iterator ni;
	for (ni = nvisit.begin (); ni != nvisit.end (); ni++)
	{
		pt_node_index nid = *ni;
		if (g_pt.nodes.find (nid) == g_pt.nodes.end ())
		{
			RESULT ("\nError: pt-node=%d not found", nid);
			continue;
		}
		DEBUG ("\nCompute new max_depth for pt-node=%d", nid);
		pt_fi_node * n = g_pt.nodes[nid];
		compute_new_summ_cmpts (*n, ext_bndry, value_in, 
			lptr, must_lptr, l, rpte, incl_in_edges, 
			new_pt_to_max_depth, summ_cmpts);
	}
}
#endif

/**
 * This function computes the max_depth and summ_cmpts of node PT_N using
 * in-edges = (E(g_pt) - EKill) U EGen, where E(g_pt) are its pre-existing
 * in-edges, EKill are edges from MUST_LPTR via L, and EGen are edges from LPTR
 * via L. It first updates max_depth of PT_N. Then it calls update_summ_cmpts()
 * for PT_N (note that update_summ_cmpts() should be called whenever either the
 * in-node newly has max_depth=inf or PT_N newly has max_depth=inf; however
 * since we cannot determine this, we always call update_summ_cmpts()). 
 * in: NEW_PT_TO_MAX_DEPTH, SUMM_CMPTS
 * out: NEW_PT_TO_MAX_DEPTH, SUMM_CMPTS
 * @returns true if max_depth of PT_N has changed
 *
 * FIXME: For efficiency, instead of pulling max_depth from all predecessors
 * (irrespective of whether or not the predecessor's max_depth has changed), we
 * should push the updated max_depth to all successors.
 */

#if SUMM_K_CONSISTENT
bool points_to_analysis_fi::
compute_new_summ_cmpts (pt_fi_node & pt_n, 
	set<pt_node_index> & ext_bndry,
	pt_node_set & value_in,
	set<pt_node_index> & lptr, 
	set<pt_node_index> & must_lptr, 
	label l, 
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, max_depth> & new_pt_to_max_depth,
	set<set<pt_node_index> > & summ_cmpts)
{
	DEBUG ("\ncompute_new_summ_cmpts (pt-node=%d)", pt_n.get_node_id ());
	pt_node_index pt_nid = pt_n.get_node_id ();

	// Max_depth of PT_NID computed in the previous iteration of this fixed
	// point computation.
	max_depth dest_md_old = 
		pt_access_map.get_max_depth (pt_nid, ext_bndry, new_pt_to_max_depth);
	
	access_name dest_access_name;
	map<label, set<pt_node_index> > in_pt_edges;

	// Computing APs of destination pt nodes using NEW_IN_EDGES
	if (incl_in_edges.find (pt_nid) != incl_in_edges.end ())
		in_pt_edges = incl_in_edges[pt_nid];
	map<label, set<pt_node_index> >::iterator ei;
	for (ei = in_pt_edges.begin (); ei != in_pt_edges.end (); ei++)
	{
		label in_label = ei->first;
		set<pt_node_index> in_nodes = ei->second;
		set<pt_node_index>::iterator ni;
		for (ni = in_nodes.begin (); ni != in_nodes.end (); ni++)
		{
			pt_node_index in_n = *ni;
			DEBUG ("\nincl_in_edges %d->l=%d->%d", in_n, in_label, pt_nid);

			// No need to check whether IN_N is valid or not. This
			// has already been done while computing
			// NEW_IN_EDGES.
			pt_access_map.update_max_depth (in_n, in_label, pt_nid, 
				ext_bndry, new_pt_to_max_depth);
			pt_access_map.update_summ_cmpts (in_n, in_label, pt_nid, 
				ext_bndry, new_pt_to_max_depth, summ_cmpts);
		}
	}

	// Computing APs of destination pt nodes using in-edges = E(g_pt) - EKill
	in_pt_edges = pt_n.get_in_edge_list ();
	for (ei = in_pt_edges.begin (); ei != in_pt_edges.end (); ei++)
	{
		label in_label = ei->first;
		set<pt_node_index> in_nodes = ei->second;
		set<pt_node_index>::iterator ni;
		for (ni = in_nodes.begin (); ni != in_nodes.end (); ni++)
		{
			pt_node_index in_n = *ni;
			DEBUG ("\nin_pt-edges %d->l=%d->%d", in_n, in_label, pt_nid);

			// IN_N is considered only if it is in Nin or newly created or unused heap.
			if (!pt_fi_node::is_node_valid_at_point (in_n, value_in.pt_nodes))
			{
				DEBUG ("\nnode=%d is invalid", in_n);
				continue;
			}

			if (must_lptr.find (in_n) != must_lptr.end () && l == in_label)
			{
				DEBUG ("\nEdge killed by must_lptr");
				continue;
			}

			pt_access_map.update_max_depth (in_n, in_label, pt_nid, 
				ext_bndry, new_pt_to_max_depth);
			pt_access_map.update_summ_cmpts (in_n, in_label, pt_nid, 
				ext_bndry, new_pt_to_max_depth, summ_cmpts);
		}
	}

	// Computing APs of destination pt nodes using in-edges = EGen to PT_N
	// If EGen (lptr x f x rpte) has an edge with PT_N in rpte.
	if (rpte.find (pt_nid) != rpte.end ())
	{
		DEBUG ("\npt-node=%d found in rpte", pt_nid);
		set<pt_node_index>::iterator li;
		for (li = lptr.begin (); li != lptr.end (); li++)
		{
			pt_access_map.update_max_depth (*li, l, pt_nid, 
				ext_bndry, new_pt_to_max_depth);
			pt_access_map.update_summ_cmpts (*li, l, pt_nid, 
				ext_bndry, new_pt_to_max_depth, summ_cmpts);
		}
	}

	max_depth dest_md_new = 
		pt_access_map.get_max_depth (pt_nid, ext_bndry, new_pt_to_max_depth);

	return dest_md_old != dest_md_new;
}
#endif

/**
 * in: NEW_PT_TO_ACCESS_NAME
 * out: NEW_PT_TO_ACCESS_NAME
 */

void points_to_analysis_fi::
pull_new_an (set<pt_node_index> & nvisit,
	set<pt_node_index> & ext_bndry,
	pt_node_set & value_in,
	set<pt_node_index> & lptr, 
	set<pt_node_index> & must_lptr, 
	label l, 
	def_stmt_set ds, 
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	FUNBEGIN ();

	DEBUG ("\npull_new_an (set of rpte)");

	set<pt_node_index> empty_set;
	set<pt_node_index>::iterator ni;
	for (ni = nvisit.begin (); ni != nvisit.end (); ni++)
	{
		pt_node_index nid = *ni;
		#if CHECK_CONTAINER
		if (g_pt.nodes.find (nid) == g_pt.nodes.end ())
		{
			RESULT ("\nError: pt-node=%d not found", nid);
			continue;
		}
		#endif
		DEBUG ("\nCompute new ap for pt-node=%d", nid);
		pt_fi_node * n = g_pt.nodes[nid];
		pull_new_an (*n, ext_bndry, value_in, lptr, must_lptr, l, ds, rpte, incl_in_edges, 
			empty_set, summ_cmpts_map, new_pt_to_access_name);
	}

	RETURN_VOID ();
}

/**
 * This function computes the APs of node PT_N using in-edges = 
 * (E(g_pt) - EKill) U EGen, where E(g_pt) are its pre-existing in-edges, EKill
 * are edges from MUST_LPTR via L, and EGen are edges from LPTR via L.
 * in: NEW_PT_TO_ACCESS_NAME
 * out: NEW_PT_TO_ACCESS_NAME
 * @returns true if access name of PT_N has changed
 *
 * Pulling may be inefficient as it pulls APs from all predecessors
 * (irrespective of whether or not the predecessor's APs have changed);
 * therefore, we have also implemented pushing the updated APs to all
 * successors.
 */

bool points_to_analysis_fi::
pull_new_an (pt_fi_node & pt_n, 
	set<pt_node_index> & ext_bndry,
	pt_node_set & value_in,
	set<pt_node_index> & lptr, 
	set<pt_node_index> & must_lptr, 
	label l, 
	def_stmt_set ds, 
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_in_edges,
	set<pt_node_index> & ext_bndry_pulled_nodes,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	FUNBEGIN ();

	DEBUG ("\npull_new_an (pt-node=%d)", pt_n.get_node_id ());
	pt_node_index pt_nid = pt_n.get_node_id ();

	if (pt_nid == g_pt.stack.get_node_id ())
	{
		RESULT ("\nError: APs of stack node should never be updated");
		RETURN (false);
		// return false;
	}

	access_name dest_access_name;
	map<label, set<pt_node_index> > in_pt_edges;

	label dest_static_name = 0;
	dest_static_name = g_pt.get_node_name (pt_nid);

#if PULL_BNDRY_ONCE
	bool pulled = false;
	if (ext_bndry_pulled_nodes.find (pt_nid) != ext_bndry_pulled_nodes.end ())
	{
		DEBUG ("\npulled=%d", pt_nid);
		pulled = true;
		// Since we will not recompute old dest_access_name for pulled
		// nodes, recollect old dest_access_name.
		access_name * dest_an = 
			pt_access_map.get_access_name (pt_nid, ext_bndry, summ_cmpts_map, new_pt_to_access_name);
		if (dest_an)
			dest_access_name = *dest_an;
	}
#endif

	// Computing APs of destination pt nodes using NEW_IN_EDGES
	if (incl_in_edges.find (pt_nid) != incl_in_edges.end ())
		in_pt_edges = incl_in_edges[pt_nid];
	map<label, set<pt_node_index> >::iterator ei;
	for (ei = in_pt_edges.begin (); ei != in_pt_edges.end (); ei++)
	{
		label in_label = ei->first;
		set<pt_node_index> in_nodes = ei->second;
		set<pt_node_index>::iterator ni;
		for (ni = in_nodes.begin (); ni != in_nodes.end (); ni++)
		{
			pt_node_index in_n = *ni;
			DEBUG ("\nincl_in_edges %d->l=%d->%d", in_n, in_label, pt_nid);

#if PULL_BNDRY_ONCE
			if (pulled && ext_bndry.find (in_n) != ext_bndry.end ())
			{
				RESULT ("\nbndry=%d done", in_n);
				continue;
			}
#endif
			// No need to check whether IN_N is valid or not. This
			// has already been done while computing
			// NEW_IN_EDGES.
			pt_access_map.compute_ap (in_n, in_label, dest_static_name, ext_bndry, g_ap, 
				dest_access_name, summ_cmpts_map, new_pt_to_access_name);
		}
	}

	// Computing APs of destination pt nodes using in-edges = E(g_pt) - EKill
	in_pt_edges = pt_n.get_in_edge_list ();
	for (ei = in_pt_edges.begin (); ei != in_pt_edges.end (); ei++)
	{
		label in_label = ei->first;
		set<pt_node_index> in_nodes = ei->second;
		set<pt_node_index>::iterator ni;
		for (ni = in_nodes.begin (); ni != in_nodes.end (); ni++)
		{
			pt_node_index in_n = *ni;
			DEBUG ("\nin_pt-edges %d->l=%d->%d", in_n, in_label, pt_nid);

#if PULL_BNDRY_ONCE
			if (pulled && ext_bndry.find (in_n) != ext_bndry.end ())
			{
				RESULT ("\nbndry=%d done", in_n);
				continue;
			}
#endif

			// IN_N is considered only if it is in Nin or newly created or unused heap.
			if (!pt_fi_node::is_node_valid_at_point (in_n, value_in.pt_nodes))
			{
				DEBUG ("\nnode=%d is invalid", in_n);
				continue;
			}

			if (must_lptr.find (in_n) != must_lptr.end () && l == in_label)
			{
				DEBUG ("\nEdge from node=%d,l=%d killed by must_lptr", in_n, l);
				continue;
			}

			pt_access_map.compute_ap (in_n, in_label, dest_static_name, ext_bndry, g_ap, 
				dest_access_name, summ_cmpts_map, new_pt_to_access_name);
		}
	}

	// Computing APs of destination pt nodes using in-edges = EGen to PT_N
	// If EGen (lptr x f x rpte) has an edge with PT_N in rpte.
	if (rpte.find (pt_nid) != rpte.end ())
	{
		DEBUG ("\npt-node=%d found in rpte", pt_nid);
		set<pt_node_index>::iterator li;
		for (li = lptr.begin (); li != lptr.end (); li++)
		{
			pt_node_index in_n = *li;
#if PULL_BNDRY_ONCE
			if (pulled && ext_bndry.find (in_n) != ext_bndry.end ())
			{
				RESULT ("\nbndry=%d done", in_n);
				continue;
			}
#endif

			pt_access_map.compute_ap (in_n, l, dest_static_name, ds, ext_bndry, g_ap, 
				dest_access_name, summ_cmpts_map, new_pt_to_access_name);
		}
	}

#if OVER_APPROX_CYCLIC_EDGES
	dest_access_name.over_approx_cyclic_edges (g_ap);
#endif

#if PULL_BNDRY_ONCE
	if (!pulled)
	{
		DEBUG ("\nnow pulled=%d", pt_nid);
		ext_bndry_pulled_nodes.insert (pt_nid);
	}
#endif

	// Access name of PT_NID computed in the previous iteration of this fixed point computation.
	access_name * dest_access_name_old = 
		pt_access_map.get_access_name (pt_nid, ext_bndry, summ_cmpts_map, new_pt_to_access_name);
	access_name dest_an_old;
	if (!dest_access_name_old)
		dest_access_name_old = &dest_an_old;

#if SUMM_STMT_CLOSURE || SUMM_TYPE_CLOSURE
	// ap_unbounded predicate of PT_N is set to true when in-edge is found
	// to be a repeating stmt id or type in gAP. But this repetition is not
	// saved in gAP. Therefore, during the analysis of a later statement,
	// ap_unbounded predicate of PT_N cannot be computed from APs of
	// in-nodes of PT_N.  A safe approximation is to retain the value of
	// ap_unbounded predicate once it is set to true. We need to use
	// ap_unbounded computed in the original PT_TO_ACCESS_MAP and not in
	// NEW_PT_TO_ACCESS_MAP.
	// Example of imprecision due to this. (x->y),(y->y). Here y will have
	// ap_unbounded=true. Now when, x=null, then also clone of y will have
	// ap_unbounded; therefore, the updated graph will be (y->y). 
	bool ap_unbounded_orig = pt_access_map.get_ap_unbounded (pt_nid);
	dest_access_name.add_ap_unbounded (ap_unbounded_orig);
#elif SUMM_K_FILTER || SUMM_K_PREFIX || SUMM_K_CONSISTENT
	// SUMM_K_FILTER can identify an unbounded access path from gAP using the
	// value of K. So no need to over approximate ap_unbounded predicate.
	// Example of imprecision due to this. (x->y),(y->y). Here y will have
	// ap_unbounded=true. Now when, x=null, then clone of y will not have
	// ap_unbounded; therefore, the updated graph will be phi.
#elif SUMM_TYPE_K && gAP_CYCLIC
	// SUMM_TYPE_K && gAP_CYCLIC can identify an unbounded access path in
	// the presence of any cyclic edge.
#elif SUMM_TYPE_K && !gAP_CYCLIC
	// SUMM_TYPE_K can identify an unbounded access path from gAP from the
	// absence of edge AP_NID->(L,TYPE).
#endif

#if SUMM_K_CONSISTENT
	// A summary node has no type because it has the types of all the nodes
	// that it represents. SUMM_K_CONSISTENT does not need types --- types
	// are required to perform merging based both on access paths and
	// types. This leads to merging of two allocation sites if their APs
	// are same. e.g. test66c.
	if (summ_cmpts_map.find (pt_nid) == summ_cmpts_map.end ())
#endif
	// Set heap name as node_name_type for heap nodes.
//	if (g_pt.is_heap_node (pt_nid))
	{
		label node_name_type = g_pt.get_node_name (pt_nid);
		dest_access_name.add_node_name_type (node_name_type);
	}

#if SUMM_K_CONSISTENT
	// If a node is in summ_cmpts, then previously computed APs should also
	// be saved. This is because the new APs are using the edges connected
	// only to PT_NID and not with other nodes of the summ_cmpt.
	if (summ_cmpts_map.find (pt_nid) != summ_cmpts_map.end ())
	{
		dest_access_name.add_access_name (*dest_access_name_old);
		label node_name_type = 0;
		dest_access_name.add_node_name_type (node_name_type);
	}
#endif
	
#if SUMM_K_CONSISTENT
	// Once dest_access_name of node is ready (including summ_cmpt nodes),
	// remove p.sigma if p.+ is already present in dest_access_name.
	remove_wild_card_subsumed_aps (dest_access_name);
#endif

	bool is_same = dest_access_name.is_same (*dest_access_name_old);

#if SUMM_K_CONSISTENT
	if (!is_same)
	{
		DEBUG ("\nSetting new pt_to_access_name for pt=%d", pt_nid);
		// If PT_NID is part of a summ_cmpt, then save the access name
		// of PT_NID corresponding to the representative node of its
		// summ_cmpt.
		if (summ_cmpts_map.find (pt_nid) != summ_cmpts_map.end ())
		{
			pt_node_index repr_nid = summ_cmpts_map[pt_nid];
			DEBUG ("\npt=%d is summ_cmpt, repr_id=%d", pt_nid, repr_nid);
			new_pt_to_access_name[repr_nid] = dest_access_name;
		}
		else
		{
			DEBUG ("\npt=%d is not summ_cmpt", pt_nid);
			new_pt_to_access_name[pt_nid] = dest_access_name;
		}
	}
#else
	if (!is_same)
		new_pt_to_access_name[pt_nid] = dest_access_name;
#endif


	#if DEBUG_CONTAINER
	DEBUG ("\nSame=%d", is_same);
	set<ap_node_index>::iterator ai; 
	DEBUG ("\ndest_ap_nodes_old of pt-node=%d=", pt_nid);
	dest_access_name_old->print (&g_ap);
	DEBUG ("\ndest_ap_nodes of pt-node=%d=", pt_nid);
	dest_access_name.print (&g_ap);
	#endif

#if SUMM_TYPE_CLOSURE
	set_ap_static_name (pt_nid, dest_access_name);
#endif

	RETURN (!is_same);
	// return !is_same;
}

#if SUMM_TYPE_K && PULL_ACCESS_NAME == 0
/**
 * This function computes the APs of succ nodes of PT_N using out-edges = 
 * (E(g_pt) - EKill) U EGen, where E(g_pt) are its pre-existing out-edges, EKill
 * are edges from MUST_LPTR via L, and EGen are edges from LPTR via L.
 * in: NEW_PT_TO_ACCESS_NAME
 * out: NEW_PT_TO_ACCESS_NAME
 * out: NEW_SUCC_NODES: succ nodes of PT_N whose access name has changed or
 *      needs to be pushed because it is not in NREACH. 
 */

void points_to_analysis_fi::
push_an_edge (pt_fi_node & pt_n, 
	set<pt_node_index> & new_succ_nodes,
	set<pt_node_index> & ext_bndry,
	set<pt_node_index> & nreach,
	pt_node_set & value_in,
	set<pt_node_index> & lptr, 
	set<pt_node_index> & must_lptr, 
	label l, 
	def_stmt_set ds, 
	set<pt_node_index> & rpte,
	map<pt_node_index, map<label, set<pt_node_index> > > & incl_out_edges,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
	pt_node_index pt_nid = pt_n.get_node_id (); 

	DEBUG ("\npush_new_an (pt-node=%d)", pt_nid);

	// Computing APs of succ of pt nodes using NEW_OUT_EDGES
	map<label, set<pt_node_index> > new_pt_out_edges;
	if (incl_out_edges.find (pt_nid) != incl_out_edges.end ())
		new_pt_out_edges = incl_out_edges[pt_nid];
	map<label, set<pt_node_index> >::iterator outei;
	for (outei = new_pt_out_edges.begin (); outei != new_pt_out_edges.end (); outei++)
	{
		label out_label = outei->first;
		set<pt_node_index> incl_out_nodes = outei->second;
	
		set<pt_node_index>::iterator ni;
		for (ni = incl_out_nodes.begin (); ni != incl_out_nodes.end (); ni++)
		{
			// No need to check whether OUT_N is valid or not. This
			// has already been done while computing NEW_IN_EDGES.
			pt_node_index out_n = *ni;
			DEBUG ("\nincl_out_edges %d->l=%d->%d", pt_nid, out_label, out_n);
	
			bool push_succ = push_an_edge (pt_nid, out_label, out_n,
				ext_bndry, nreach, summ_cmpts_map, new_pt_to_access_name);
			if (push_succ)
				new_succ_nodes.insert (out_n);
		}
	}

	// Computing APs of destination pt nodes using out-edges = E(g_pt) - EKill
	map<label, set<pt_node_index> > out_pt_edges = pt_n.get_out_edge_list ();
	map<label, set<pt_node_index> >::iterator ei;
	for (ei = out_pt_edges.begin (); ei != out_pt_edges.end (); ei++)
	{
		label out_label = ei->first;
		if (must_lptr.find (pt_nid) != must_lptr.end () && l == out_label)
		{
			DEBUG ("\nEdge from node=%d,l=%d killed by must_lptr", pt_nid, l);
			continue;
		}

		set<pt_node_index> out_nodes = ei->second;
		set<pt_node_index>::iterator ni;
		for (ni = out_nodes.begin (); ni != out_nodes.end (); ni++)
		{
			pt_node_index out_n = *ni;
			DEBUG ("\nout_pt-edges %d->l=%d->%d", pt_nid, out_label, out_n);

			// OUT_N is considered only if it is in Nin or newly created or unused heap.
			if (!pt_fi_node::is_node_valid_at_point (out_n, value_in.pt_nodes))
			{
				DEBUG ("\nnode=%d is invalid", out_n);
				continue;
			}

			bool push_succ = push_an_edge (pt_nid, out_label, out_n,
				ext_bndry, nreach, summ_cmpts_map, new_pt_to_access_name);
			if (push_succ)
				new_succ_nodes.insert (out_n);
		}
	}

	// Computing APs of destination pt nodes using out-edges = EGen from PT_N
	// If EGen (lptr x f x rpte) has an edge with PT_N in lptr.
	if (lptr.find (pt_nid) != lptr.end ())
	{
		DEBUG ("\npt-node=%d found in lptr", pt_nid);
		set<pt_node_index>::iterator ri;
		for (ri = rpte.begin (); ri != rpte.end (); ri++)
		{
			pt_node_index out_n = *ri;
			bool push_succ = push_an_edge (pt_nid, l, out_n,
				ext_bndry, nreach, summ_cmpts_map, new_pt_to_access_name);
			if (push_succ)
				new_succ_nodes.insert (out_n);
		}
	}
}
#endif

#if SUMM_TYPE_K && PULL_ACCESS_NAME == 0

/**
 * Compute AN from all AN of SRC_NID appended with OUT_LABEL. Add this to
 * DEST_NID. Do this only if required i.e. if AN of DEST_NID had been reset
 * i.e. if DEST_NID is in NREACH. This function is called for SRC_NID not in
 * EXT_VIS_NODES.
 * @return true if AN of DEST_NID needs to be pushed i.e. 
	(a) DEST_NID is in NREACH and its AN has changed
	(b) DEST_NID is not in NREACH and its AN needs to be pushed
 */

bool points_to_analysis_fi:: 
push_an_edge (pt_node_index src_nid,
	label out_label, 
	pt_node_index dest_nid,
	set<pt_node_index> & ext_bndry,
	set<pt_node_index> & nreach,
	map<pt_node_index, pt_node_index> & summ_cmpts_map,
	map<pt_node_index, access_name> & new_pt_to_access_name)
{
#if PUSH_FROM_ROOT
	// The AN of nreach nodes is reset. We need to recompute AN of dest_nid
	// only if it is in nreach.
	if (nreach.find (dest_nid) == nreach.end ())
		// We return true to indicate that AN of src_nid has been
		// propagated to dest_nid. This is required so that we can
		// traverse the whole subgraph under src_nid, where the
		// dest_nid is pushed in new_succ_nodes and its value is
		// propagated further.  Whether or not actually AN of dest_nid
		// needs to be pushed is checked using ext_vis_nodes.
		return true;
#else
	if (nreach.find (dest_nid) == nreach.end ())
		// We return false to indicate that AN of src_nid need not be
		// propagated to dest_nid because AN of dest_nid has not been
		// reset.
		return false;
#endif

	DEBUG ("\npush_an_edge: %d->%d->%d", src_nid, out_label, dest_nid);

	access_name dest_access_name;
#if SUMM_TYPE_K
	label dest_static_name = g_pt.get_node_name (dest_nid);
#endif

	pt_access_map.compute_ap (src_nid, out_label, dest_static_name, ext_bndry, g_ap, 
		dest_access_name, summ_cmpts_map, new_pt_to_access_name);
	
	access_name * dest_access_name_old = 
		pt_access_map.get_access_name (dest_nid, ext_bndry, summ_cmpts_map, new_pt_to_access_name);
	access_name dest_an_old;
	if (!dest_access_name_old)
		dest_access_name_old = &dest_an_old;

	// Set heap name as node_name_type for heap nodes.
//	if (g_pt.is_heap_node (dest_nid))
	{
		label node_name_type = g_pt.get_node_name (dest_nid);
		dest_access_name.add_node_name_type (node_name_type);
	}

	bool is_subset = dest_access_name.is_subset (*dest_access_name_old);
#if DEBUG_CONTAINER
	DEBUG ("\ndest_access_name_old=%d", dest_nid);
	dest_access_name_old->print (&g_ap);
	DEBUG ("\ndest_access_name=%d", dest_nid);
	dest_access_name.print (&g_ap);
	DEBUG ("\nedge %d->f=%d->%d new_an of dest is_subset=%d", src_nid, out_label, dest_nid, is_subset);
#endif

	if (!is_subset)
	{
		dest_access_name_old->add_access_name (dest_access_name);
		new_pt_to_access_name[dest_nid] = *dest_access_name_old;
		DEBUG ("\nSet dest_nid=%d", dest_nid);
	}

	// Push true if AN of DEST_NID has changed
	return !is_subset;
}
#endif

#if SUMM_K_CONSISTENT
void points_to_analysis_fi::
remove_wild_card_subsumed_aps (access_name & pt_access_name)
{
	set<ap_node_index> pt_ap_nids = pt_access_name.get_ap_nodes ();
	set<ap_node_index>::iterator api;
	g_ap.remove_wild_card_subsumed_aps (pt_ap_nids);
	pt_access_name.set_ap_nodes (pt_ap_nids);
}
#endif


#if SUMM_TYPE_CLOSURE
void points_to_analysis_fi::
set_ap_static_name (pt_node_index pt_nid,
	access_name & pt_access_name)
{
	// For SUMM_STMT_CLOSURE, stmt id info has been added to gAP (for summarization)
	// right now.  So this information becomes available when successor
	// field edges need to be appended to newly created access paths. This
	// availability is important so that repeating statement ids are not
	// created.

	// Therefore, corresondingly for !SUMM_STMT_CLOSURE, we add gPT node info to
	// gAP-to-gPT map for all gAP nodes (for summarization) right now, so
	// that this information becomes available when successor field edges
	// need to be appended to newly created access paths.

	// Note that PT_NID is being marked with pt_access_name.ap_nodes in
	// new_pt_to_access_name right now. However, later, a clone of PT_NID
	// will actually be marked with pt_access_name.ap_nodes in
	// pt_to_access_name. Since the heap type of PT_NID and its clone will
	// be same, it is okay to set the type of gAP nodes here only.

	label static_name = g_pt.get_node_name (pt_nid);
	set<ap_node_index> pt_ap_nids = pt_access_name.get_ap_nodes ();
	set<ap_node_index>::iterator ai;
	for (ai = pt_ap_nids.begin (); ai != pt_ap_nids.end (); ai++)
	{
		ap_node_index pt_ap_nid = *ai;

		ap_fi_node * apn = g_ap.nodes[pt_ap_nid];
		apn->add_static_name (static_name);

		#if DEBUG_CONTAINER
		csvarinfo_t var = VEC_index (csvarinfo_t, program.variable_data, static_name);
		DEBUG ("\nap=%d, new pt=%d, new static_name=%s(%d)", 
			pt_ap_nid, pt_nid, var->name, static_name);
		#endif
	}
}
#endif


void points_to_analysis_fi::
append_clone_map (map<pt_node_index, pt_node_index> & new_clone,
	context<pt_node_set, variables> & current_context)
{
	FUNBEGIN ();

	DEBUG ("\nappend_clone_map ()");

	map<pt_node_index, set<pt_node_index> > * clone = (map<pt_node_index, set<pt_node_index> > * )
		current_context.get_aux_info ();

	if (!clone)
	{
		RESULT ("\nError: Clone of context=%d is NULL", current_context.get_context_id ());
		RETURN_VOID ();
		// return;
	}

	map<pt_node_index, pt_node_index>::iterator ci;
	#pragma omp parallel for
	for (ci = new_clone.begin (); ci != new_clone.end (); ci++)
		(*clone)[ci->first].insert (ci->second);

	DEBUG ("\nClone of context=%d appended", current_context.get_context_id ());

	RETURN_VOID ();
}

void points_to_analysis_fi::
append_clone_map (map<pt_node_index, set<pt_node_index> > & new_clone,
	context<pt_node_set, variables> & current_context)
{
	FUNBEGIN ();
	DEBUG ("\nappend_clone_map (sets)");

	map<pt_node_index, set<pt_node_index> > * clone = (map<pt_node_index, set<pt_node_index> > * )
		current_context.get_aux_info ();

	if (!clone)
	{
		RESULT ("\nError: Clone of context=%d is NULL", current_context.get_context_id ());
		RETURN_VOID ();
		// return;
	}

	map<pt_node_index, set<pt_node_index> >::iterator ci;
	// #pragma omp parallel for
	for (ci = new_clone.begin (); ci != new_clone.end (); ci++)
	{
		set<pt_node_index> cids = ci->second;
		// (*clone)[ci->first].insert (cids.begin (), cids.end ());
		merge_set (cids, (*clone)[ci->first]);
	}
	
	RETURN_VOID ();
}

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
bool points_to_analysis_fi::
is_node_strictly_stronger (pt_node_index n1, 
	pt_node_index n2,
	set<pt_node_index> & valid_nodes)
{
	DEBUG ("\nis_node_strictly_stronger(n1=%d,n2=%d)", n1, n2);

	#if CHECK_CONTAINER
	if (!pt_fi_node::is_node_valid_at_point (n1, valid_nodes))
	{
		RESULT ("\nError: is_node_strictly_stronger() called for invalid node=%d", n1);
		return false;
	}
	#endif
	#if CHECK_CONTAINER
	if (!pt_fi_node::is_node_valid_at_point (n2, valid_nodes))
	{
		RESULT ("\nError: is_node_strictly_stronger() called for invalid node=%d", n2);
		return false;
	}
	#endif

	if (n1 == n2)
		return false;

	if (g_pt.is_node_strictly_stronger (n1, n2))
		return true;

	if (!is_node_ap_strictly_stronger (n1, n2))
		return false;

	// for all out-edges of n1
	pt_fi_node * n1_node = g_pt.nodes[n1];
	map<label, set<pt_node_index> > oute1 = n1_node->get_out_edge_list ();
	map<label, set<pt_node_index> >::iterator e1i;
	for (e1i = oute1.begin (); e1i != oute1.end (); e1i++)
	{
		label f = e1i->first;
		DEBUG ("\nedge %d->%d->", n1, f);
		// succ m1 of n1
		set<pt_node_index> m1_ids = e1i->second;
		set<pt_node_index>::iterator m1i;
		for (m1i = m1_ids.begin (); m1i != m1_ids.end (); m1i++)
		{
			pt_node_index m1 = *m1i;

			if (!pt_fi_node::is_node_valid_at_point (m1, valid_nodes))
			{
				DEBUG ("\ninvalid dest, edge %d->%d->%d", n1, f, m1);
				continue;
			}
				
			// find m2 stronger than m1, such that <n1,f,m1> is
			// strictly stronger than <n2,f,m2>
			bool found_m2 = false;
			set<pt_node_index>::iterator m2i;
			for (m2i = valid_nodes.begin (); m2i != valid_nodes.end (); m2i++)
			{
				pt_node_index m2 = *m2i;
				if (!is_node_stronger (m1, m2, valid_nodes))
					continue;
				if (!is_edge_compatible (n2, f, m2))
					continue;
				found_m2 = true;
				break;
			}
			if (!found_m2)
				return false;
		}
	}

	RESULT ("\nPO: n1=%d < n2=%d", n1, n2);
	g_pt.add_strictly_stronger_node (n1, n2);
	return true;
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
bool points_to_analysis_fi::
is_node_stronger (pt_node_index n1, 
	pt_node_index n2,
	set<pt_node_index> & valid_nodes)
{
	if (n1 == n2)
		return true;

	return is_node_strictly_stronger (n1, n2, valid_nodes);
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
bool points_to_analysis_fi::
is_node_ap_strictly_stronger (pt_node_index n1, pt_node_index n2)
{
	DEBUG ("\nis_node_ap_strictly_stronger(n1=%d,n2=%d)", n1, n2);
	
	if (n1 == n2)
		return false;

	// If node is a stack node, then return false.
	if (n1 == g_pt.stack.get_node_id ())
		return false;
	if (n2 == g_pt.stack.get_node_id ())
		return false;

	// If node is a fresh node, then return false.
	// Although a fresh node n1 can be subset of non-fresh node n2. But
	// dont kill fresh nodes. We do not want fields of fresh nodes to
	// become fields of non-fresh nodes. Also I dont know the implication
	// of killing specially fresh heap nodes.
	if (g_pt.is_fresh_named_node (n1) || g_pt.is_fresh_heap_node (n1))
		return false;
	if (g_pt.is_fresh_named_node (n2) || g_pt.is_fresh_heap_node (n2))
		return false;

	#if CHECK_CONTAINER
	if (pt_access_map.pt_to_access_name.find (n1) == 
		pt_access_map.pt_to_access_name.end ())
	{
		RESULT ("\nError: Access name of node=%d not found", n1);
		return false;
	}
	if (pt_access_map.pt_to_access_name.find (n2) == 
		pt_access_map.pt_to_access_name.end ())
	{
		RESULT ("\nError: Access name of node=%d not found", n2);
		return false;
	}
	#endif

	access_name n1_an = pt_access_map.pt_to_access_name[n1];
	access_name n2_an = pt_access_map.pt_to_access_name[n2];

	// If node has unbounded access path name, then return false.
	if (n1_an.is_ap_unbounded ())
		return false;
	// We do not allow merging even a bounded node n1 with an unbounded
	// node n2 because then spurious cycles are create even if they did not
	// exist. For example, if n1 points to n2 but there is no cycle on n2,
	// then replacing n1 with n2 creates a cycle on n2. To go further,
	// someone could say, any way a cycle on n2 will eventually get
	// created. So let us say x->n1->n2,y->n3->n1. Claim: n2 has repeating
	// fields on same access path with n1; this implies that eventually in
	// the next iteration, n2 will any way get a cycle. However, replacing
	// n1 with n2 is still bad because with the replacement, we will have
	// x->n2->n2,y->n3->n2, and without the replacement, we have
	// x->n1->n2->n2,y->n3->n1. The latter gives lesser spurious alias
	// pairs, eg. (x.0.0,y.0.0). So indeed a cycle on n2 will eventually
	// get created but not on the node immediately after n1.
	if (n2_an.is_ap_unbounded ())
		return false;

	if (!n1_an.is_subset (n2_an))
	{
		DEBUG ("\nAP PO: n1=%d /< n2=%d", n1, n2);
		return false;
	}

	DEBUG ("\nAP PO: n1=%d < n2=%d", n1, n2);
	return true;	
}
#endif

/**
 * This function checks if creating edge from m to n via f does not change the access name of n.
 * @returns true if it does not change the name.
 */

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
bool points_to_analysis_fi::
is_edge_strictly_stronger (label f,
	pt_node_index m1,
	pt_node_index n1, 
	pt_node_index m2,
	pt_node_index n2,
	set<pt_node_index> & valid_nodes)
{
	DEBUG ("\nis_edge_strictly_stronger(f=%d,m1=%d,n1=%d,m2=%d,n2=%d)", f, m1, n1, m2, n2);

	g_pt_edge e1 = make_pair (m1, make_pair (f, n1));
	g_pt_edge e2 = make_pair (m2, make_pair (f, n2));

	if (g_pt.is_edge_strictly_stronger (e1, e2))
		return true;
	
	if (m1 == m2 && n1 == n2)
		return false;

	if (!is_node_stronger (m1, m2, valid_nodes))
	{
		DEBUG ("\n!is_node_stronger (m1=%d,m2=%d)", m1, m2);
		return false;
	}
	if (!is_node_stronger (n1, n2, valid_nodes))
	{
		DEBUG ("\n!is_node_stronger (n1=%d,n2=%d)", n1, n2);
		return false;
	}

	if (!is_edge_compatible (m2, f, n2))
	{
		DEBUG ("\n!is_edge_compatible (m2=%d,f=%d,n2=%d)", m1, f, n2);
		return false;
	}

	DEBUG ("\nAdd strictly stronger edge <m2=%d,f=%d,n2=%d> in place <m1=%d,f=%d,n1=%d>",
		m2, f, n2, m1, f, n1);
	g_pt.add_strictly_stronger_edge (e1, e2);
	return true;
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
bool points_to_analysis_fi::
is_edge_compatible (pt_node_index m, label f, pt_node_index n)
{
	label n_static_name = 0;
	#if SUMM_TYPE_K
	n_static_name = g_pt.get_node_name (n);
	DEBUG ("\nn_static_name=%d, is_heap=%d", 
		n_static_name, program.heap_var (n_static_name));
	#endif

	// If node is in EXT_BNDRY, then its access paths are fetched from
	// PT_TO_ACCESS_NAME.  Else its access paths are fetched from
	// NEW_PT_TO_ACCESS_NAME.
	set<pt_node_index> ext_bndry;
	ext_bndry.insert (m);
	access_name edge_access_name;
	map<pt_node_index, pt_node_index> summ_cmpts_map;
	map<pt_node_index, access_name> new_pt_to_access_name;

	pt_access_map.compute_ap (m, f, n_static_name, ext_bndry, g_ap, 
		edge_access_name, summ_cmpts_map, new_pt_to_access_name);
	
	#if CHECK_CONTAINER
	if (pt_access_map.pt_to_access_name.find (n) 
		== pt_access_map.pt_to_access_name.end ())
	{
		RESULT ("\nError: Access name of node=%d not found", n);
		return false;
	}
	#endif

	access_name n_access_name = pt_access_map.pt_to_access_name[n];
#if DEBUG_CONTAINER
	DEBUG ("\naccess_name n=%d=", n);
	n_access_name.print (&g_ap);
	DEBUG ("\naccess_name m=%d->f=%d", m, f);
	edge_access_name.print (&g_ap);
#endif

	if (!edge_access_name.is_subset (n_access_name))
		return false;

	return true;
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
void points_to_analysis_fi::
kill_weak_access_nodes (pt_node_set & valid_nodes)
{
#if DEBUG_CONTAINER
	DEBUG ("\nValue=");
	valid_nodes.print_value (NULL);
#endif

	// We compute partial order considering the nodes only at a particular
	// program point (ignoring other nodes in g_pt).  Each program point
	// has a different partial order. We cannot use partial order computed
	// from some other program point. 
	// For example, g_pt=x->n1,z->m1,n1->m1,x->n2,y->n2.
	// For valid_nodes={n1,n2}, n1 <= n2.
	// For valid_nodes={n1,n2,m1}, n1 is not weaker than n2.
	g_pt.clear_partial_order_info ();
	// FIXME: If we compute partial order considering all the nodes in g_pt, we
	// would have a conservative partial order. However, then we could
	// reuse partial order information across program points. Partial order
	// of only those nodes needs to be cleared and recomputed whose
	// descendant nodes/edges have changed.

	set<pt_node_index> weak_access_nodes;
	set<pt_node_index> optimum_valid_nodes;
	find_weak_access_nodes (valid_nodes.pt_nodes, weak_access_nodes, optimum_valid_nodes);

	g_pt.record_weak_nodes_statistics (weak_access_nodes.size (), valid_nodes.pt_nodes.size ());

	// Don't perform the following if ACCESS_PARTIAL_ORDER=0 and PARTIAL_ORDER_STATISTICS=0
#if ACCESS_PARTIAL_ORDER
	set<pair<pt_node_index, pt_node_index> > old_fs_new_fi_edges;
	set<pt_node_index>::iterator n1i;
	RESULT ("\nkill_weak_access_nodes=");
	for (n1i = weak_access_nodes.begin (); n1i != weak_access_nodes.end (); n1i++)
	{
		pt_node_index n1 = *n1i;
		RESULT ("%d,", n1);
	}

	for (n1i = weak_access_nodes.begin (); n1i != weak_access_nodes.end (); n1i++)
	{
		pt_node_index n1 = *n1i;
		insert_strictly_stronger_edges (n1, valid_nodes.pt_nodes, optimum_valid_nodes, 
			old_fs_new_fi_edges);
	}
	DEBUG ("\nstronger edges inserted");

#if FI_REANALYSIS
	reanalyse_fi_dept_blocks (old_fs_new_fi_edges);
#endif

	valid_nodes.kill (weak_access_nodes);
	DEBUG ("\nkill_weak_acces_nodes done");
#endif
}
#endif

/**
 * This function finds all the weak access nodes in VALID_NODES. It also stores
 * in g_pt.strictly_stronger_nodes all the stronger nodes of the weak access
 * nodes.
 */

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
void points_to_analysis_fi::
find_weak_access_nodes (set<pt_node_index> & valid_nodes,
	set<pt_node_index> & weak_access_nodes,
	set<pt_node_index> & optimum_valid_nodes)
{
	DEBUG ("\nfind_weak_access_nodes()");

	set<pt_node_index>::iterator n1i;
	for (n1i = valid_nodes.begin (); n1i != valid_nodes.end (); n1i++)
	{
		pt_node_index n1 = *n1i;

		bool found_n2 = false;
		set<pt_node_index>::iterator n2i;
		for (n2i = valid_nodes.begin (); n2i != valid_nodes.end (); n2i++)
		{
			pt_node_index n2 = *n2i;
			if (!is_node_strictly_stronger (n1, n2, valid_nodes))
				continue;
			found_n2 = true;
			// Dont break. We want to find all strictly stronger
			// nodes of all valid nodes.
		}

		if (found_n2)
			weak_access_nodes.insert (n1);
		else
			// optimum_valid_nodes = valid_nodes - weak_access_nodes
			optimum_valid_nodes.insert (n1);
	}
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
void points_to_analysis_fi::
insert_strictly_stronger_edges (pt_node_index n1, 
	set<pt_node_index> & valid_nodes,
	set<pt_node_index> & optimum_valid_nodes,
	set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges)
{
	DEBUG ("\ninsert_strictly_stronger_edges()");

	// A previous call to find_weak_access_nodes() has already collected all
	// strictly stronger nodes of optimum_valid_nodes in
	// g_pt.strictly_stronger_nodes

	// for all n2 strictly stronger than n1
	set<pt_node_index> ssn1 = g_pt.get_strictly_stronger_nodes (n1);
	set<pt_node_index>::iterator n2i;
	for (n2i = ssn1.begin (); n2i != ssn1.end (); n2i++)
	{
		pt_node_index n2 = *n2i;
		if (!pt_fi_node::is_node_valid_at_point (n2, optimum_valid_nodes))
			continue;

		if (n1 == n2)
		{
			RESULT ("\nError: strictly stronger node of n1=%d is n1=%d itself", n1, n2);
			continue;
		}

		insert_strictly_stronger_out_edges (n1, n2, valid_nodes, optimum_valid_nodes, old_fs_new_fi_edges);
		insert_strictly_stronger_in_edges (n1, n2, valid_nodes, optimum_valid_nodes, old_fs_new_fi_edges);	
	}
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
void points_to_analysis_fi::
insert_strictly_stronger_out_edges (pt_node_index n1, 
	pt_node_index strictly_stronger_n1,
	set<pt_node_index> & valid_nodes,
	set<pt_node_index> & optimum_valid_nodes,
	set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges)
{
	DEBUG ("\ninsert_strictly_stronger_out_edges()");

	pt_node_index n2 = strictly_stronger_n1;

	pt_fi_node * n1_node = g_pt.nodes[n1];

	// for all out-edges of n1
	map<label, set<pt_node_index> >::iterator e1i;
	map<label, set<pt_node_index> > oute1 = n1_node->get_out_edge_list ();
	for (e1i = oute1.begin (); e1i != oute1.end (); e1i++)
	{
		label f = e1i->first;
		DEBUG ("\nedge %d->%d->", n1, f);

		// succ m1 of n1
		set<pt_node_index> m1_ids = e1i->second;
		set<pt_node_index>::iterator m1i;
		for (m1i = m1_ids.begin (); m1i != m1_ids.end (); m1i++)
		{
			pt_node_index m1 = *m1i;
			if (!pt_fi_node::is_node_valid_at_point (m1, optimum_valid_nodes))
				continue;
				
			// for all m2 stronger than m1
			set<pt_node_index> sm1 = g_pt.get_strictly_stronger_nodes (m1);
			sm1.insert (m1);
			set<pt_node_index>::iterator m2i;
			for (m2i = sm1.begin (); m2i != sm1.end (); m2i++)
			{
				pt_node_index m2 = *m2i;
				if (!pt_fi_node::is_node_valid_at_point (m2, optimum_valid_nodes))
					continue;

				replace_strictly_stronger_edge (f, n1, m1, n2, m2, 
					valid_nodes, old_fs_new_fi_edges);
			}
		}
	}
}
#endif

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
void points_to_analysis_fi::
insert_strictly_stronger_in_edges (pt_node_index n1, 
	pt_node_index strictly_stronger_n1,
	set<pt_node_index> & valid_nodes,
	set<pt_node_index> & optimum_valid_nodes,
	set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges)
{
	DEBUG ("\ninsert_strictly_stronger_in_edges()");

	pt_node_index n2 = strictly_stronger_n1;

	pt_fi_node * n1_node = g_pt.nodes[n1];

	// for all in-edges of n1
	map<label, set<pt_node_index> >::iterator e1i;
	map<label, set<pt_node_index> > ine1 = n1_node->get_in_edge_list ();
	for (e1i = ine1.begin (); e1i != ine1.end (); e1i++)
	{
		label f = e1i->first;
		DEBUG ("\nedge %d->%d->", n1, f);

		// succ m1 of n1
		set<pt_node_index> m1_ids = e1i->second;
		set<pt_node_index>::iterator m1i;
		for (m1i = m1_ids.begin (); m1i != m1_ids.end (); m1i++)
		{
			pt_node_index m1 = *m1i;
			if (!pt_fi_node::is_node_valid_at_point (m1, optimum_valid_nodes))
				continue;
				
			// for all m2 stronger than m1
			set<pt_node_index> sm1 = g_pt.get_strictly_stronger_nodes (m1);
			sm1.insert (m1);
			set<pt_node_index>::iterator m2i;
			for (m2i = sm1.begin (); m2i != sm1.end (); m2i++)
			{
				pt_node_index m2 = *m2i;
				if (!pt_fi_node::is_node_valid_at_point (m2, optimum_valid_nodes))
					continue;

				replace_strictly_stronger_edge (f, m1, n1, m2, n2, 
					valid_nodes, old_fs_new_fi_edges);
			}
		}
	}
}
#endif


/**
 * This function does not use optimum_valid_nodes since nodes to be replaced
 * (n1 and m1) may not be present in optimum_valid_nodes; in which case
 * is_node_strictly_stronger() will return error.
 */

#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
void points_to_analysis_fi::
replace_strictly_stronger_edge (label f, 
	pt_node_index m1, 
	pt_node_index n1, 
	pt_node_index m2, 
	pt_node_index n2, 
	set<pt_node_index> & valid_nodes,
	set<pair<pt_node_index, pt_node_index> > & old_fs_new_fi_edges)
{
	DEBUG ("\nreplace_strictly_stronger_edge()");

	if (!is_edge_strictly_stronger (f, m1, n1, m2, n2, valid_nodes))
		return;

	pt_fi_node * m2_node = g_pt.nodes[m2];
	pt_fi_node * n2_node = g_pt.nodes[n2];
	
	// Add strictly_stronger edge <m2,f,n2> of <m1,f,n1>
	pt_node_index stack_id = g_pt.stack.get_node_id ();
	if (m2_node->insert_edge (f, *n2_node, stack_id))
	{
#if FI_REANALYSIS
		// Reanalyze program points if this edge is newly added
		int old_max_node_id = g_pt.get_max_node_id ();
		add_old_fs_new_fi_edge (m2, n2,	old_max_node_id, old_fs_new_fi_edges);
#endif
	}
}
#endif

void points_to_analysis_fi::
delete_aux_info (void * aux_info)
{
#if GC
	if (aux_info)
		delete (map<pt_node_index, set<pt_node_index> > *)aux_info;
#endif
}

void points_to_analysis_fi::
print_clone_map (map<pt_node_index, pt_node_index> & clone)
{
	map<pt_node_index, pt_node_index>::iterator ci;
	for (ci = clone.begin (); ci != clone.end (); ci++)
		RESULT ("\n%d=%d", ci->first, ci->second);
}

void points_to_analysis_fi::
print_clone_map (map<pt_node_index, set<pt_node_index> > & clone)
{
	map<pt_node_index, set<pt_node_index> >::iterator ci;
	for (ci = clone.begin (); ci != clone.end (); ci++)
	{
		pt_node_index c1 = ci->first;
		RESULT ("\n%d=", c1);
		set<pt_node_index> c2 = ci->second;
		set<pt_node_index>::iterator c2i;
		for (c2i = c2.begin (); c2i != c2.end (); c2i++)
			RESULT ("%d,", *c2i);
	}
}

void points_to_analysis_fi::
print_value (pt_node_set & ptn)
{
	FUNBEGIN ();

#ifdef DOT_FILE
	FILE * file = fopen (DOT_FILE, "a"); 
	fprintf (file, "\n"); 
	fclose (file); 
	file = fopen (DOT_FILE, "a"); 

	set<pt_node_index> ptr_pte = g_pt.print_subgraph (file, ptn.pt_nodes);

	fclose (file);
#else
	set<pt_node_index> ptr_pte = g_pt.print_subgraph (NULL, ptn.pt_nodes);
#endif

	pt_access_map.print_submap (ptr_pte, g_ap);

	pt_node_index stack_id = g_pt.stack.get_node_id ();

	set<pt_node_index>::iterator ni;
	RESULT ("\n\n{");
	for (ni = ptn.pt_nodes.begin (); ni != ptn.pt_nodes.end (); ni++)
	{
		pt_node_index nid = *ni;
		if (nid == stack_id)
		{
			RESULT ("%d,", nid);
			continue;
		}
		pt_fi_node * n = g_pt.nodes[nid];
#if SUMM_K_CONSISTENT
		set<csvarinfo_t> vars;
		n->get_all_varinfos (stack_id, vars);
		set<csvarinfo_t>::iterator vi;
		for (vi = vars.begin (); vi != vars.end (); vi++)
		{
			csvarinfo_t var = *vi;
			RESULT ("(%s)%d,", var->name, nid);
		}		
#else
		csvarinfo_t var;
		n->get_node_varinfo (stack_id, var);
		RESULT ("(%s)%d,", var->name, nid);
#endif
	}
	RESULT ("}");
	RESULT ("\n{");
	for (ni = ptn.pt_nodes.begin (); ni != ptn.pt_nodes.end (); ni++)
		RESULT ("%d,", *ni);
	RESULT ("}\n");

//	g_ap.print_graph (NULL);

	RETURN_VOID ();
}

void points_to_analysis_fi::
get_useful_aps (//set<pt_node_index> & in_values,
	unsigned int index,
	bool is_assignment_index,
	set<ap_node_index> & useful_ap_nodes,
	set<list<label> > & useful_ap_paths)
	// set<pt_node_index> & useful_pt_nodes
{
	DEBUG ("\nget_useful_aps ()");

	// Use data index

	if (!is_assignment_index)
	{
		csvarinfo_t var = VEC_index (csvarinfo_t, program.variable_data, index);

		// g_pt.generate_addressof_nodes (var->id, useful_pt_nodes);
		// set<pt_node_index> temp_pt_nodes;
		// generate_pointer_nodes (var->id, NULL, temp_pt_nodes);
		// useful_pt_nodes.insert (temp_pt_nodes.begin (), temp_pt_nodes.end ());

		list<label> useful_path;
		useful_path.push_back (var->id);
		useful_path.push_back (ASTERISK);
		// No need to append offset sequence.
		// (a) int D.1234=x->d; return D.1234; No need to find aliases of x->d as d is non-integer.
		// (b) int * D.1234=x->p; return D.1234; x->p is covered in assignment statement -- not here.
		g_ap.get_ap_nodes (useful_path, useful_ap_nodes);
		useful_ap_paths.insert (useful_path);

		set<ap_node_index>::iterator ai;

#if DEBUG_CONTAINER
		DEBUG ("\nget_useful_aps()=var=%s(%d),ap_nids=", var->name, var->id);
		for (ai = useful_ap_nodes.begin (); ai != useful_ap_nodes.end (); ai++)
			DEBUG ("%d,", *ai);
#endif

		return;
	}

	// Assignment data index

	constraint_t assignment = 
		VEC_index (constraint_t, program.assignment_data, index);
	constraint_expr lhs = assignment->lhs;
	constraint_expr rhs = assignment->rhs;	
	// Ignore PHI statements of the following type
	if (lhs.var == rhs.var && lhs.type == rhs.type && lhs.offset == rhs.offset)
		return;

	DEBUG ("\nlhs=%d->%lld (%d), rhs=%d->%lld (%d)", lhs.var, lhs.offset, lhs.type,
		rhs.var, rhs.offset, rhs.type);

	// We cannot collect nodes in all summarization techniques. For
	// example, k-limited technique may not have K long path in gAP.
	// Therefore, we work only with useful_lhs/rhs_ap_paths and not _nodes.

	// set<pt_node_index> useful_lhs_pt, useful_rhs_pt;
	set<ap_node_index> useful_lhs_ap_nodes, useful_rhs_ap_nodes;
	set<list<label> > useful_lhs_ap_paths, useful_rhs_ap_paths;

	// get_useful_lhs_pt_ap_nodes (in_values, lhs, useful_lhs_ap, useful_lhs_pt);
	// useful_pt_nodes.insert (useful_lhs_pt.begin (), useful_lhs_pt.end ());
	get_useful_lhs_ap_nodes (lhs, useful_lhs_ap_nodes, useful_lhs_ap_paths);
	// useful_ap_nodes.insert (useful_lhs_ap.begin (), useful_lhs_ap.end ());
	merge_set (useful_lhs_ap_nodes, useful_ap_nodes);
	merge_set (useful_lhs_ap_paths, useful_ap_paths);

	// get_useful_rhs_pt_ap_nodes (in_values, rhs, useful_rhs_ap, useful_rhs_pt);
	// useful_pt_nodes.insert (useful_rhs_pt.begin (), useful_rhs_pt.end ());
	get_useful_rhs_ap_nodes (rhs, useful_rhs_ap_nodes, useful_rhs_ap_paths);
	// useful_ap_nodes.insert (useful_rhs_ap.begin (), useful_rhs_ap.end ());
	merge_set (useful_rhs_ap_nodes, useful_ap_nodes);
	merge_set (useful_rhs_ap_paths, useful_ap_paths);

#if DEBUG_CONTAINER
	DEBUG ("\nget_useful_aps(),ap_nids=");
	set<ap_node_index>::iterator ai;
	for (ai = useful_ap_nodes.begin (); ai != useful_ap_nodes.end (); ai++)
		DEBUG ("%d,", *ai);
#endif

	DEBUG ("\ng_ap.get_access_paths()");
//	g_ap.get_access_paths (useful_ap_nodes, useful_ap_paths);

#if DEBUG_CONTAINER
	set<ap_node_index>::iterator api;
	DEBUG ("\nuseful_lhs_aps=");
	for (api = useful_lhs_ap_nodes.begin (); api != useful_lhs_ap_nodes.end (); api++)
	{
		list<label> ap;
		ap_node_index apnid = *api;
		g_ap.get_access_paths (apnid, ap);
		DEBUG ("\n\t");
		g_ap.print_access_path (ap);
	}
	DEBUG ("\nuseful_rhs_aps=");
	for (api = useful_rhs_ap_nodes.begin (); api != useful_rhs_ap_nodes.end (); api++)
	{
		list<label> ap;
		ap_node_index apnid = *api;
		g_ap.get_access_paths (apnid, ap);
		DEBUG ("\n\t");
		g_ap.print_access_path (ap);
	}
#endif
}

void points_to_analysis_fi::
get_useful_rhs_ap_nodes (// set<pt_node_index> & in_values,
	constraint_expr & rhs,
	set<ap_node_index> & rhs_ap_nodes,
	set<list<label> > & rhs_ap_paths)
	// set<pt_node_index> & rhs_pt_nodes
{
	list<label> rhs_path;

	switch (rhs.type)
	{
	// lhs=rhs or lhs=&(rhs->f)
	// or
	// *lhs=rhs or lhs->f=rhs or *lhs=&(rhs->f) or lhs->f=&(rhs->f)
	case SCALAR:
	{
		DEBUG ("\nrhs.type == SCALAR");
		// g_pt.generate_addressof_nodes (rhs.var, rhs_pt_nodes);
		// set<pt_node_index> temp_rhs_pt_nodes;
		// generate_pointer_nodes (rhs.var, NULL, temp_rhs_pt_nodes);
		// rhs_pt_nodes.insert (temp_rhs_pt_nodes.begin (), temp_rhs_pt_nodes.end ());
		// temp_rhs_pt_nodes.clear ();
		// generate_pointer_nodes (rhs.var, rhs.offset_sequence, temp_rhs_pt_nodes);
		// rhs_pt_nodes.insert (temp_rhs_pt_nodes.begin (), temp_rhs_pt_nodes.end ());

		rhs_path.push_back (rhs.var);
		rhs_ap_paths.insert (rhs_path);
		rhs_path.push_back (ASTERISK);
		rhs_ap_paths.insert (rhs_path);
		list<label>::iterator li;
		if (rhs.offset_sequence)
		{
#if MERGE_NON_POINTER_FIELDS
			rhs_path.push_back (rhs.offset);
			rhs_ap_paths.insert (rhs_path);
#else
			for (li = rhs.offset_sequence->begin (); li != rhs.offset_sequence->end (); li++)
				if (*li)
				{
					rhs_path.push_back (*li);
					rhs_ap_paths.insert (rhs_path);
				}
#endif
		}
//		g_ap.get_ap_nodes (rhs_path, rhs_ap_nodes);

		break;
	}

	// lhs=&rhs
	// or
	// *lhs=&rhs or lhs->f=&rhs
	case ADDRESSOF:
		DEBUG ("\nrhs.type == ADDRESSOF");
		break;

	// lhs=*rhs or lhs=rhs->f
	// or
	// *lhs=*rhs or lhs->f=rhs->f or ...
	// Such a statement exists in mcf benchmark.
	// Function suspend_impl <bb 13> *new_arc_6 = *arc_7;
	case DEREF:
	{
		DEBUG ("\nrhs.type == DEREF");
		// g_pt.generate_addressof_nodes (rhs.var, rhs_pt_nodes);
		// set<pt_node_index> temp_rhs_pt_nodes;
		// generate_pointer_nodes (rhs.var, NULL, temp_rhs_pt_nodes);
		// rhs_pt_nodes.insert (temp_rhs_pt_nodes.begin (), temp_rhs_pt_nodes.end ());
		// temp_rhs_pt_nodes.clear ();
		// generate_pointer_nodes (rhs.var, rhs.offset_sequence, temp_rhs_pt_nodes);
		// rhs_pt_nodes.insert (temp_rhs_pt_nodes.begin (), temp_rhs_pt_nodes.end ());
		// temp_rhs_pt_nodes.clear ();
		// g_pt.generate_deref_nodes (rhs.var, rhs.offset_sequence, temp_rhs_pt_nodes);
		// rhs_pt_nodes.insert (temp_rhs_pt_nodes.begin (), temp_rhs_pt_nodes.end ());

		rhs_path.push_back (rhs.var);
		rhs_ap_paths.insert (rhs_path);
		rhs_path.push_back (ASTERISK);
		rhs_ap_paths.insert (rhs_path);
		list<label>::iterator li;
		if (rhs.offset_sequence)
		{
#if MERGE_NON_POINTER_FIELDS
			rhs_path.push_back (rhs.offset);
			rhs_ap_paths.insert (rhs_path);
#else
			for (li = rhs.offset_sequence->begin (); li != rhs.offset_sequence->end (); li++)
				if (*li)
				{
					rhs_path.push_back (*li);
					rhs_ap_paths.insert (rhs_path);
				}
#endif
		
			rhs_path.push_back (ASTERISK);
			rhs_ap_paths.insert (rhs_path);
		}
//		g_ap.get_ap_nodes (rhs_path, rhs_ap_nodes);

		break;
	}
	default:
		RESULT ("\nError: rhs.type cannot hold a fourth type");
	}

	// get_nodes_valid_at_point (rhs_pt_nodes, in_values);
}

void points_to_analysis_fi::
get_useful_lhs_ap_nodes (// set<pt_node_index> & in_values,
	constraint_expr & lhs,
	set<ap_node_index> & lhs_ap_nodes,
	set<list<label> > & lhs_ap_paths)
	// set<pt_node_index> & lhs_pt_nodes
{

	list<label> lhs_path;

	switch (lhs.type)
	{
	// lhs=...
	case SCALAR:
	{
		DEBUG ("\nlhs.type == SCALAR");
		break;
	}

        // lhs->f=... or *lhs=...
	case DEREF:
	{
		DEBUG ("\nlhs.type == DEREF");
		// g_pt.generate_addressof_nodes (lhs.var, lhs_pt_nodes);
		// set<pt_node_index> temp_lhs_pt_nodes;
		// generate_pointer_nodes (lhs.var, NULL, temp_lhs_pt_nodes);
		// lhs_pt_nodes.insert (temp_lhs_pt_nodes.begin (), temp_lhs_pt_nodes.end ());

		lhs_path.push_back (lhs.var);
		lhs_ap_paths.insert (lhs_path);
		if (lhs.offset_sequence && lhs.offset_sequence->size ())
		{
			lhs_path.push_back (ASTERISK);
			lhs_ap_paths.insert (lhs_path);
		}
//		g_ap.get_ap_nodes (lhs_path, lhs_ap_nodes);

		break;
	}

	case ADDRESSOF:
		DEBUG ("\nlhs.type == ADDRESSOF");
		break;

	default:
		RESULT ("\nError: lhs.type cannot hold a fourth type");
	}

	// get_nodes_valid_at_point (lhs_pt_nodes, in_values);
}

/* 
 * Different contexts might generate the same points-to pairs. A points-to pair
 * may appear in multiple contexts at a program point.  However, for each use
 * of variable x in the basic block (IN_VALUES), we print its points-to pairs
 * only once.  This is because context is analysis specific and the user is
 * concerned only with the points-to information of x at the program point.
 * However, we should not eliminate repetition due to multiple uses in a block
 * (REPEATING_USEFUL_ALIAS_PAIRS). 
 * Even if we have one statement per block, there could be multiple uses ---
 * use of same variable on both lhs and rhs, or multiple use of same variable
 * on rhs due to structures (x=z; becomes x.f=z.f;x.g=z.g;...).
 */

void points_to_analysis_fi::
get_useful_ap_alias_set (map<list<label>, set<list<label> > > & in_ap_alias_set,
	basic_block current_block,
	map<list<label>, list<list<label> > > & repeating_useful_ap_alias_set)
{
	unsigned int block_type = ((block_information *)(current_block->aux))->get_block_type ();
        DEBUG ("\nBlock %d, block type %d", current_block->index, block_type);

#if DEBUG_CONTAINER
        // Print statements of the block
        gimple_stmt_iterator gsi;
        DEBUG ("\n");
        for (gsi = gsi_start_bb (current_block); !gsi_end_p (gsi); gsi_next (&gsi))
                print_gimple_stmt (dump_file, gsi_stmt (gsi), 0, 0);
#endif

        list<pair<unsigned int, bool> > parsed_data_indices =
                ((block_information *)(current_block->aux))->get_parsed_data_indices ();

        // Iterate in forward direction for points-to analysis
        list<pair<unsigned int, bool> >::iterator it;
        for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
        {
                unsigned int index = (*it).first;
                bool is_assignment = (*it).second;
                DEBUG ("\nParsed data: index %d, bool %d, ", index, is_assignment);

		set<ap_node_index> useful_ap_nodes;
		set<list<label> > useful_ap_paths;
		// set<pt_node_index> useful_pt_nodes;

       		// get_useful_pt_ap_nodes (in_values, index, is_assignment, useful_ap_nodes, useful_pt_nodes);
       		get_useful_aps (index, is_assignment, useful_ap_nodes, useful_ap_paths);

#if DEBUG_CONTAINER
		// set<pt_node_index>::iterator pi;
		// DEBUG ("\nUseful pt nodes=");
		// for (pi = useful_pt_nodes.begin (); pi != useful_pt_nodes.end (); pi++)
		// {
		// 	label useful_var = g_pt.get_node_name (*pi);
		// 	csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, useful_var);
		// 	DEBUG ("%s(%d,%d),", v_info->name, useful_var, *pi);
		// }
		set<ap_node_index>::iterator apsi;
		DEBUG ("\nUseful ap=");
		for (apsi = useful_ap_nodes.begin (); apsi != useful_ap_nodes.end (); apsi++)
		{
			list<label> ap;
			ap_node_index apnid = *apsi;
			g_ap.get_access_paths (apnid, ap);
			DEBUG ("\n\tap=%d=", apnid);
			g_ap.print_access_path (ap);
		}
#endif
	
		// Count an alias pair as many times as it is useful
		map<list<label>, set<list<label> > > useful_ap_alias_set;
                map<list<label>, set<list<label> > >::iterator api;
                for (api = in_ap_alias_set.begin (); api != in_ap_alias_set.end (); api++)
		{
			list<label> ap = api->first;
			if (!is_useful_path (ap, useful_ap_paths))
                                continue;

                        set<list<label> > aps = api->second;
                        set<list<label> >::iterator li;
                        for (li = aps.begin (); li != aps.end (); li++)
                                if (*li != ap)
                                        repeating_useful_ap_alias_set[ap].push_back (*li);
                }
	}
}

/** 
 * Find max length of the acyclic paths reaching PNID. An edge is added to
 * VISITED_EDGES every time for every new access path. This has become
 * possible because it is not passed as reference. 
 *
 * This function basically pushes the length of the AP of PNID to its
 * destination nodes by adding 1. It then recursively calls this function on
 * its destination nodes. This is done until every edge is covered exactly once
 * (visited_edges) along every access path.
 *
 * Note: We have considered visited_edges instead of visited_nodes because
 * the latter misses out counting back edges in an AP.
 *
 * TODO: Improve efficiency. Takes around 5hours at each program point in
 * test45.c with both VISITED_EDGES and VISITED_NODES.
 */

unsigned int points_to_analysis_fi::
get_max_acyclic_ap_len (set<pt_node_index> & pt_nodes)
{
	DEBUG ("\nget_max_acyclic_ap_len()");

	map<pt_node_index, unsigned int> max_acyclic_len;
	DEBUG ("\nstack-id=%d", g_pt.stack.get_node_id ());

//	map<pt_node_index, map<label, set<pt_node_index> > > visited_edges;
//	get_max_acyclic_ap_len (g_pt.stack.get_node_id (), 0, pt_nodes, 
//		visited_edges, max_acyclic_len);

//	set<pt_node_index> visited_nodes;
//	get_max_acyclic_ap_len (g_pt.stack.get_node_id (), 0, pt_nodes, 
//		visited_nodes, max_acyclic_len);

	set<pt_node_index> visited_nodes;
	get_max_acyclic_ap_len (g_pt.stack.get_node_id (), pt_nodes, 
		visited_nodes, max_acyclic_len);

	DEBUG ("\nmax_acyclic_len=");
	map<pt_node_index, unsigned int>::iterator ci;
	unsigned int count = 0;
	for (ci = max_acyclic_len.begin (); ci != max_acyclic_len.end (); ci++)
	{
		unsigned int new_count = ci->second;
#if DEBUG_CONTAINER
		DEBUG ("\n(pnid=%d,%d)", ci->first, new_count);
#endif
		if (count < new_count)
			count = new_count;
	}

	RESULT ("\nlocal_max_acyclic_len=%d", count);
	return count;
}

/** 
 * Using VISITED_EDGES
 *
 * PNID_CURR_LEN: Each occurrence of PNID in a different AP has a different
 * PNID_CURR_LEN (length of acyclic AP reaching in that AP). PNID_CURR_LEN
 * should match the sequence of activation records followed for the current AP;
 * otherwise, every new AP passing through PNID will add to the length computed
 * from an old AP passing through PNID.
 */

void points_to_analysis_fi::
get_max_acyclic_ap_len (pt_node_index pnid, 
	unsigned int pnid_curr_len,
	set<pt_node_index> & valid_nodes,
	map<pt_node_index, map<label, set<pt_node_index> > > visited_edges, 
	map<pt_node_index, unsigned int> & max_acyclic_len)
{
	DEBUG ("\nget_max_acyclic_ap_len(pnid=%d)", pnid);

	unsigned int pnid_old_len = max_acyclic_len[pnid];
	if (pnid_old_len < pnid_curr_len)
	{
		max_acyclic_len[pnid] = pnid_curr_len;
		DEBUG ("\npnid=%d,old=%d,curr=%d,max=%d", 
			pnid, pnid_old_len, pnid_curr_len, pnid_curr_len);
	}
	else
		DEBUG ("\npnid=%d,old=%d,curr=%d,max=%d", 
			pnid, pnid_old_len, pnid_curr_len, pnid_old_len);

	map<label, set<pt_node_index> > visited_out_edges;
	if (visited_edges.find (pnid) != visited_edges.end ())
		visited_out_edges = visited_edges[pnid];

	pt_fi_node * pt_n = g_pt.nodes[pnid];
	map<label, set<pt_node_index> >::iterator ei;
	map<label, set<pt_node_index> > oute;
	oute = pt_n->get_out_edge_list ();
	for (ei = oute.begin (); ei != oute.end (); ei++)
	{
		label l = ei->first;

		set<pt_node_index> visited_dests;
		if (visited_out_edges.find (l) != visited_out_edges.end ())
			visited_dests = visited_out_edges[l];

		DEBUG ("\nedge %d->%d->", pnid, l);
		set<pt_node_index> dests = ei->second;
		set<pt_node_index>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
			if (visited_dests.find (*di) == visited_dests.end ())
				DEBUG ("%d,", *di);
		for (di = dests.begin (); di != dests.end (); di++)
		{
			pt_node_index dest = *di;

			if (visited_dests.find (dest) != visited_dests.end ())
				continue;

			if (!pt_fi_node::is_node_valid_at_point (dest, valid_nodes))
			{
				DEBUG ("\ninvalid dest, edge %d->%d->%d", pnid, l, dest);
				continue;
			}
				
			map<pt_node_index, map<label, set<pt_node_index> > > vis = visited_edges;
			vis[pnid][l].insert (dest);
			DEBUG ("\nvisited=%d->l=%d->%d", pnid, l, dest);

			get_max_acyclic_ap_len (dest, pnid_curr_len + 1, valid_nodes, 
				vis, max_acyclic_len);
		}
	}
}

/** 
 * Using VISITED_NODES (unique per path of the graph / sequence of activation
 * records). This function collects the depth of each node (i.e. the max number
 * of dereferences that reach each node).
 */

void points_to_analysis_fi::
get_max_acyclic_ap_len (pt_node_index pnid, 
	unsigned int pnid_curr_len,
	set<pt_node_index> & valid_nodes,
	set<pt_node_index> visited_nodes,
	map<pt_node_index, unsigned int> & max_acyclic_len)
{
	if (visited_nodes.find (pnid) != visited_nodes.end ())
		return;

	visited_nodes.insert (pnid);

	DEBUG ("\nget_max_acyclic_ap_len(pnid=%d)", pnid);

	unsigned int pnid_old_len = max_acyclic_len[pnid];
	if (pnid_old_len < pnid_curr_len)
	{
		max_acyclic_len[pnid] = pnid_curr_len;
		DEBUG ("\npnid=%d,old=%d,curr=%d,max=%d", 
			pnid, pnid_old_len, pnid_curr_len, pnid_curr_len);
	}
	else
		DEBUG ("\npnid=%d,old=%d,curr=%d,max=%d", 
			pnid, pnid_old_len, pnid_curr_len, pnid_old_len);

	pt_fi_node * pt_n = g_pt.nodes[pnid];
	map<label, set<pt_node_index> >::iterator ei;
	map<label, set<pt_node_index> > oute;
	oute = pt_n->get_out_edge_list ();
	for (ei = oute.begin (); ei != oute.end (); ei++)
	{
		label l = ei->first;

		DEBUG ("\nedge %d->%d->", pnid, l);
		set<pt_node_index> dests = ei->second;
		set<pt_node_index>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
			if (visited_nodes.find (*di) == visited_nodes.end ())
				DEBUG ("%d,", *di);
		for (di = dests.begin (); di != dests.end (); di++)
		{
			pt_node_index dest = *di;

//			if (visited_nodes.find (dest) != visited_nodes.end ())
//				continue;

			if (!pt_fi_node::is_node_valid_at_point (dest, valid_nodes))
			{
				DEBUG ("\ninvalid dest, edge %d->%d->%d", pnid, l, dest);
				continue;
			}
				
//			set<pt_node_index> vis = visited_nodes;
//			vis.insert (dest);
//			get_max_acyclic_ap_len (dest, pnid_curr_len + 1, valid_nodes, 
//				vis, max_acyclic_len);

			get_max_acyclic_ap_len (dest, pnid_curr_len + 1, valid_nodes, 
				visited_nodes, max_acyclic_len);
		}
	}
}

/** 
 * Using VISITED_NODES (passed as reference). This is actual depth first algo. 
 *
 * This function collects the height of each node (i.e. the number of
 * dereferences that succeed each node up till the leaf). The height may not be
 * the max possible height of the graph. This is because we use DFS (i.e. do
 * not revisit an already visited node) on our non-regular gPT graph (that
 * where the nodes in a loop have multiple in-edges). Therefore, effectively
 * some random back edges/cycles get removed to form one of the many possible
 * spanning trees that can be constructed out of the graph. This spanning tree
 * may not have the longest path possible from the graph. Therefore, the height
 * calculated is not the maximum possible. Note that a regular graph has only
 * one possible spanning tree but our graphs are non-regular.
 *
 * HEIGHT[] is needed so that if a node is revisited, its previously computed
 * height can be recalled.
 * Cycles in DAG have a problem that if a successor is already visited but its
 * height is not yet computed, then current incompletely computed height gets
 * used. A height of a node would not yet have been computed if the node is in
 * a cycle. 
 */

void points_to_analysis_fi::
get_max_acyclic_ap_len (pt_node_index pnid, 
	set<pt_node_index> & valid_nodes,
	set<pt_node_index> & visited_nodes,
	map<pt_node_index, unsigned int> & height)
{
	if (visited_nodes.find (pnid) != visited_nodes.end ())
		return;

	DEBUG ("\nget_max_acyclic_ap_len(pnid=%d)", pnid);

	visited_nodes.insert (pnid);
	height[pnid] = 1;

	unsigned int pnid_old_height = height[pnid];

	pt_fi_node * pt_n = g_pt.nodes[pnid];
	map<label, set<pt_node_index> >::iterator ei;
	map<label, set<pt_node_index> > oute;
	oute = pt_n->get_out_edge_list ();
	for (ei = oute.begin (); ei != oute.end (); ei++)
	{
		label l = ei->first;

		DEBUG ("\nedge %d->%d->", pnid, l);
		set<pt_node_index> dests = ei->second;
		set<pt_node_index>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
			if (visited_nodes.find (*di) == visited_nodes.end ())
				DEBUG ("%d,", *di);
		for (di = dests.begin (); di != dests.end (); di++)
		{
			pt_node_index dest = *di;

			if (!pt_fi_node::is_node_valid_at_point (dest, valid_nodes))
			{
				DEBUG ("\ninvalid dest, edge %d->%d->%d", pnid, l, dest);
				continue;
			}

			get_max_acyclic_ap_len (dest, valid_nodes, visited_nodes, height);

			if (pnid_old_height < height[dest] + 1)
			{
				height[pnid] = height[dest] + 1;
				pnid_old_height = height[pnid];
				DEBUG ("\nheight[pnid=%d]=%d, height[dest=%d]=%d",
					pnid, height[pnid], dest, height[dest]);
			}
		}
	}
}
void points_to_analysis_fi::
get_access_paths (set<pt_node_index> & ptn,
	map<pt_node_index, set<list<label> > > & node_aps,
	bool is_k)
{
	set<pt_node_index>::iterator ni;
#if DEBUG_CONTAINER
	DEBUG ("\nget_access_paths(), ptn=");
	for (ni = ptn.begin (); ni != ptn.end (); ni++)
		DEBUG ("%d,", *ni);
#endif
	
	for (ni = ptn.begin (); ni != ptn.end (); ni++)
	{
		pt_node_index pnid = *ni;
		if (is_k)
		{
			get_k_access_paths (pnid, ptn, node_aps);
			continue;
		}
	
		// !is_k	

		if (pt_access_map.pt_to_access_name.find (pnid) == 
			pt_access_map.pt_to_access_name.end ())
		{
			RESULT ("\nError: Cannot find access_name of ptnid=%d in get_access_paths", pnid);
			return;
		}

		set<ap_node_index> ap_nids = pt_access_map.get_ap_nodes (pnid);
		set<ap_node_index>::iterator api;
		for (api = ap_nids.begin (); api != ap_nids.end (); api++)
		{
			ap_node_index apnid = *api;
			list<label> ap;
			g_ap.get_access_paths (apnid, ap);
			node_aps[pnid].insert (ap);
		}
	}
}

bool points_to_analysis_fi::
is_ap_valid_alias (list<label> & ap1)
{
        label l1;

        // Ignore if heap path
        l1 = *(ap1.begin ());
        if (program.heap_var (l1))
                return false;

        // Ignore if var followed by field edge, eg x->32. This alias pair will
        // get captured with x.32+32 var.
        label l1_next = 0;
        if (l1 && ap1.size () > 1)
        {
                l1_next = *(++ap1.begin ());
                DEBUG ("\nl1=%d, l1_next=%d", l1, l1_next);
                if (l1_next) return false;
        }
        return true;
}

/** 
 * This function basically pushes the access paths of VAR to its destination
 * nodes by appending the out-edge field to the access paths of VAR. It then
 * recursively calls this function on its destination nodes. This is done upto
 * k length of every access path.
 */

void points_to_analysis_fi::
get_k_access_paths (pt_node_index pnid,
	set<pt_node_index> & valid_nodes,
	map<pt_node_index, set<list<label> > > & node_aps)
{
	if (pnid == g_pt.stack.get_node_id ())
		return;
	DEBUG ("\nget_k_access_paths(pnid=%d)", pnid);
#if SUMM_K_CONSISTENT
	set<label> vars;
	pt_fi_node * n = g_pt.nodes[pnid];
	n->get_all_names (g_pt.stack.get_node_id (), vars);
	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
	{
		list<label> base_ap;
		base_ap.push_back (*vi);
		if (is_ap_valid_alias (base_ap))
			node_aps[pnid].insert (base_ap);
	}
#else
	label var = g_pt.get_node_name (pnid);
        csvarinfo_t vinfo = VEC_index (csvarinfo_t, program.variable_data, var);
        if (vinfo && vinfo->decl && DECL_ARTIFICIAL (vinfo->decl))
                return;

	list<label> base_ap;
	base_ap.push_back (var);

	if (is_ap_valid_alias (base_ap))
		node_aps[pnid].insert (base_ap);
#endif

	pt_fi_node * pt_n = g_pt.nodes[pnid];
	map<label, set<pt_node_index> >::iterator ei;
	map<label, set<pt_node_index> > oute;
	oute = pt_n->get_out_edge_list ();
	for (ei = oute.begin (); ei != oute.end (); ei++)
	{
		label l = ei->first;
		DEBUG ("\nedge %d->%d->", pnid, l);
		set<pt_node_index> dests = ei->second;
		set<pt_node_index>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
		{
			pt_node_index dest = *di;
			if (!pt_fi_node::is_node_valid_at_point (dest, valid_nodes))
			{
				DEBUG ("\ninvalid dest, edge %d->%d->%d", pnid, l, dest);
				continue;
			}
			// Push access paths of dest to its successors only if the
			// access paths of dest change.
			if (append_k_access_paths (pnid, l, dest, node_aps))
				get_k_access_paths (dest, valid_nodes, node_aps);
		}
	}
}

bool points_to_analysis_fi::
append_k_access_paths (pt_node_index src_id,
	label field,
	pt_node_index dest_id,
	map<pt_node_index, set<list<label> > > & node_aps)
{
	DEBUG ("\nappend_k_aps (src=%d, field=%d, dest=%d)", src_id, field, dest_id);
	bool has_changed = false;

	set<list<label> > src_aps = node_aps[src_id];
	set<list<label> >::iterator api;
	for (api = src_aps.begin (); api != src_aps.end (); api++)
	{
		list<label> ap = *api;
#if DEBUG_CONTAINER
		DEBUG ("\nsrc(%d)_ap=", src_id);
                g_ap.print_access_path (ap);
#endif

#if SUMM_K_CONSISTENT
		// If FIELD is WILD_CARD_ID, then find all possible types of ap.
		// Substitute FIELD with the fields of each of these types.
		// Note that each WILD_CARD_ID is substituted this way.
		// append_ap_field() will allow K number of pointers and
		// types of ap will allow a finite sequence of fields
		// statically possible.
		set<label> subfields;
		if (field == wild_card_id)
		{
			set<tree> ap_trees;	
			program.get_ap_trees (ap, ap_trees);
			set<tree>::iterator ti;
			DEBUG ("\nsubfields of");
			for (ti = ap_trees.begin (); ti != ap_trees.end (); ti++)
			{
				program.get_subfield_offsets (*ti, subfields);
				DEBUG ("\n");
				// print_node_brief (dump_file, 0, *ti, 0);
			}
		}
		else
			subfields.insert (field);
			
		set<label>::iterator sfi;
		for (sfi = subfields.begin (); sfi != subfields.end (); sfi++)
			has_changed |= append_ap_field (ap, *sfi, dest_id, node_aps);
	
#else
		has_changed |= append_ap_field (ap, field, dest_id, node_aps);
#endif
	}
	return has_changed;
}

/**
 * This function returns true if AP.FIELD is not present in NODE_APS; in which
 * case it adds AP.FIELD. Else it returns false.
 */

bool points_to_analysis_fi::
append_ap_field (list<label> ap,
	label field,
	pt_node_index dest_id,
	map<pt_node_index, set<list<label> > > & node_aps)
{
	ap_fi_graph::append_ap_field (ap, field);

	if (*(--ap.end ()) == wild_card_id)
		return false;

	if (node_aps[dest_id].find (ap) != node_aps[dest_id].end ())
		return false;

	if (!is_ap_valid_alias (ap))
		return false;

	#if DEBUG_CONTAINER
	DEBUG ("\ndest=%d, ap=", dest_id);
	g_ap.print_access_path (ap);
	#endif

	node_aps[dest_id].insert (ap);
	return true;
}

/**
 * This function finds ap alias set on pt_nodes by traversing gPT and computing
 * APs upto MAX_LEN_PRINT. This function does not use gAP information saved on
 * gPT nodes. This helps in finding aliases with length MAX_LEN_PRINT > K 
 * where K is the limit of gAP paths.
 *
 */

void points_to_analysis_fi::
get_ap_alias_set (set<pt_node_index> & pt_nodes,
	set<list<label> > & useful_paths,
	map<list<label>, set<list<label> > > & ap_alias_set)
{
#if DEBUG_CONTAINER
	set<pt_node_index>::iterator ni;
	DEBUG ("\nget_ap_alias_set(), pt_nodes=");
	for (ni = pt_nodes.begin (); ni != pt_nodes.end (); ni++)
		DEBUG ("%d,", *ni);
#endif

	map<pt_node_index, set<list<label> > > node_aps;
	bool is_k = true;
	get_access_paths (pt_nodes, node_aps, is_k);

#if DEBUG_CONTAINER
	map<pt_node_index, set<list<label> > >::iterator mi;
	for (mi = node_aps.begin (); mi != node_aps.end (); mi++)
	{
		DEBUG ("\n%d=", mi->first);
		set<list<label> > s = mi->second;
		set<list<label> >::iterator si;
		for (si = s.begin (); si != s.end (); si++)
		{
			DEBUG ("(");
			list<label> ap = *si;
			g_ap.print_access_path (ap);		
			DEBUG (")");
		}
	}
#endif

	map<pt_node_index, set<list<label> > >::iterator pi;
	for (pi = node_aps.begin (); pi != node_aps.end (); pi++)
	{
                if (pi->first == undef_id)
                        continue;

                set<list<label> > aps = pi->second;

                // Computing ap_alias_set

                set<list<label> >::iterator api;
                for (api = aps.begin (); api != aps.end (); api++)
                {
                        list<label> ap = *api;
                        merge_set (aps, ap_alias_set[ap]);
                }

#if 0
		// Computing ap_pairs

		if (pi->first == undef_id)
			continue;

		set<list<label> > aps = pi->second;
		set<list<label> >::iterator api1;
		for (api1 = aps.begin (); api1 != aps.end (); api1++)
		{
			list<label> ap1 = *api1;

			set<list<label> >::iterator api2;
			for (api2 = api1; api2 != aps.end (); api2++)
			{
				if (api1 == api2)
					continue;

				list<label> ap2 = *api2;

				get_ap_pair (ap1, ap2, ap_pairs);
			}
		}
#endif
	}
}

bool points_to_analysis_fi::
is_useful_path (list<label> & ap,
	set<list<label> > & useful_paths)
{
	list<label> ap1 = ap;
	// ap1.remove (wild_card_id);
	return useful_paths.find (ap1) != useful_paths.end ();
}

/**
 * This function finds ap alias set on pt_nodes involving ap_nodes.
 *
 * To compute aliases, we cannot not use the APs already saved on gPT nodes
 * without change. This is because the APs saved on gPT nodes are K_PREFIX i.e.
 * xff might actually be representing xfffg. We need to change xff to xff*.
 */

void points_to_analysis_fi::
get_access_path_pairs (set<pt_node_index> & pt_nodes,
	set<ap_node_index> & useful_ap_nodes,
	set<pair<list<label>, list<label> > > & ap_pairs, 
	bool restrict_to_useful)
{
	set<pt_node_index>::iterator ni;
	for (ni = pt_nodes.begin (); ni != pt_nodes.end (); ni++)
	{
		pt_node_index pnid = *ni;
		DEBUG ("\npt=%d", pnid);
		if (pt_access_map.pt_to_access_name.find (pnid) == 
			pt_access_map.pt_to_access_name.end ())
		{
			RESULT ("\nError: Cannot find access_name of ptnid=%d in get_access_paths", pnid);
			return;
		}

		set<ap_node_index> ap_nids = pt_access_map.pt_to_access_name[pnid].get_ap_nodes ();
		set<ap_node_index>::iterator api1;
		for (api1 = ap_nids.begin (); api1 != ap_nids.end (); api1++)
		{
			ap_node_index apnid1 = *api1;
			DEBUG ("\nap1=%d", apnid1);

			list<label> ap1;
			g_ap.get_access_paths (apnid1, ap1);
			#if DEBUG_CONTAINER
			g_ap.print_access_path (ap1);
			#endif

			unsigned int max_len = 0;
			if (SUMM_K_FILTER) 		max_len = SUMM_K_FILTER;
			else if (SUMM_K_PREFIX)		max_len = SUMM_K_PREFIX;
			else if (SUMM_K_CONSISTENT)	max_len = SUMM_K_CONSISTENT;
			else				RESULT ("\nError: K is not set");

			if (ap1.size () == max_len)
				ap1.push_back (wild_card_id);

			set<ap_node_index>::iterator api2;
			for (api2 = api1; api2 != ap_nids.end (); api2++)
			{
				if (api1 == api2)
					continue;

				ap_node_index apnid2 = *api2;
				DEBUG ("\nap2=%d", apnid2);
				list<label> ap2;
				g_ap.get_access_paths (apnid2, ap2);
				#if DEBUG_CONTAINER
				g_ap.print_access_path (ap2);
				#endif

				if (restrict_to_useful &&
					useful_ap_nodes.find (apnid1) == useful_ap_nodes.end () &&
					useful_ap_nodes.find (apnid2) == useful_ap_nodes.end ())
				{
					#if DEBUG_CONTAINER
					DEBUG ("\nSkip, ap1=%d, ap2=%d\n\t", apnid1, apnid2);	
					list<label> ap1;
					g_ap.get_access_paths (apnid1, ap1);
					g_ap.print_access_path (ap1);
					list<label> ap2;
					g_ap.get_access_paths (apnid2, ap2);
					g_ap.print_access_path (ap2);
					#endif
					continue;
				}

				if (ap2.size () == max_len)
					ap2.push_back (wild_card_id);

				get_ap_pair (ap1, ap2, ap_pairs);
			}
		}
	}
}

void points_to_analysis_fi::
get_ap_pair (list<label> & ap1, list<label> & ap2, 
	set<pair<list<label>, list<label> > > & ap_pairs)
{

/*
	// I think the following should not be applied.  Two APs with same
	// frontier fields could be node aliases -- these should not be
	// ignored.
#if SUMM_K_PREFIX == 0 || SUMM_K_CONSISTENT == 0
	// The last field edge may be a wild card in case of SUMM_K_PREFIX.
	// Therefore, the following does not hold for SUMM_K_PREFIX.

	// If ap1 and ap2 have same addresses due to field edges of structure,
	// then do not consider them as aliases. They are aliased by points-to
	// edges only if at least one of
	// them has ASTERISK as the last label.
	label l1 = *(ap1.rbegin ());
	label l2 = *(ap2.rbegin ());
	DEBUG ("\nl1=%d, l2=%d", l1, l2);
	if (l1 != ASTERISK && l2 != ASTERISK)
	{
		if (ap1.size () == 1)
			continue;
		if (ap2.size () == 1)
			continue;
		if (l1 != l2)
		{
			// This is not an error for SUMM_K_PREFIX
			RESULT ("\nError: Link alias should have same frontier fields");
			RESULT ("\n\t!!(");
			g_ap.print_access_path (ap1);
			RESULT (",");
			g_ap.print_access_path (ap2);
			RESULT (")");
		}
		return;
	}
#endif
*/

#if SUMMARIZE_ALIASED_PATHS
#else
	if (*(--ap1.end ()) == wild_card_id)
		return;
	if (*(--ap2.end ()) == wild_card_id)
		return;
#endif

      if (ap1 < ap2)
      	ap_pairs.insert (make_pair (ap1, ap2));
      else
      	ap_pairs.insert (make_pair (ap2, ap1));
}

void points_to_analysis_fi::
print_access_paths (map<pt_node_index, set<list<label> > > & node_aps)
{
	map<pt_node_index, set<list<label> > >::iterator napi;
	for (napi = node_aps.begin (); napi != node_aps.end (); napi++)
	{
		set<list<label> > aps = napi->second;
		if (aps.size () <=1)
			continue;
		RESULT ("\n\t\t{");
		set<list<label> >::iterator apsi;
		for (apsi = aps.begin (); apsi != aps.end (); apsi++)
		{
			list<label> ap = *apsi;
			g_ap.print_access_path (ap);
			RESULT (",");
		}
		RESULT ("}");
	}
}

void points_to_analysis_fi::
print_ap_alias_set  (map<list<label>, list<list<label> > > & ap_alias_set)
{
        map<list<label>, list<list<label> > >::iterator psi;
        for (psi = ap_alias_set.begin (); psi != ap_alias_set.end (); psi++)
        {
                list<label> ap = psi->first;
                RESULT ("\n\t\t");
		g_ap.print_access_path (ap);
                RESULT (" -> ");

                list<list<label> > apss = psi->second;
                list<list<label> >::iterator apsi;
                for (apsi = apss.begin (); apsi != apss.end (); apsi++)
                {
                        list<label> aps = *apsi;
			g_ap.print_access_path (aps);
                        RESULT (",");
                }
        }
}

void points_to_analysis_fi::
print_ap_alias_set  (map<list<label>, set<list<label> > > & ap_alias_set)
{
        map<list<label>, set<list<label> > >::iterator psi;
        for (psi = ap_alias_set.begin (); psi != ap_alias_set.end (); psi++)
        {
                list<label> ap = psi->first;
                RESULT ("\n\t\t");
		g_ap.print_access_path (ap);
                RESULT (" -> ");

                set<list<label> > apss = psi->second;
                set<list<label> >::iterator apsi;
                for (apsi = apss.begin (); apsi != apss.end (); apsi++)
                {
                        list<label> aps = *apsi;
			g_ap.print_access_path (aps);
                        RESULT (",");
                }
        }
}

void points_to_analysis_fi::
print_context_statistics (map<function_index, context_enums<pt_node_set, variables> > & function_contexts)
{
	INFO ("\nACCESS-BASED CONTEXT POINTS-TO PAIRS\n===============\n");

	map<context_index, int> max_call_chain_len = get_call_chain_lengths (100);
	map<context_index, int>::iterator ci;
	for (ci = max_call_chain_len.begin (); ci != max_call_chain_len.end (); ci++)
		DEBUG ("\ncontext=%d, call_chain=%d", ci->first, ci->second);

	map<function_index, unsigned int> program_use_points;
	unsigned int max_num_nodes = 0;
	float max_avg_out_edges = 0;
	set<set<list<int> > > program_aliases;
	map<label, set<label> > summ_stack_to_stack_pointers;

	typename map<function_index, context_enums<pt_node_set, variables> >::iterator fi;
	for (fi = function_contexts.begin (); fi != function_contexts.end (); fi++)
	{
		struct cgraph_node * function = program.get_cgraph_node (fi->first);
		const char * function_name = cgraph_node_name (function);
		struct function * function_decl = DECL_STRUCT_FUNCTION (function->decl);
		context_enums<pt_node_set, variables> contexts = fi->second;

		int count_imp_contexts = 0;
		int count_contexts = contexts.size ();
		bool count_empty_pta = 0;
		bool count_non_empty_pta = 0;

		int count_reuses = 0;
		int max_reuses = 0;

		int max_fn_call_chain = 0;

		unsigned int function_use_points = 0;
		typename context_enums<pt_node_set, variables>::iterator ci;
		for (ci = contexts.begin (); ci != contexts.end (); ci++)
		{
			context<pt_node_set, variables> * current_context = ci->second;
			context_index cid = ci->first;
			pt_node_set * g;
			basic_block block = current_context->get_start_block ();
//			RESULT ("\nFunction %s, context %d, IN(%d)", 
//				function_name, current_context->get_context_id (), block->index);

			int curr_reuses = current_context->get_source_contexts ().size ();
			count_reuses += curr_reuses;
			if (max_reuses < curr_reuses)
				max_reuses = curr_reuses;

			int curr_call_chain = max_call_chain_len[cid];
			if (max_fn_call_chain < curr_call_chain)
				max_fn_call_chain = curr_call_chain;

			unsigned int block_id = block->index;
			set<pt_node_index> in_block_pointers;
			map<label, set<label> > in_block_points_to_pairs;
			map<label, set<label> > in_block_root_aliases;
			set<set<list<int> > > in_block_aliases;
			map<label, set<label> > in_block_reachable_roots;

			// In value
			g = current_context->get_in_value (block);
			if (!g)
			{
				RESULT ("\nError: in value of block=%d is NULL", block->index);
				continue;
			}
			g->get_graph_statistics (max_num_nodes, max_avg_out_edges,
				in_block_pointers,
				in_block_root_aliases,
				in_block_aliases,
				in_block_reachable_roots,
				false);

			g_pt.get_points_to_pairs (in_block_pointers, in_block_points_to_pairs, summ_stack_to_stack_pointers);
//			g_pt.print_points_to_pairs (in_block_points_to_pairs, true);

			if (!in_block_points_to_pairs.size ())
			{
				count_empty_pta++;
				//RESULT ("\nempty, count=%d\n", count_empty_pta);
			}
	
			if (in_block_points_to_pairs.size ())
				count_non_empty_pta++;
		}

		if (count_empty_pta) count_imp_contexts++;
		if (count_non_empty_pta) count_imp_contexts++;

		RESULT ("\nFunction %s, imp_contexts=%d, contexts=%d", 
			function_name, count_imp_contexts, count_contexts);
		RESULT (", total_func_calls = %d, avg_reuses=%d, max_reuses=%d",
			count_reuses, count_reuses / count_contexts, max_reuses);
		RESULT (", max_call_chain_len=%d",
			max_fn_call_chain); 

	}

	INFO ("\n");
}

void points_to_analysis_fi::
get_non_temp_ap_alias_set (map<list<label>, list<list<label> > > & ap_alias_set,
        map<list<label>, list<list<label> > > & ap_alias_set_non_temp)
{
        map<list<label>, list<list<label> > >::iterator pi;
        for (pi = ap_alias_set.begin (); pi != ap_alias_set.end (); pi++)
        {
                list<label> ap = pi->first;
                label v = *(ap.begin ());
                csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, v);
                if (DECL_ARTIFICIAL (v_info->decl))
                        continue;

                list<list<label> > aps = pi->second;
                list<list<label> >::iterator apsi;
                for (apsi = aps.begin (); apsi != aps.end (); apsi++)
                {
                        list<label> sp = *apsi;
                        label sv = *(sp.begin ());
                        csvarinfo_t sv_info = VEC_index (csvarinfo_t, program.variable_data, sv);
                        if (DECL_ARTIFICIAL (sv_info->decl))
                                continue;
                        ap_alias_set_non_temp[ap].push_back (sp);
                }
        }
}

void points_to_analysis_fi::
get_non_temp_ap_alias_set (map<list<label>, set<list<label> > > & ap_alias_set,
        map<list<label>, set<list<label> > > & ap_alias_set_non_temp)
{
        map<list<label>, set<list<label> > >::iterator pi;
        for (pi = ap_alias_set.begin (); pi != ap_alias_set.end (); pi++)
        {
		list<label> ap = pi->first;
                label v = *(ap.begin ());
                csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, v);
                if (DECL_ARTIFICIAL (v_info->decl))
			continue;

		set<list<label> > aps = pi->second;
		set<list<label> >::iterator apsi;
		for (apsi = aps.begin (); apsi != aps.end (); apsi++)
		{
			list<label> sp = *apsi;
                	label sv = *(sp.begin ());
                	csvarinfo_t sv_info = VEC_index (csvarinfo_t, program.variable_data, sv);
                	if (DECL_ARTIFICIAL (sv_info->decl))
				continue;
			ap_alias_set_non_temp[ap].insert (sp);
		}
        }
}
		
void points_to_analysis_fi::
print_fi_value ()
{
	FILE * file = NULL;
//	FILE * file = fopen (DOT_FILE, "w"); 
//	fprintf (file, "\n"); 
//	fclose (file); 
//	file = fopen (DOT_FILE, "a"); 
	RESULT ("\ng_pt=");
	g_pt.print_graph (file);
	RESULT ("\ng_ap=");
	g_ap.print_graph (file);
//	fclose (file); 
	
	pt_access_map.print_map (NULL, &g_ap);
}

void points_to_analysis_fi::
print_analysis_statistics (map<function_index, context_enums<pt_node_set, variables> > & function_contexts)
{
	INFO ("\nACCESS-BASED POINTS-TO PAIRS\n===============\n");

#if INTERMEDIATE_RESULT
	g_pt.print_graph (NULL);
	g_ap.print_graph (NULL);
	pt_access_map.print_map (NULL, &g_ap);
	RESULT ("\n");
#endif

	map<function_index, unsigned int> program_use_points;
	unsigned int max_num_nodes = 0;
	float max_avg_out_edges = 0;
	set<set<list<int> > > program_aliases;
	map<list<label>, set<list<label> > > unique_ap_alias_set;
	map<list<label>, set<list<label> > > unique_ap_alias_set_non_temp;

	unsigned int count_ap_alias_set = 0;
	unsigned int count_ap_alias_set_non_temp = 0;
	unsigned int count_useful_ap_alias_set = 0;
	unsigned int count_useful_ap_alias_set_non_temp = 0;
	unsigned int program_blocks = 0;
	unsigned int useful_program_blocks = 0;
	unsigned int count = 0;
	set<label> heap_to_stack_pointees;
	unsigned int heap_to_stack_pointers = 0;
	unsigned int tot_program_points_to_pairs = 0;
	map<label, set<label> > program_points_to_pairs;
	map<label, set<label> > summ_stack_to_stack_pointers;
	unsigned int count_valid_nodes = 0;
	unsigned int contexts_count = 0;
	unsigned int function_count = 0;
	unsigned int max_contexts_per_function = 0;
	unsigned int count_valid_edges = 0;
	unsigned int tot_stack_clones = 0;
	unsigned int tot_heap_clones = 0;
	unsigned int max_stack_clones = 0;
	unsigned int max_heap_clones = 0;
	unsigned int tot_reapeating_stack_vars = 0;
	unsigned int tot_reapeating_heap_vars = 0;
	unsigned int tot_ap = 0;
	unsigned int tot_ce = 0;
	unsigned int tot_ap_len = 0;
	unsigned int tot_access_names_with_cyclic_edges = 0;
	unsigned int tot_access_names_with_no_cyclic_edge = 0;
	unsigned int pcount = 0;
	unsigned int num_tot_ap = 0;
	unsigned int num_useful_ap = 0;

	set<ap_node_index> empty_nodes;
	set<list<label> > empty_paths;

	// We use FUNCTION_CONTEXTS_MAP instead of PROGRAM_CONTEXTS of
	// inter_procedural_analysis.hh so that the statistics are printed in
	// order of functions. This makes it easier to compare to files of
	// statistics.
	typename map<function_index, context_enums<pt_node_set, variables> >::iterator fi;
	for (fi = function_contexts.begin (); fi != function_contexts.end (); fi++)
	{
		struct cgraph_node * function = program.get_cgraph_node (fi->first);
		const char * function_name = cgraph_node_name (function);
		RESULT ("\nFunction %s", function_name);
		struct function * function_decl = DECL_STRUCT_FUNCTION (function->decl);

		context_enums<pt_node_set, variables> contexts = fi->second;
		contexts_count += contexts.size ();
		function_count++;
		if (max_contexts_per_function < contexts.size ())
			max_contexts_per_function = contexts.size ();

		unsigned int function_use_points = 0;
		basic_block block;
		FOR_EACH_BB_FN (block, function_decl)
		{
			DEBUG ("\nblock=%d", block->index);
			program_blocks++;

			unsigned int block_id = block->index;
			set<pt_node_index> in_block_pointers;
			set<pt_node_index> out_block_pointers;
			map<label, set<label> > in_block_points_to_pairs;
			map<label, set<label> > out_block_points_to_pairs;
			map<label, set<label> > in_block_root_aliases;
			map<label, set<label> > out_block_root_aliases;
			set<set<list<int> > > in_block_aliases;
			set<set<list<int> > > out_block_aliases;
			map<label, set<label> > in_block_reachable_roots;
			map<label, set<label> > out_block_reachable_roots;
			map<pt_node_index, set<list<label> > > in_aliases;
			map<pt_node_index, set<list<label> > > out_aliases;
			map<list<label>, set<list<label> > > in_ap_alias_set;
			map<list<label>, set<list<label> > > out_ap_alias_set;
			map<list<label>, set<list<label> > > in_ap_alias_set_non_temp;
			map<list<label>, set<list<label> > > out_ap_alias_set_non_temp;
			map<list<label>, list<list<label> > > repeating_useful_ap_alias_set;
			map<list<label>, list<list<label> > > repeating_useful_ap_alias_set_non_temp;
			set<set<pt_node_index> > in_values;
			set<pt_node_index> unique_in_values;
			set<pt_node_index> unique_out_values;

			// Compute meet of all the contexts for this basic block

			typename context_enums<pt_node_set, variables>::iterator ci;
			for (ci = contexts.begin (); ci != contexts.end (); ci++)
			{
				context<pt_node_set, variables> * current_context =
					ci->second;
				DEBUG ("\ncontext=%d", current_context->get_context_id ());

				pt_node_set * g;

				///////////////////////////////////////////////////////////////////////////

				// In value
				g = current_context->get_in_value (block);
				if (!g)
				{
					RESULT ("\nError: in value of block=%d is NULL", block->index);
					continue;
				}
				g->get_graph_statistics (max_num_nodes, max_avg_out_edges,
					in_block_pointers,
					in_block_root_aliases,
					in_block_aliases,
					in_block_reachable_roots,
					false);
				// get_access_paths (*g, in_aliases);
				// get_ap_alias_set (g->pt_nodes, empty_nodes, in_ap_alias_set, false);
#if ALIAS_STATISTICS_CONTAINER
				get_ap_alias_set (g->pt_nodes, empty_paths, in_ap_alias_set_non_temp);
#endif
	
				///////////////////////////////////////////////////////////////////////////

				#if DEBUG_CONTAINER
				DEBUG ("\ngraph=IN(%d)", block->index);
				print_value (*g);
				#endif
				// unsigned int c = get_max_acyclic_ap_len (g->pt_nodes);
				// if (count < c)
				//	count = c;

				///////////////////////////////////////////////////////////////////////////

				// Collecting IN values of all contexts at this program point
				in_values.insert (g->pt_nodes);
				// unique_in_values.insert (g->pt_nodes.begin (), g->pt_nodes.end ());
				merge_set (g->pt_nodes, unique_in_values);

				///////////////////////////////////////////////////////////////////////////

				// Out value
				g = current_context->get_out_value (block);
				if (!g)
				{
					RESULT ("\nError: out value of block=%d is NULL", block->index);
					continue;
				}
				g->get_graph_statistics (max_num_nodes, max_avg_out_edges, 
					out_block_pointers, 
					out_block_root_aliases, 
					out_block_aliases,
					out_block_reachable_roots,
					false);
				// get_access_paths (*g, out_aliases);
				// get_ap_alias_set (g->pt_nodes, empty_nodes, out_ap_alias_set, false);
#if ALIAS_STATISTICS_CONTAINER
				get_ap_alias_set (g->pt_nodes, empty_paths, out_ap_alias_set_non_temp);
#endif

				///////////////////////////////////////////////////////////////////////////

				#if DEBUG_CONTAINER
				DEBUG ("\ngraph=OUT(%d)", block->index);
				print_value (*g);
				#endif
				// c = get_max_acyclic_ap_len (g->pt_nodes);
				// if (count < c)
				//	count = c;

				///////////////////////////////////////////////////////////////////////////

				// unique_out_values.insert (g->pt_nodes.begin (), g->pt_nodes.end ());
				merge_set (g->pt_nodes, unique_out_values);
			}

			pt_node_set g;
			// if (program.print_source_location (block))
			//      g_pt.print_sibgraph (NULL, in_block_pointers, true);

			////////////////////////////////////////////////////////////////////////////

			RESULT ("\n    in-bb=%d", block_id);
#if POINTS_TO
			// function_use_points += print_block_points_to_pairs (block, contexts, true, true);
			g_pt.get_points_to_pairs (in_block_pointers, in_block_points_to_pairs, summ_stack_to_stack_pointers);
			unsigned int c = g_pt.print_points_to_pairs (in_block_points_to_pairs, false, heap_to_stack_pointees);
			heap_to_stack_pointers += c;
#endif

			// pcount = count_map_size (in_ap_alias_set);
			// print_access_paths (in_aliases);
			// RESULT ("\n\tIN All=%d", pcount);
			// print_ap_alias_set (in_ap_alias_set);
			// g.print_root_aliases (in_block_root_aliases);
			// g.print_aliases (in_block_aliases);
			// g.print_reachable_roots (in_block_reachable_roots);
			// count_ap_alias_set += pcount;

#if DATA_SIZE_STATISTICS
			count_valid_nodes += unique_in_values.size ();
			count_valid_edges += g_pt.count_graph_edges (unique_in_values);
			g_pt.count_clones (tot_stack_clones, 
				tot_heap_clones, 
				max_stack_clones, 
				max_heap_clones, 
				tot_reapeating_stack_vars,
				tot_reapeating_heap_vars,
				unique_in_values,
				false);
/*
			unsigned int tot_access_names_with_cyclic_edges_this = 0;
			unsigned int tot_access_names_with_no_cyclic_edge_this = 0;
			unsigned int dont_care_1 = 0, dont_care_2 = 0;
			pt_access_map.get_statistics (g_ap, 
				dont_care_1,
				dont_care_2,
				tot_access_names_with_cyclic_edges_this,
				tot_access_names_with_no_cyclic_edge_this,
				tot_ap,
				tot_ce,
				tot_ap_len,
				unique_in_values);
			tot_access_names_with_cyclic_edges += tot_access_names_with_cyclic_edges_this;
			tot_access_names_with_no_cyclic_edge += tot_access_names_with_no_cyclic_edge_this;
*/
#endif

			////////////////////////////////////////////////////////////////////////////

			// NON_TEMP ALL program points
			// get_non_temp_ap_alias_set (in_ap_alias_set, in_ap_alias_set_non_temp);
			pcount = 0;
			count_map_size (in_ap_alias_set_non_temp, pcount, num_tot_ap);
			count_ap_alias_set_non_temp += pcount;
			RESULT ("\n\tIN Non-temp=%d", pcount);
			print_ap_alias_set (in_ap_alias_set_non_temp);

			////////////////////////////////////////////////////////////////////////////

			// USEFUL
			// Print unique ap alias set for a statement over
			// all the contexts at this program point.
			get_useful_ap_alias_set (in_ap_alias_set_non_temp, block, 
				repeating_useful_ap_alias_set_non_temp);
			pcount = 0;
			count_map_size (repeating_useful_ap_alias_set_non_temp, pcount, num_useful_ap);
			count_useful_ap_alias_set_non_temp += pcount;
			RESULT ("\n\tUseful non-temp=%d, useful_program_blocks=%d", pcount, useful_program_blocks);
			print_ap_alias_set (repeating_useful_ap_alias_set_non_temp);
			if (pcount)
				useful_program_blocks++;

			////////////////////////////////////////////////////////////////////////////

			// NON_TEMP USEFUL program points
			// get_non_temp_ap_alias_set (repeating_useful_ap_alias_set, 
			//	repeating_useful_ap_alias_set_non_temp);
			// pcount = count_map_size (repeating_useful_ap_alias_set_non_temp);
			// RESULT ("\n\tuseful non-temp=%d", pcount);
			// print_ap_alias_set (repeating_useful_ap_alias_set_non_temp);
			// count_useful_ap_alias_set_non_temp += pcount;

			////////////////////////////////////////////////////////////////////////////

			RESULT ("\n    out-bb=%d", block_id);
#if POINTS_TO
			g_pt.get_points_to_pairs (out_block_pointers, out_block_points_to_pairs, summ_stack_to_stack_pointers);
			c = g_pt.print_points_to_pairs (out_block_points_to_pairs, false, heap_to_stack_pointees);
			heap_to_stack_pointers += c;
#endif

			// print_access_paths (out_aliases);
			// pcount = count_map_size (out_ap_alias_set);
			// RESULT ("\n\tOUT All=%d", pcount);
			// print_ap_alias_set (out_ap_alias_set);
			// g.print_root_aliases (out_block_root_aliases);
			// g.print_aliases (out_block_aliases);
			// g.print_reachable_roots (out_block_reachable_roots);
			// count_ap_alias_set += pcount;

#if DATA_SIZE_STATISTICS
			count_valid_nodes += unique_out_values.size ();
			count_valid_edges += g_pt.count_graph_edges (unique_out_values);
			g_pt.count_clones (tot_stack_clones, 
				tot_heap_clones, 
				max_stack_clones, 
				max_heap_clones, 
				tot_reapeating_stack_vars,
				tot_reapeating_heap_vars,
				unique_out_values,
				false);

/*
			tot_access_names_with_cyclic_edges_this = 0;
			tot_access_names_with_no_cyclic_edge_this = 0;
			dont_care_1 = 0; dont_care_2 = 0;
			pt_access_map.get_statistics (g_ap, 
				dont_care_1,
				dont_care_2,
				tot_access_names_with_cyclic_edges_this,
				tot_access_names_with_no_cyclic_edge_this,
				tot_ap,
				tot_ce,
				tot_ap_len,
				unique_out_values);
			tot_access_names_with_cyclic_edges += tot_access_names_with_cyclic_edges_this;
			tot_access_names_with_no_cyclic_edge += tot_access_names_with_no_cyclic_edge_this;
*/
#endif

			////////////////////////////////////////////////////////////////////////////

			// NON_TEMP ALL program points
			// get_non_temp_ap_alias_set (out_ap_alias_set, out_ap_alias_set_non_temp);
			pcount = 0;
			count_map_size (out_ap_alias_set_non_temp, pcount, num_tot_ap);
			count_ap_alias_set_non_temp += pcount;
			RESULT ("\n\tOUT Non-temp=%d", pcount);
			print_ap_alias_set (out_ap_alias_set_non_temp);

			////////////////////////////////////////////////////////////////////////////

			merge_map (in_ap_alias_set_non_temp, unique_ap_alias_set_non_temp);
			merge_map (out_ap_alias_set_non_temp, unique_ap_alias_set_non_temp);

#if POINTS_TO
			// Copy all edges from in/out_block_points_to_pairs to
			// program_points_to_pairs
	                map<label, set<label> >::iterator pi;
	                for (pi = in_block_points_to_pairs.begin ();
	                        pi != in_block_points_to_pairs.end ();
	                        pi++)
	                {
	                        label src = pi->first;
	                        set<label> dests = pi->second;
	                        // program_points_to_pairs[src].insert (dests.begin (), dests.end ());
				merge_set (dests, program_points_to_pairs[src]);
	                        dests.erase (undef_id);
	                        tot_program_points_to_pairs += dests.size ();
	                }
	                for (pi = out_block_points_to_pairs.begin ();
	                        pi != out_block_points_to_pairs.end ();
	                        pi++)
	                {
	                        label src = pi->first;
	                        set<label> dests = pi->second;
	                        // program_points_to_pairs[src].insert (dests.begin (), dests.end ());
				merge_set (dests, program_points_to_pairs[src]);
	                        dests.erase (undef_id);
	                        tot_program_points_to_pairs += dests.size ();
	                }
#endif
		}

		// DEBUG ("\nfunction=%s use-points=%d", function_name, function_use_points);
		// program_use_points[function->uid] = function_use_points;
	}

	RESULT ("\n--------\n");
        unsigned int unique_program_points_to_pairs = 0;
#if POINTS_TO
        map<label, set<label> >::iterator pi;
        for (pi = program_points_to_pairs.begin ();
                pi != program_points_to_pairs.end ();
                pi++)
        {
                set<label> dests = pi->second;
                dests.erase (undef_id);
                unique_program_points_to_pairs += dests.size ();
        }

        RESULT ("\nTotal program points-to pairs: unique=%d, tot=%d",
                unique_program_points_to_pairs, tot_program_points_to_pairs);
#if SUMM_K_CONSISTENT
        RESULT ("\nTotal stack-pointers with heap_to_stack program pointers=%d",
                heap_to_stack_pointers);
#endif

	g_pt.print_points_to_pairs (program_points_to_pairs, false, heap_to_stack_pointees);
        RESULT ("\nTotal heap_to_stack pointees=%d", heap_to_stack_pointees.size ());

#if SUMM_K_CONSISTENT
	RESULT ("\nProgram summ_stack_to_stack_points-to pairs=");
	set<label> empty;
	g_pt.print_points_to_pairs (summ_stack_to_stack_pointers, false, empty);
#endif
#endif


#if 0
	unsigned int use_points = 0;
	map<function_index, unsigned int>::iterator ui;
	for (ui = program_use_points.begin (); ui != program_use_points.end (); ui++)
		use_points += ui->second;
	RESULT ("\nTotal use points = %d", use_points);

	RESULT ("\nGraph with maximum |N+E| has num_nodes=%d, avg_out_edges=%.2f",
		max_num_nodes, max_avg_out_edges);
	pt_node_set g;
	g.print_aliases (program_aliases);
#endif

//      print_original_gcc_points_to_pairs ();

	// pcount = count_map_size (unique_ap_alias_set);
	// RESULT ("\nUnique program ap alias set=%d", pcount);
	// print_ap_alias_set (unique_ap_alias_set);

	// get_non_temp_ap_alias_set (unique_ap_alias_set, unique_ap_alias_set_non_temp);
	unsigned int pcount_non_temp = 0, num_unique_ap = 0;
	count_map_size (unique_ap_alias_set_non_temp, pcount_non_temp, num_unique_ap);
	RESULT ("\nUnique (non-temp) program ap alias set=%d", pcount_non_temp);
	print_ap_alias_set (unique_ap_alias_set_non_temp);

	float avg_stack_clones = (float) tot_stack_clones / tot_reapeating_stack_vars;	
	float avg_heap_clones = (float) tot_heap_clones / tot_reapeating_heap_vars;	

	INFO ("\n");
	RESULT ("\nTotal program blocks=%d", program_blocks);
        RESULT ("\nFunction count=%d", function_count);
        RESULT ("\nTotal value contexts=%d", contexts_count);
        RESULT ("\nAvg contexts per function=%f", (float) contexts_count / function_count);
	RESULT ("\nMax contexts per function=%d", max_contexts_per_function);
	RESULT ("\nTotal valid nodes=%d", count_valid_nodes);
	RESULT ("\nTotal valid edges=%d", count_valid_edges);
	RESULT ("\nAvg valid nodes per program point=%f", (float) count_valid_nodes/(program_blocks*2));
	RESULT ("\nAvg valid edges per program point=%f", (float) count_valid_edges/(program_blocks*2));
	RESULT ("\ntot_reapeating_stack_vars=%d", tot_reapeating_stack_vars);
	RESULT ("\ntot_stack_clones=%d", tot_stack_clones);
	RESULT ("\navg_stack_clones per program point=%f", avg_stack_clones);
	RESULT ("\ntot_reapeating_heap_vars=%d", tot_reapeating_heap_vars);
	RESULT ("\ntot_heap_clones=%d", tot_heap_clones);
	RESULT ("\navg_heap_clones per program point=%f", avg_heap_clones);
	RESULT ("\nmax_stack_clones at a program point=%d", max_stack_clones);
	RESULT ("\nmax_heap_clones at a program point=%d", max_heap_clones);
	RESULT ("\nFS, tot_ap=%d", tot_ap);
	RESULT ("\nFS, tot_ce=%d", tot_ce);
	RESULT ("\nFS, tot_ap_len=%d", tot_ap_len);
	RESULT ("\nFS, tot_alias_sets_with_cyclic_ap=%d", tot_access_names_with_cyclic_edges);
	RESULT ("\nFS, tot_alias_sets_with_no_cyclic=%d", tot_access_names_with_no_cyclic_edge);
	RESULT ("\ntot_update_points where stmttouch=%d", tot_update_points);
	RESULT ("\nAvg stmtouch per program point=%f", (float) tot_stmttouch / tot_update_points);
	RESULT ("\nAvg potaffreg per program point=%f", (float) tot_potaffreg / tot_update_points);
	RESULT ("\nAvg finalaffreg per program point=%f", (float) tot_finalaffreg / tot_update_points);
	RESULT ("\nTotal ap alias set=%d", count_ap_alias_set);
	RESULT ("\nTotal ap alias set non-temp=%d", count_ap_alias_set_non_temp);
	RESULT ("\nTotal useful ap alias set=%d", count_useful_ap_alias_set);
	RESULT ("\nTotal useful ap alias set non-temp=%d", count_useful_ap_alias_set_non_temp);
	RESULT ("\nTotal useful program blocks=%d", useful_program_blocks);
	RESULT ("\nnum_unique_ap=%d", num_unique_ap);
	RESULT ("\nnum_tot_ap=%d", num_tot_ap);
	RESULT ("\nnum_useful_ap=%d", num_useful_ap);

	FILE * stat_file = fopen (STAT_FILE, "a");
#if SUMM_TYPE_K
	fprintf (stat_file, "\nACCESS_BASED,SUMM_TYPE_K=%d,L=%d", SUMM_TYPE_K, MAX_LEN_PRINT);
	fprintf (stat_file, "\ngAP_CYCLIC=%d, gAP_CYCLIC_EDGES=%d", gAP_CYCLIC, gAP_CYCLIC_EDGES);
#elif SUMM_POINTED_TO_BY
	fprintf (stat_file, "\nACCESS_BASED,FIELD=%d,REACH=%d,L=%d", 
		SUMM_FIELD_POINTED_TO_BY, SUMM_REACHABLE_BY, MAX_LEN_PRINT);
#elif SUMM_K_PREFIX
	fprintf (stat_file, "\nACCESS_BASED,SUMM_K_PREFIX=%d,L=%d", SUMM_K_PREFIX, MAX_LEN_PRINT);
#else
	fprintf (stat_file, "\nACCESS_BASED,SUMM_TYPE_K=%d,L=%d", SUMM_TYPE_K, MAX_LEN_PRINT);
#endif
	fclose (stat_file);
	g_pt.print_statistics ();
#if ACCESS_PARTIAL_ORDER || PARTIAL_ORDER_STATISTICS
	g_pt.print_partial_order_statistics ();
#endif
	g_ap.print_statistics ();
	pt_access_map.print_statistics (g_ap);
	program.print_statistics ();

//	print_context_statistics (function_contexts);
	
	stat_file = fopen (STAT_FILE, "a");
	fprintf (stat_file, "\nTotal program blocks=%d", program_blocks);
        fprintf (stat_file, "\nFunction count=%d", function_count);
        fprintf (stat_file, "\nTotal value contexts=%d", contexts_count);
        fprintf (stat_file, "\nAvg contexts per function=%f", (float) contexts_count / function_count);
	fprintf (stat_file, "\nMax contexts per function=%d", max_contexts_per_function);
	fprintf (stat_file, "\nTotal valid nodes=%d", count_valid_nodes);
	fprintf (stat_file, "\nTotal valid edges=%d", count_valid_edges);
	fprintf (stat_file, "\nAvg valid nodes per program point=%f", (float) count_valid_nodes/(program_blocks*2));
	fprintf (stat_file, "\nAvg valid edges per program point=%f", (float) count_valid_edges/(program_blocks*2));
	fprintf (stat_file, "\ntot_reapeating_stack_vars=%d", tot_reapeating_stack_vars);
	fprintf (stat_file, "\ntot_stack_clones=%d", tot_stack_clones);
	fprintf (stat_file, "\navg_stack_clones per program point=%f", avg_stack_clones);
	fprintf (stat_file, "\ntot_reapeating_heap_vars=%d", tot_reapeating_heap_vars);
	fprintf (stat_file, "\ntot_heap_clones=%d", tot_heap_clones);
	fprintf (stat_file, "\navg_heap_clones per program point=%f", avg_heap_clones);
	fprintf (stat_file, "\nFS, tot_ap=%d", tot_ap);
	fprintf (stat_file, "\nFS, tot_ce=%d", tot_ce);
	fprintf (stat_file, "\nFS, tot_ap_len=%d", tot_ap_len);
	fprintf (stat_file, "\nFS, tot_alias_sets_with_cyclic_ap=%d", tot_access_names_with_cyclic_edges);
	fprintf (stat_file, "\nFS, tot_alias_sets_with_no_cyclic_ap=%d", tot_access_names_with_no_cyclic_edge);
	fprintf (stat_file, "\ntot_update_points where stmttouch=%d", tot_update_points);
	fprintf (stat_file, "\nAvg stmtouch per program point=%f", (float) tot_stmttouch / tot_update_points);
	fprintf (stat_file, "\nAvg potaffreg per program point=%f", (float) tot_potaffreg / tot_update_points);
	fprintf (stat_file, "\nAvg finalaffreg per program point=%f", (float) tot_finalaffreg / tot_update_points);
	fprintf (stat_file, "\nUnique ap alias set=%d", pcount);
	fprintf (stat_file, "\nUnique ap alias set non-temp=%d", pcount_non_temp);
	fprintf (stat_file, "\nTotal ap alias set=%d", count_ap_alias_set);
	fprintf (stat_file, "\nTotal ap alias set non-temp=%d", count_ap_alias_set_non_temp);
	fprintf (stat_file, "\nTotal useful ap alias set=%d", count_useful_ap_alias_set);
	fprintf (stat_file, "\nTotal useful ap alias set non-temp=%d", count_useful_ap_alias_set_non_temp);
	fprintf (stat_file, "\nTotal useful program blocks=%d", useful_program_blocks);
	fprintf (stat_file, "\nnum_unique_ap=%d", num_unique_ap);
	fprintf (stat_file, "\nnum_tot_ap=%d", num_tot_ap);
	fprintf (stat_file, "\nnum_useful_ap=%d", num_useful_ap);
	fclose (stat_file);
}

/**
 * The client analysis can modify the control flow graph to use our
 * inter-procedural analysis, which assumes that each function call is the only
 * statement in a basic block. Also, each pointer statement is made the only
 * statement of a basic block for bi-directional inter-procedural analysis.
 */

void points_to_analysis_fi::
preprocess_and_parse_program ()
{
#if DEBUG_CONTAINER
	program.print_original_cfg ();
#endif

	// If a pre-analysis has already set main, do not reinitialize.
	if (!program.main_cnode)
	{
		// FIXME: variable_data is reinitialized and the one created by
		// liveness_analysis_simple is not freed.
		program.initialization ();
		program.preprocess_control_flow_graph ();
	}

#if SKIP_EMPTY_CFG
		program.is_cfg_ptr_asgn_empty ();
#endif
	set_blocks_order ();

	RESULT ("\nK=%d/%d/%d/%d, gAP-cyclic=%d", 
		SUMM_TYPE_K, SUMM_K_FILTER, SUMM_K_PREFIX, SUMM_K_CONSISTENT, gAP_CYCLIC);

#if DEBUG_CONTAINER
	program.print_parsed_data ();
	#if HEAP_TYPE_BASED_NAME
	program.print_heap_type_id ();
	#endif
	program.print_variable_data ();
	program.print_assignment_data ();
	program.print_heap_to_alloc_site ();

#endif
}


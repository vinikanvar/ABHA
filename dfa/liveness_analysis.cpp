
/************************
 * @author Vini Kanvar
************************/

#include "liveness_analysis.hh"

// In flow functions, we consider only the latest use-site and discard any
// previous use-site. We do not do this at meet. Used by only <deterministic_graph>.
#define LATEST_USE_SITE_ONLY (0 & LIVENESS_DETERMINISTIC)

#define IGNORE_NON_ASGNS 0

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

/**
 * <deterministic_graph>: This liveness analysis generates only explicitly live
 * paths. At each program point, whenever required, it checks implicitly live
 * paths using the already computed points-to graph at the program point. 
 * <non_deterministic_graph>: This liveness analysis generates explicit and
 * aliases of live paths.
	
 * However, points-to graph at each program point may not contain all variables
 * because some variables are bypassed. There are two fixes to find the
 * implicitly live path at each program point:
 (a) Do not bypass access paths whose frontier is dereferenced with lhs of a
     statement in the callees. (too inefficient) or
 (b) Save the bypassed information with each context, and then at each context,
     accumulate all the bypassed information of all its calling contexts while
     computing MOVP. 
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
liveness_analysis (bool is_val_context):
	backward_inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges> (is_val_context)
{
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
~liveness_analysis ()
{
	delete_context_aux_info ();
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
LIVE_VALUE_TYPE * liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
boundary_value ()
{
	DEBUG ("\nboundary_value ()");
	return new LIVE_VALUE_TYPE;
}

/**     
 * Free all block values of curr_context if no context is reachable from it
 */   


template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
free_context_analysis_values (context<LIVE_VALUE_TYPE, unlabeled_edges> & curr_context)
{
#if GC_ON_THE_FLY
	free_context_values (curr_context);
#endif
}

/* Returns the top data flow value of the lattice. 
 * This is the default data flow value.
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
LIVE_VALUE_TYPE * liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
initial_value ()
{
	return new LIVE_VALUE_TYPE;
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
process_call_statement (context<LIVE_VALUE_TYPE, unlabeled_edges> * src_context, basic_block call_site)
{
	basic_block asgn_call_block = call_site;
	basic_block io_context_block = call_site;
	call_site = NULL;

	unsigned int io_context_block_type = ((block_information *)(io_context_block->aux))->get_block_type ();
	if (io_context_block_type & AUX_BLOCK)
	{
		asgn_call_block = program.get_single_succ_block (io_context_block);
		if (!asgn_call_block)
		{
			RESULT ("\nError: AUX CALL block error 1");
			return;
		}
		unsigned int asgn_call_block_type = ((block_information *)(asgn_call_block->aux))->get_block_type ();
		if (!(asgn_call_block_type & CALL_BLOCK))
		{
			RESULT ("\nError: AUX CALL block error 2");
			return;
		}
	}

	set<struct cgraph_node *> dest_functions = get_called_functions (*src_context, asgn_call_block);
	if (!dest_functions.size ())
	{
		RESULT ("\nError: Did not find called/destination function");
		// Process parsed information to deal with statements
		// formal-params:=actual-params and to make function pointers
		// (used in a function call) as live.
		// process_parsed_data (src_context, call_site, NULL);
		// src_context->set_in_value (io_context_block, initial_value ());
		return;
	}

	bool to_kill = false;
	// Kill if there is only one function call.
	if (dest_functions.size () == 1)
		to_kill = true;

	// iterate over all functions pointed by a function pointer.
	set<struct cgraph_node *>::iterator fi;
	for (fi = dest_functions.begin (); fi != dest_functions.end (); fi++)
	{
		struct cgraph_node * dest_function = *fi;

#if DEBUG_CONTAINER
		const char * dest_function_name =
			IDENTIFIER_POINTER (DECL_NAME (dest_function->decl));
		DEBUG ("\nChecking context of function %s, src_context %d, call_site %d",
			dest_function_name, src_context->get_context_id (), asgn_call_block->index);
#endif

#if SKIP_EMPTY_CFG
		// Note: If the target of function pointer is an empty
		// function, then the function pointer is not made live at IN
		// of the call.
                if (program.is_cfg_ptr_asgn_empty (dest_function))
                {
			// We need to set IN so that the adjacent blocks get added
			copy_out_to_in (src_context, io_context_block);
                        continue;
                }
#endif

		// If destination of dependent context does not exist, then do
		// not proceed.
		if (!is_dest_of_dept_context_exist (src_context, asgn_call_block, dest_function))
		{
			RESULT ("\nError: dept context of called function does not exist");
			// LIVE_VALUE_TYPE * out_value = src_context->get_out_value (io_context_block);
                        // in_value->copy_value (*out_value, false);
			continue;
		}

		// We should not merge flow-sensitive out and aux for the
		// callee because then we will not be able to extract the aux
		// of current context from the analyzed value of callee
		// (because of presence of use-sites).  Therefore, we use the
		// fact that liveness analysis is a separable framework. We
		// analyze the two graphs separately and then merge them. 

		// The call site (CALL_BLOCK) that contains foo() is used to
		// build the context transition for the flow-sensitive out
		// value. An empty block before call site block (marked
		// AUX_BLOCK and CALL_BLOCK) is used to build the context
		// transition for aux. The IN value of call site block flows to
		// AUX_BLOCK; thereby merging the information.

		// In ipa/backward_procedural_analysis, dept_context for both
		// call site block and AUX_BLOCK is found from call site block
		// because dept_context does not exist for AUX_BLOCK.

		if (!(io_context_block_type & AUX_BLOCK))
		{
			LIVE_VALUE_TYPE * out_value = src_context->get_out_value (io_context_block);
			process_call_statement (*out_value, *src_context, 
				asgn_call_block, io_context_block, dest_function, to_kill);
		}
		else
		{
			RESULT ("\naux");
			// Pass aux (unaffected context dept value) to callee. It will
			// also become aux in callee since callees_defs_lhs_derefs in
			// callee are surely there in caller.
			LIVE_VALUE_TYPE * unaffected_context_dept_live = 
				get_unaffected_live_value (*src_context);
			if (!unaffected_context_dept_live)
				return;

			// Do not process call if value is empty
			if (!unaffected_context_dept_live->is_empty ())
				process_call_statement (*unaffected_context_dept_live, *src_context, 
					asgn_call_block, io_context_block, dest_function, to_kill);

			// OUT is value obtained after calling function on
			// flow-sensitive data from CALL_BLOCK & !AUX_BLOCK.
			// Merge it with above produced value at IN.
			LIVE_VALUE_TYPE * out_value = src_context->get_out_value (io_context_block);
			initialize_in_value (src_context, io_context_block);
			LIVE_VALUE_TYPE * in_value = src_context->get_in_value (io_context_block);
               	        in_value->copy_value (*out_value, false);
		}
	}

#if GREEDY_ALIAS_CLOSURE
	// Generate aliases of var (i.e. paths pointing to var). This is
	// defined for <non_deterministic_graph> (KSK07)
	DEBUG ("\ngenerate_alias_closure IN-call");
	generate_alias_closure (src_context, io_context_block);

#else

	LIVE_VALUE_TYPE * in_value = src_context->get_in_value (io_context_block);
	if (in_value)
		in_value->clean ();
#endif
}

/**
 * The par:=arg and rec:=ret assignments and call statement is fetched from
 * asgn_block. The calling context is created for call_block.
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
process_call_statement (LIVE_VALUE_TYPE & out_value,
	context<LIVE_VALUE_TYPE, unlabeled_edges> & src_context,
	basic_block asgn_call_block,
	basic_block io_context_block,
	struct cgraph_node * dest_function,
	bool to_kill)
{
	// Every called function (via function pointer) has different
	// returned variable. Therefore, a different copy of
	// return_value should be passed.

	DEBUG ("\nout_value->copy_value()");
	LIVE_VALUE_TYPE out_value_copy;
	out_value_copy.copy_value (out_value, false);
#if DEBUG_CONTAINER
	DEBUG ("\nout_value_copy of function call (before return-receive mapping)");
	out_value_copy.print_value (NULL);
#endif

	// Map returned value to receiving value.
	// process_return_value() does not kill the previous liveness of
	// the returned variable (rhs) which was computed from the
	// previous called function (via function pointer).
	// FIXME: First delete previous liveness of rhs variable since
	// process_return_value() does not kill edges.

	process_return_value (&src_context, asgn_call_block, &out_value_copy, dest_function, to_kill);

#if INTERMEDIATE_RESULT
	RESULT ("\nout_value + return mapping of function %s",
		cgraph_node_name (dest_function));
	out_value_copy.print_value (NULL);
#endif

	// To build a context, pass callees_global_defs and
	// callees_lhs_derefs rooted paths; bypass the rest. While
	// analyzing the context, pass callees_global_defs
	// flow-sensitively; memoize the rest since we do not perform
	// strong updates on live paths.

	// Only return var among locals of the callee is live before
	// calling the callee; this also needs to be passed both for
	// context creation and context analysis. 

	// Extract def_deref_ret_rooted value from out_value_copy and
	// not in_value_copy. 
	struct cgraph_node * src_function = src_context.get_function ();
	LIVE_VALUE_TYPE * def_deref_ret_rooted_value =
		extract_def_deref_ret_rooted_value (src_context, dest_function, out_value_copy);
	LIVE_VALUE_TYPE * return_value = def_deref_ret_rooted_value;
#if INTERMEDIATE_RESULT
	RESULT ("\nout_value_copy left with def_deref_ret-unreachable nodes");
	out_value_copy.print_value (NULL);
	RESULT ("\nreturn_value function %s", cgraph_node_name (dest_function));
	return_value->print_value (NULL);
#endif

	// Process called context
	LIVE_VALUE_TYPE * function_in_value =
		process_destination_context (src_context, io_context_block, dest_function, return_value);

#if ACCUM_LIVE_CONTEXT_INDEPT
        // Save only this bypassed value in the called context. For
        // accumulation of bypassed values of all previous transitive
        // calls, we perform fixed point computation using
        // ipa::analyze_context_aux_worklist().
        save_context_indept_live (src_context, io_context_block, dest_function, out_value_copy);
        DEBUG ("\nsave_context_indept_live done");
#endif

	if (!function_in_value)
		return;

	// FUNCTION_IN_VALUE belongs to START block of called function.
	// It should not be modified. Work on its copy.
	LIVE_VALUE_TYPE function_in_value_copy;
	function_in_value_copy.copy_value (*function_in_value, false);

	// Map actual parameters to formal parameters
	process_function_arguments (&src_context, asgn_call_block, &function_in_value_copy, dest_function);
#if DEBUG_CONTAINER
	DEBUG ("\nreturn_value + argument_mapping of function %s",
		cgraph_node_name (dest_function));
	function_in_value_copy.print_value (NULL);
#endif

	// Delete local variables in IN_VALUE under the condition that
	// the SRC_CONTEXT has never been called by a context of
	// DEST_FUNCTION.
	// FIXME: Delete all variables whose address does not escape.
	// Delete all locals if SRC_CONTEXT has never been called by a
	// context of DEST_FUNCTION.

	check_and_delete_local_variables (src_context, dest_function, function_in_value_copy, NULL);
#if DEBUG_CONTAINER
	DEBUG ("\ncheck_and_delete_local_variables:");
	function_in_value_copy.print_value (NULL);
#endif

	// Rohan Padhye: OUT = IN_succ U OUT. Take self-meet to ensure monotonic results. 

	// Create a copy of FUNCTION_IN_VALUE to IN of call-site. IN
	// of the call-site contains arg_ret_glob-unreachable nodes. The
	// def_deref_ret_rooted nodes are in FUNCTION_IN_VALUE.
	// Therefore, FUNCTION_IN_VALUE should be appended to the IN
	// of the call-site.
	DEBUG ("\nfunction_in_value->copy_value() to in_value");
	// Initialize IN to non-null when we know that called function is non-null
	initialize_in_value (&src_context, io_context_block);
	LIVE_VALUE_TYPE * in_value = src_context.get_in_value (io_context_block);
	in_value->copy_value (function_in_value_copy, false);

	unsigned int io_context_block_type = ((block_information *)(io_context_block->aux))->get_block_type ();

	// If io_context_block is an AUX_BLOCK, no need to pick aux as that is
	// what we passed.
	// If io_context_block is not an AUX_BLOCK, then pick from aux of dest_context
	// and pass it flow sensitively as it is a flow sensitive information
	if (!(io_context_block_type & AUX_BLOCK))
	{
		copy_unaffected_context_dept_live (src_context, io_context_block, dest_function, *in_value);
	}


	// If io_context_block is an AUX_BLOCK, out_value_copy is part of aux
	// of src_context. Do not save it anywhere (flow-sensitively).
	// If io_context_block is an AUX_BLOCK, out_value_copy is a
	// flow-sensitive value. Save it in IN_VALUE.
	if (!(io_context_block_type & AUX_BLOCK))
	{
		// Copy def_deref_ret_unreachable value to in_value.
		DEBUG ("\nCopying def_deref_ret-unreachable value to in");
		DEBUG ("\nout_value->copy_value() to in_value");
		in_value->copy_value (out_value_copy, false);
	}
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
initialize_in_value (context<LIVE_VALUE_TYPE, unlabeled_edges> * src_context, basic_block io_context_block)
{
	LIVE_VALUE_TYPE * in_value = src_context->get_in_value (io_context_block);
	if (!in_value)
		in_value = initial_value ();
	// We do not change the old IN value; we change a copy of the old IN
	// value. This is because old IN value saved in COPY_OLD_IN_VALUE (in
	// ipa/backward_inter_procedural_analysis.cpp) should not be modified.
	else
	{
		DEBUG ("\nCreating new in_value");
		DEBUG ("\nin_value->copy_value()");
		LIVE_VALUE_TYPE * in_value_copy = in_value->copy_value (false);
		in_value = in_value_copy;
	}
	src_context->set_in_value (io_context_block, in_value);

#if DEBUG_CONTAINER
	DEBUG ("\nValue at in of call-site");
	in_value->print_value (NULL);
#endif
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
bool liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
process_parsed_data (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, 
	basic_block current_block, 
	LIVE_VALUE_TYPE * returning_value, 
	bool to_kill)
{
	DEBUG ("\nprocess_parsed_data");

	list<pair<unsigned int, bool> > parsed_data_indices = 
		((block_information *)(current_block->aux))->get_parsed_data_indices ();

	bool is_in_initialized = false;
	unsigned int block_type = ((block_information *)(current_block->aux))->get_block_type ();

	if (block_type & NORETURN_BLOCK)
	{
		bool is_in_initialized = true;
		current_context->set_in_value (current_block, initial_value ());
		DEBUG ("\nempty IN");
		return is_in_initialized;
	}

	// END block is empty.
	if (block_type & END_BLOCK)
	{
		DEBUG ("\nEND_BLOCK");
		if (first_stmt (current_block))
		{
			 RESULT ("\nError: end block is not empty");
			 return false;
		}
		DEBUG ("\nNo statement found in START_BLOCK");
		bool is_out_initialized = true;

		// copy_out_to_in (current_context, current_block);
		LIVE_VALUE_TYPE * out_value = current_context->get_out_value (current_block);
		LIVE_VALUE_TYPE out_value_copy;

#if BYPASSING_UNAFFECTED
		out_value_copy.copy_value (*out_value, false);
		#if DEBUG_CONTAINER
		RESULT ("\nout_value_copy=");
		out_value_copy.print_value (NULL);
		#endif
		LIVE_VALUE_TYPE * changing_context_dept_live =
			extract_changing_context_dept_live (*current_context, out_value_copy);
		#if DEBUG_CONTAINER
		DEBUG ("\nchanging_context_dept_live=");
		changing_context_dept_live->print_value (NULL);
		DEBUG ("\nout_value_copy (after extraction)=");
		out_value_copy.print_value (NULL);
		#endif
		current_context->set_in_value (current_block, changing_context_dept_live);
#else
		copy_out_to_in (current_context, current_block);
#endif
		// OUT_VALUE_COPY contains the unaffected part 
		copy_unaffected_context_dept_aux (out_value_copy, *current_context, true);
#if INTERMEDIATE_RESULT
		RESULT ("\nunaffected_context_dept=");
		out_value_copy.print_value (NULL);
#endif

		return is_out_initialized;
	}

	// The IN of CALL blocks is initialized in process_call_statement().
	// Initialize other blocks here.
	if (!(block_type & CALL_BLOCK))
		copy_out_to_in (current_context, current_block);

	// We initialize IN of all blocks even if IN is only same as OUT.
	bool is_out_initialized = true;

	LIVE_VALUE_TYPE * value;
	if (block_type & CALL_BLOCK && (value = returning_value));
	else
		value = current_context->get_in_value (current_block);


	// Iterate in backward direction for liveness analysis
	list<pair<unsigned int, bool> >::reverse_iterator it;
	for (it = parsed_data_indices.rbegin (); it != parsed_data_indices.rend (); it++)
	{
		unsigned int index = (*it).first;
		bool is_assignment = (*it).second;

		DEBUG ("\nParsed data: index %d, bool %d, ", index, is_assignment);
		if (is_assignment)
		{
			#if DEBUG_CONTAINER
			program.print_assignment_data (index);
			#endif
			DEBUG ("\nTransferring and generating liveness for assignment statement");
			process_assignment_statement (*value, current_context, current_block, index);
		}
		else
		{
			#if DEBUG_CONTAINER
			program.print_variable_data (index);
			#endif
			DEBUG ("\nMarking variable as live");
#if IGNORE_NON_ASGNS == 0
			process_use_statement (*value, current_context, current_block, index);
#endif
		}
	}

	// Delete list of nodes that are unreachable from any node in IN_VALUE
	value->clean ();

#if CHECK_CONTAINER
	if (value->is_graph_reachability_okay () ||
		value->is_graph_labelling_okay ())
		RESULT ("\nOKAY");
#endif

	if (block_type & CALL_BLOCK)
		return is_in_initialized;

	// Reuse: Delete a graph if it repeats at the successor program point.
	LIVE_VALUE_TYPE * value_in = current_context->get_in_value (current_block);
	LIVE_VALUE_TYPE * value_out = current_context->get_out_value (current_block);
	if (value_out->is_value_same (*value_in))
		current_context->set_in_value (current_block, value_out);
	
#if GREEDY_ALIAS_CLOSURE
	// Generate aliases of var (i.e. paths pointing to var). This is
	// defined for <non_deterministic_graph> (KSK07)
	DEBUG ("\ngenerate_alias_closure IN-block");
	generate_alias_closure (current_context, current_block);
#endif

	return is_in_initialized;
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
bool liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
process_use_statement (LIVE_VALUE_TYPE & value, 
	context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, 
	basic_block current_block, 
	unsigned int variable_index)
{
	DEBUG ("\nprocess_use_statement");

	if (!program.is_proper_var (variable_index))
		return true;

	// Return variable is marked live if received variable is live -- done
	// by process_return_value(). 
	unsigned int block_type = ((block_information *)(current_block->aux))->get_block_type ();
	if (block_type & RETURN_BLOCK)
		return true;
	
	csvarinfo_t variable = VEC_index (csvarinfo_t, program.variable_data, variable_index);
	DEBUG ("\nObtaining in and out values of block %d", current_block->index);
	value.insert_edge (value.stack, variable->id, variable->id * (ROOT_LINK));
	DEBUG ("\nprocess_use_statement done");

	// No need to compute link alias closure here. It will be calculated
	// after all statements of a block are processed in process_parsed_data().

	return true;
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
bool liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
process_assignment_statement (LIVE_VALUE_TYPE & value, 
	context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, 
	basic_block current_block, 
	unsigned int assignment_data_index, 
	bool to_kill)
{
	DEBUG ("\nprocess_assignment_statement");

	constraint_t assignment = VEC_index (constraint_t, program.assignment_data, assignment_data_index);
	constraint_expr lhs = assignment->lhs;
	constraint_expr rhs = assignment->rhs;	
#if DEBUG_CONTAINER
	DEBUG ("\n");
	program.print_assignment_data (assignment_data_index);
#endif

	// In liveness analysis, the access-paths at OUT are either
	// (a) killed by lhs and transferred through rhs to IN, or
	// (b) transferred without change from OUT to IN

#if DEBUG_CONTAINER
	DEBUG ("\nGraph at OUT");
	value.print_value (NULL);
#endif

	// For x.f=&x, the following is true. However, we should not return;
	// Return if LHS equals RHS. This can happen due to pointer arithmetic.
	//if (lhs.var == rhs.var && lhs.offset == rhs.offset)
	//      return;

	// If block has PHI statement, and ASSIGNMENT_DATA_INDEX is not the
	// first PHI constraint, then do not perform killing. PREVIOUS_PHI of
	// first phi statement will be found set, if there exists lhs=rhs phi
	// statement, in which case even the first phi statement should not
	// perform any killing.
	if (assignment->previous_phi)
	{
		DEBUG ("\nprevious_phi is true. Setting to_kill=false");
		to_kill = false;
	}

	// if (lhs.pointer_arithmetic || rhs.pointer_arithmetic)
	//	return;
	// Assume all pointer arithmetic happen only on arrays. Ignoring
	// pointer arithmeitc on fields of structures.
	if (lhs.pointer_arithmetic)
		lhs.offset = 0;
	if (rhs.pointer_arithmetic)
		rhs.offset = 0;

#if DEBUG_CONTAINER
	if (lhs.var == rhs.var && rhs.type == SCALAR)
		DEBUG ("\nlhs.var = rhs.var = %d", lhs.var);
#endif

	// Using changing context dependent value (flow-sensitive)
	set<LIVE_VALUE_SUBTYPE *> lvalue_nodes = 
		process_lhs (value, current_context, current_block, lhs, to_kill, true);

	typename set<LIVE_VALUE_SUBTYPE *>::iterator lhsi;
	for (lhsi = lvalue_nodes.begin (); lhsi != lvalue_nodes.end (); lhsi++)
	{
		LIVE_VALUE_SUBTYPE * lvalue_node = *lhsi;
		process_rhs (value, assignment_data_index, rhs, *lvalue_node, value);
	}

	// Using unaffected context dependent value (memoized)
	// collect aux_lvalue_nodes
	LIVE_VALUE_TYPE * unaffected_context_dept = 
		get_unaffected_live_value (*current_context);
	if (!unaffected_context_dept)
		return false;

	// Mark to_kill=false and to_gen=false so that unaffected_context_dept remains unaffected.
	set<LIVE_VALUE_SUBTYPE *> lvalue_nodes_aux = 
		process_lhs (*unaffected_context_dept, current_context, current_block, lhs, false, false);
	for (lhsi = lvalue_nodes_aux.begin (); lhsi != lvalue_nodes_aux.end (); lhsi++)
	{
		LIVE_VALUE_SUBTYPE * lvalue_node = *lhsi;
		process_rhs (value, assignment_data_index, rhs, *lvalue_node, *unaffected_context_dept);
	}

	// Delete list of nodes that are unreachable from any node in IN_VALUE
	// value.clean (lvalue_node);

	DEBUG ("\nprocess_assignment_statement done");
	return true;
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
set<LIVE_VALUE_SUBTYPE *> liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
process_lhs (LIVE_VALUE_TYPE & value, 
	context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, 
	basic_block current_block, 
	constraint_expr & lhs,
	bool to_kill,
	bool to_gen)
{
	DEBUG ("\nprocess_lhs");

	LIVE_VALUE_SUBTYPE * lvalue_node = NULL;
	set<LIVE_VALUE_SUBTYPE *> lvalue_nodes;

#if DEBUG_CONTAINER
	DEBUG ("\ngraph at IN");
	value.print_value (NULL);
#endif

	// lhs = ...
	if (lhs.type == SCALAR)
	{
		DEBUG ("\nlhs.type == SCALAR");

		process_lhs_scalar (value, lhs, to_kill, lvalue_nodes);
	}

	// lhs->f = ... or *lhs = ...
	else if (lhs.type == DEREF)
	{
		DEBUG ("\nlhs.type == DEREF");

		// Find link aliases before inserting prefixes of lhs otherwise
		// newly generated prefixes of lhs are unnecesarily
		// synchronized with points-to graph.
		process_link_alias_lhs (value, current_context, current_block, lhs, lvalue_nodes);

		if (!to_gen)
			return lvalue_nodes;

		// FIXME: Since we are not performing strong updates on live
		// paths, no need to generate y as live.

		// For the explicit * in lhs
		process_lhs_deref (value, lhs, to_kill, lvalue_nodes); 
	}	

	else if (lhs.type == ADDRESSOF)
	{
		RESULT ("\nError: Lvalue error.");
	}

	else
	{
		RESULT ("\nError: Wrong lhs type");
	}

	return lvalue_nodes;
}

template <>
void liveness_analysis<deterministic_graph, deterministic_node>::
process_lhs_scalar (deterministic_graph & value, 
	constraint_expr & lhs,
	bool to_kill,
	set<deterministic_node *> & lvalue_nodes)
{
	DEBUG ("\nRetrieving destination node of lhs");
	deterministic_node * lvalue_node = value.get_destination_node (lhs.var);
	if (lvalue_node)
	{
		DEBUG ("\nlhs points to node %d", lvalue_node->get_node_id ());
		DEBUG ("\nDeleting edge for lhs %d without cleaning", lhs.var);
		if (to_kill && !program.is_array (lhs.var) && !program.is_union (lhs.var))
			value.temp_delete_edge (value.stack, lhs.var, *lvalue_node);
		lvalue_nodes.insert (lvalue_node);
	}
}

template <>
void liveness_analysis<non_deterministic_graph, non_deterministic_node>::
process_lhs_scalar (non_deterministic_graph & value, 
	constraint_expr & lhs,
	bool to_kill,
	set<non_deterministic_node *> & lvalue_nodes)
{
	DEBUG ("\nRetrieving destination node of lhs");
	set<non_deterministic_node *> temp_lvalue_nodes = value.get_destination_nodes (value.stack, lhs.var);
	set<non_deterministic_node *>::iterator ni;
	for (ni = temp_lvalue_nodes.begin (); ni != temp_lvalue_nodes.end (); ni++)
	{
		non_deterministic_node * lvalue_node = *ni;
		DEBUG ("\nlhs points to node %d", lvalue_node->get_node_id ());
		DEBUG ("\nDeleting edge for lhs %d without cleaning", lhs.var);
		if (to_kill && !program.is_array (lhs.var) && !program.is_union (lhs.var))
			value.temp_delete_edge (value.stack, lhs.var, *lvalue_node);
		lvalue_nodes.insert (lvalue_node);
	}
}

template <>
void liveness_analysis<deterministic_graph, deterministic_node>::
process_lhs_deref (deterministic_graph & value, 
	constraint_expr & lhs,
	bool to_kill,
	set<deterministic_node *> & lvalue_nodes)
{
	deterministic_node * lhs_dest = 
		value.insert_edge (value.stack, lhs.var, lhs.var * (ROOT_LINK));
	if (!lhs_dest)
	{
		RESULT ("\nError: Could not create lhs %d", lhs.var);
		return;
	}
	DEBUG ("\nlhs_dest=%d, in_edge_label=%d", lhs_dest->get_node_id (), lhs.var);
	// For the implicit * in lhs
	deterministic_node * lvalue_node = value.get_destination_node (*lhs_dest, lhs.offset);
	if (lvalue_node)
	{
		DEBUG ("\nDeleting edge for lhs %d offset %d without cleaning", 
			lhs.var, lhs.offset);
		if (to_kill)
			value.temp_delete_edge (*lhs_dest, lhs.offset, *lvalue_node);
		lvalue_nodes.insert (lvalue_node);
	}
}

template <>
void liveness_analysis<non_deterministic_graph, non_deterministic_node>::
process_lhs_deref (non_deterministic_graph & value, 
	constraint_expr & lhs,
	bool to_kill,
	set<non_deterministic_node *> & lvalue_nodes)
{
        non_deterministic_node * lhs_dest =
                value.insert_edge (value.stack, lhs.var, lhs.var * (ROOT_LINK));
        if (!lhs_dest)
        {
                RESULT ("\nError: Could not create lhs %d", lhs.var);
                return;
        }
        DEBUG ("\nlhs_dest=%d, in_edge_label=%d", lhs_dest->get_node_id (), lhs.var);
        // For the implicit * in lhs
	// Fetch all lhs_dests and not just the above created lhs_dest
	set<non_deterministic_node *> lhs_dests = 
		value.get_destination_nodes (value.stack, lhs.var);
	set<non_deterministic_node *>::iterator ldi;
	for (ldi = lhs_dests.begin (); ldi != lhs_dests.end (); ldi++)
	{
		lhs_dest = *ldi;
	        set<non_deterministic_node *> temp_lvalue_nodes =
        	        value.get_destination_nodes (*lhs_dest, lhs.offset);
	        set<non_deterministic_node *>::iterator lni;
        	for (lni = temp_lvalue_nodes.begin (); lni != temp_lvalue_nodes.end (); lni++)
	        {
        	        non_deterministic_node * lvalue_node = *lni;
                	DEBUG ("\nDeleting edge for lhs %d (node=%d) offset %d without cleaning",
	                        lhs.var, lvalue_node->get_node_id (), lhs.offset);
        	        if (to_kill)
                	        value.temp_delete_edge (*lhs_dest, lhs.offset, *lvalue_node);
	                lvalue_nodes.insert (lvalue_node);
	        }
	}
}

/**
 * Fetch lvalue_node from lvalue_graph. Generate rhs and its subgraph in value.
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
process_rhs (LIVE_VALUE_TYPE & value, 
	unsigned int assignment_data_index,
	constraint_expr & rhs,
	LIVE_VALUE_SUBTYPE & lvalue_node,
	LIVE_VALUE_TYPE & lvalue_graph)
{
	bool edge_type;
#if LIVENESS_DETERMINISTIC 
	// edge_type denotes latest use-site recording option used by only
	// <deterministic_graph>. 
	#if LATEST_USE_SITE_ONLY
		edge_type = true;
	#else
		edge_type = false;
	#endif
#else
	// edge_type denotes is_alloc_site option used by only
	// <non_deterministic_graph>.
	edge_type = false;
#endif

	// ... = rhs or ... = &(rhs->f)
	if (rhs.type == SCALAR)
	{
		DEBUG ("\nrhs.type == SCALAR");

		// Don't add rhs to in_value directly, but to gen_value, for
		// statements like x->f=x, which generate and kill the same link
	
		// For the implicit * in rhs
		LIVE_VALUE_SUBTYPE * rhs_dest = 
			value.insert_edge (value.stack, rhs.var, rhs.var * (ROOT_LINK));
		// Do not pass latest_use_only here; x=y;use x->g; then while
		// marking y->g  as live, we will discard previous use-site of
		// g and mark this use-site instead on g.
		lvalue_graph.copy_subgraph (lvalue_node, *rhs_dest, rhs.offset, value);
	}
		
	// ... = rhs->f or ... = *rhs
	else if (rhs.type == DEREF)
	{
		DEBUG ("\nrhs.type == DEREF");

		LIVE_VALUE_SUBTYPE * rhs_dest = 
			value.insert_edge (value.stack, rhs.var, rhs.var * (ROOT_LINK));
		DEBUG ("\nrhs_dest=%d", rhs_dest->get_node_id ());

		// FIXME: test9.c shows the need of context with the use-site.
		// For example, func(); func(); each of which has x=x->f; Then
		// only two dereferences of f should be marked live. But
		// without context id, infinite f are marked live.

		if (!assignment_data_index)
			RESULT ("\nError: use-site is 0");

		LIVE_VALUE_SUBTYPE * rhs_offset_dest = 
			value.insert_edge (*rhs_dest, rhs.offset, assignment_data_index, edge_type);
		DEBUG ("\nrhs_offset_dest=%d", rhs_offset_dest->get_node_id ());
		lvalue_graph.copy_subgraph (lvalue_node, *rhs_offset_dest, value);
		DEBUG ("\nInsert rhs offset %d", rhs.offset);
		DEBUG ("\nassignment_data_index=%d", assignment_data_index);

		// Nodes with repeating sites are automatically summarized
		// since we maintain the following variant: nodes are uniquely
		// identified by the use-sites. 
	}

	// ... = &rhs
	else if (rhs.type == ADDRESSOF)
	{
		DEBUG ("\nrhs.type == ADDRESSOF");

		// e.g. x=&y;t=x->g;use t then y.g is impicitly live at IN(3) and
		// y.f is dead. At IN(1), y.g is explicitly live.
		if (program.is_proper_var (rhs.var) && !program.heap_var (rhs.var))
			lvalue_graph.copy_subgraph (lvalue_node, value.stack, rhs.var, value);
	}

	else
		RESULT ("\nError: rvalue error.");
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
LIVE_VALUE_TYPE * liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
get_unaffected_live_value (context<LIVE_VALUE_TYPE, unlabeled_edges> & current_context)
{
	// Using unaffected context dependent value (memoized)
	// collect aux_lvalue_nodes
	unaffected_live<LIVE_VALUE_TYPE> * aux = 
		(unaffected_live<LIVE_VALUE_TYPE> *) current_context.get_aux_info ();
	if (!aux)
	{
		RESULT ("\nError: aux (LIVE_VALUE_TYPE) is NULL");
		return NULL;
	}
	LIVE_VALUE_TYPE * unaffected_context_dept = &aux->context_dept;

#if BYPASSING_UNAFFECTED == 0
	if (!unaffected_context_dept->is_empty ())
                RESULT ("\nError: unaffected_context_dept_pta is being used");
#endif
	return unaffected_context_dept;
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
unlabeled_edges * liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
get_points_to_in_value (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, 
	basic_block current_block)
{
	if (function_side_effects.get_is_unimp_blocks_ready ())
	{
		struct cgraph_node * func = current_context->get_function ();
		if (function_side_effects.is_block_unimportant (func, current_block->index))
			return NULL;
	}

	inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE> * dept_analysis = NULL;
	context<unlabeled_edges, LIVE_VALUE_TYPE> * dept_context = NULL;
	dept_analysis = get_dependent_analysis ();
	dept_context = get_dependent_context (current_context);
	if (!dept_context)
		return NULL;

        unaffected_pta * aux = (unaffected_pta *) dept_context->get_aux_info ();
        if (!aux)
        {
                RESULT ("\nError: aux (unaffected context_dept value) is NULL");
                return NULL;
        }

	// Get IN value + unaffected_context_indept_pta + unaffected_context_dept_pta
        unlabeled_edges * unaffected_context_indept_pta = &aux->context_indept;
        unlabeled_edges * unaffected_context_dept_pta = &aux->context_dept;
        unlabeled_edges * fs_context_dept_pta = dept_context->get_in_value (current_block);

        unlabeled_edges * points_to_in = new unlabeled_edges;
	if (unaffected_context_indept_pta)
		points_to_in->copy_value (*unaffected_context_indept_pta, false);
	if (unaffected_context_dept_pta)
	        points_to_in->copy_value (*unaffected_context_dept_pta, false);
	// Some blocks may have IMPORTANT=1 but no cfp from START to the block
	// may be important; therefore, points-to analysis of the block may
	// have not been performed.
	if (fs_context_dept_pta)
	        points_to_in->copy_value (*fs_context_dept_pta, false);

#if DEBUG_CONTAINER
	DEBUG ("\nlink alias pta=");
	points_to_in->print_value (NULL);
#endif

	return points_to_in;
}
	
/**
 * This function stores aliased lvalue nodes of lhs. Here lhs is of DEREF type.
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
process_link_alias_lhs (LIVE_VALUE_TYPE & live_value, 
	context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, 
	basic_block current_block, 
	constraint_expr & lhs,
	set<LIVE_VALUE_SUBTYPE *> & link_alias_lvalue_nodes)
{
	if (lhs.type != DEREF)
	{
		RESULT ("\nError: lhs is not DEREF");
		return;
	}

	// DEREF statements are lone statements of a block. Therefore,
	// POINTS_TO_IN is the points-to graph at IN of this statement.
	// FIXME: It could be more efficient to not SPLIT and compute points-to
	// graph for this statement. Or, at least SPLIT only if deref
	// statement is not the first statement of the block and deref is on lhs.

	// Fetch IN (and not OUT) because the points-to info required may be
	// dead at OUT. e.g. x->f=y. x and z are aliased at IN, z->f is live
	// at OUT, x may be dead at OUT.

	// FIXME: Get IN value + unaffected_context_indept_pta +
	// unaffected_context_dept_pta separately and sync with live graph
	// separately for efficiency. 

	unlabeled_edges * points_to_in = get_points_to_in_value (current_context, current_block);
	if (!points_to_in)
	{
		RESULT ("\nError: points_to_in of block=%d is NULL", current_block->index);
		return;
	}
	points_to_in->increment_reference_count ();
#if DEBUG_CONTAINER
	DEBUG ("\npoints-to");
	points_to_in->print_value (NULL);
#endif

	// A pointer-ap is an ap with * in the end. All live nodes are pointed
	// to by pointer-aps.  Let v.*.f.* be lhs.
	// v.* is either a heap node h1 or stack var w1.
	// v.*.f.* is either a heap node h2 or stack var w2.
	// We do not search for h2 and w2 in live nodes because we want to
	// restrict to link aliases and not node aliases.
	// We search for h1.f.* and w1.f.* in live nodes to find link aliases.
	// For this, we find live nodes/aps that point to h1 and w1, or live
	// nodes/aps that are w1 itself. However, the latter i.e.,  w1 ap
	// itself is not a live node since w1 is not a pointer-ap.
	// So, for the latter, we need to explicitly find live node for w1.f.*.
	// For the former, we map points-to nodes to live nodes that are both
	// pointed to by pointer-aps.

	// Get points-to nodes of lhs.var (not offset) i.e. V.* from VALUE
	set<label> may_lhs_pts_nodes;
	// For the explicit * in lhs
	points_to_in->get_destination_vars (lhs.var, may_lhs_pts_nodes);
#if DEBUG_CONTAINER
	set<label>::iterator pni;
	DEBUG ("\nmay_lhs_pts_nodes=");
	for (pni = may_lhs_pts_nodes.begin (); pni != may_lhs_pts_nodes.end (); pni++)
	{
		label pnid = *pni;
		DEBUG ("%d,", pnid);
	}
#endif

#if DEBUG_CONTAINER
	DEBUG ("\nlive_value=");
	live_value.print_value (NULL);
#endif

	// Synchronize live and points-to nodes
	map<label, set<LIVE_VALUE_SUBTYPE *> > sync_pts_live_nodes;
	sync_pts_live_value (*points_to_in, live_value, sync_pts_live_nodes);

	// Find if a pointer-ap pointing to h1 or w1, appended with f.* is live.

	// Get live nodes with may_lhs_pts_nodes and then find destination nodes via label OFFSET.*
	set<label>::iterator lptsi;
	for (lptsi = may_lhs_pts_nodes.begin (); lptsi != may_lhs_pts_nodes.end (); lptsi++)
	{
		label lhs_pts_node = *lptsi;
		if (sync_pts_live_nodes.find (lhs_pts_node) == sync_pts_live_nodes.end ())
			continue;

		// Live node aliases of lhs.var (without offset)
		set<LIVE_VALUE_SUBTYPE *> lhs_live_nodes = sync_pts_live_nodes[lhs_pts_node];

		// Find live link aliases of lhs (with offset or explicit * in lhs)
		typename set<LIVE_VALUE_SUBTYPE *>::iterator lhsi;
		DEBUG ("\nlhs_live_nodes=");
		for (lhsi = lhs_live_nodes.begin (); lhsi != lhs_live_nodes.end (); lhsi++)
		{
			LIVE_VALUE_SUBTYPE * lhs_live_node = *lhsi;
			live_value.insert_destination_nodes (*lhs_live_node, lhs.offset, link_alias_lvalue_nodes);
			DEBUG ("%d,", lhs_live_node->get_node_id ());
		}
	}
#if DEBUG_CONTAINER
	typename set<LIVE_VALUE_SUBTYPE *>::iterator lhsi;
	DEBUG ("\nlink_alias_lvalue_nodes=");
	for (lhsi = link_alias_lvalue_nodes.begin (); lhsi != link_alias_lvalue_nodes.end (); lhsi++)
	{
		LIVE_VALUE_SUBTYPE * lhs_n = *lhsi;
		DEBUG ("%d,", lhs_n->get_node_id ());
	}
#endif
	DEBUG ("\nFinding link alias lvalue nodes from stack");

	// Find if w1.f.* is live.
	
	// Find if w1 is in may_lhs_pts_nodes
	for (lptsi = may_lhs_pts_nodes.begin (); lptsi != may_lhs_pts_nodes.end (); lptsi++)
	{
		label lhs_pts_node = *lptsi;
	        csvarinfo_t lhs_info = VEC_index (csvarinfo_t, program.variable_data, lhs_pts_node);
	        if (lhs_info->is_heap_var)
			continue;

		if (!lhs_info)
		{
			RESULT ("\nError: Could not find pointee=%d of lhs", lhs_pts_node);
			continue;
		}
		DEBUG ("\nlhs_info=%s(%d)", lhs_info->name, lhs_info->id);
		// Append f to w1.
		csvarinfo_t lhs_f_info;
		if (lhs.offset)
		{
			// SVcomp test.0214 has lhs_info array, lhs.offset=0,
			// still it enters this code and finds
			// cs_first_vi_for_offset.
			DEBUG ("\nlhs.offset=%d is not 0", lhs.offset);
			lhs_f_info = program.cs_first_vi_for_offset (lhs_info, lhs.offset);
		}
		else
		{
			DEBUG ("\nlhs.offset=%d is 0", lhs.offset);
			lhs_f_info = lhs_info;
		}

		if (!lhs_f_info)
		{
			// This could happen in case of arrays.
			RESULT ("\nError: Could not find field=%d of pointee=%s(%d)",
				lhs.offset, lhs_info->name, lhs_info->id);
			lhs_f_info = lhs_info;
		}

		// Find if w1.f is a live node
		// Add the live node to link_alias_lvalue_nodes
		live_value.insert_destination_nodes (live_value.stack, lhs_f_info->id, link_alias_lvalue_nodes);
	}

	points_to_in->decrement_reference_count ();
}

/**
 * Add to assignment_data of the CALL_SITE, mappings of actual parameters to
 * formal parameters of CALLED_FUNCTION. Then process them and delete the
 * mappings if the CALL_SITE is a function pointer call.
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
process_function_arguments (context<LIVE_VALUE_TYPE, unlabeled_edges> * src_context,
	basic_block call_site,
	LIVE_VALUE_TYPE * value,
	struct cgraph_node * called_function)
{
	DEBUG ("\nprocess_function_arguments()");

	if (!value)
	{
		RESULT ("\nError: Null value");
		return;
	}

#if DEBUG_CONTAINER
	DEBUG ("\nParsed data of bb=%d before adding arguments", call_site->index);
	program.print_parsed_data (call_site);
#endif

	// Functions process_function_arguments() and process_return_value()
	// cannot distinguish between argument and return-value mappings; for
	// example in the case of recursion, both lhs and rhs may be from the
	// same function. Therefore, for a call block we clear all assignment
	// mappings (for both direct and function pointer calls) before and
	// after adding new assignments.
	((block_information *)(call_site->aux))->erase_assignment_indices ();

	// Create mappings on-the-fly
	struct cgraph_node * src_function = src_context->get_function ();
	// This function fetches the old map entry in assignment pool if it
	// exists, else creates a new map entry.
	program.map_function_pointer_arguments (src_function, call_site, called_function);

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
}

/**
 * Add to assignment_data of the CALL_SITE, mapping of returned value of
 * CALLED_FUNCTION to the received value. Then process them and delete the
 * mappings if the CALL_SITE is a function pointer call.
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
process_return_value (context<LIVE_VALUE_TYPE, unlabeled_edges> * src_context,
	basic_block call_site,
	LIVE_VALUE_TYPE * value,
	struct cgraph_node * called_function,
	bool to_kill)
{
	DEBUG ("\nprocess_return_values()");

	if (!value)
	{
		DEBUG ("\nNUll value");
		return;
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

		// This function fetches the old map entry in assignment pool
		// if it exists, else creates a new map entry.
		program.map_return_value (call_site, src_function, return_block, called_function);
	}

	// We do not want to assume that lhs receiving variable and rhs
	// returned variable are scalars. Therefore, we call
	// process_parsed_data().
	// We set TO_KILL=false, so that liveness of returned variable (rhs)
	// from the previous called function (via function pointer) is not
	// killed.
	process_parsed_data (src_context, call_site, value, to_kill);

#if DEBUG_CONTAINER
	const char * function_name = cgraph_node_name (called_function);
	DEBUG ("\nParsed data of bb=%d (function=%s) after adding return values",
		call_site->index, function_name);
	program.print_parsed_data (call_site);
#endif

	// Erase the mappings
	((block_information *)(call_site->aux))->erase_assignment_indices ();
}

/** 
 * All those paths that are possibly aliased to lhs of the statements in the
 * callee should be passed to the callee. A global in lhs is possibly aliased
 * to any local of any function. Therefore, we need to pass callees_lhs_derefs
 * (locals and globals) to the callee. We do not pass local defs because locals
 * of caller are different locals of callee (even if they are of the same
 * function).

 * To build a context, pass callees_global_defs and callees_lhs_derefs rooted
 * paths; bypass the rest. While analyzing the context, pass
 * callees_global_defs flow-sensitively; memoize the rest since we do not
 * perform strong updates on live paths.

 * Only return var among locals of the callee is live before calling the
 * callee; this also needs to be passed both for context creation and context
 * analysis. 
 */

//FIXME: This function is taking too long because callees_lhs_derefs is huge

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
LIVE_VALUE_TYPE * liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
extract_def_deref_ret_rooted_value (context<LIVE_VALUE_TYPE, unlabeled_edges> & src_context,
	struct cgraph_node * called_function,
	LIVE_VALUE_TYPE & value_out)
{
	DEBUG ("\nextract_def_deref_ret_rooted_value()");

#if (BYPASSING_UNUSED == 0 && BYPASSING_UNREACHABLE == 0)
	LIVE_VALUE_TYPE * def_deref_ret_rooted_value_full = value_out.copy_value (false);
	value_out.erase ();
	return def_deref_ret_rooted_value_full;
#endif

	set<variable_id> def_deref_ret_vars = program.get_return_vars (called_function);
	set<variable_id> * callees_global_defs = function_side_effects.get_callees_global_defs (called_function);
	set<variable_id> * callees_lhs_derefs = function_side_effects.get_callees_lhs_derefs (called_function);
	if (callees_global_defs)
		def_deref_ret_vars.insert (callees_global_defs->begin (), callees_global_defs->end ());
	if (callees_lhs_derefs)
		def_deref_ret_vars.insert (callees_lhs_derefs->begin (), callees_lhs_derefs->end ());

	// We need to pass even locals because they could be possibly link
	// aliased to lhs_derefs of callee. Eg. foo(x); use x->f;
	// foo(y){y->f=z}. Here, liveness of x->f (local) needs to be passed to
	// foo() so that y->f is live at out and z is live at in of the
	// statement y->f=z;

	set<variable_id>::iterator vi;
	RESULT ("\ncallees_global_defs=");
	if (callees_global_defs)
	 	for (vi = callees_global_defs->begin (); vi != callees_global_defs->end (); vi++)
	 		RESULT ("%d, ", *vi);
	RESULT ("\ncallees_lhs_derefs=");
	if (callees_lhs_derefs)
		for (vi = callees_lhs_derefs->begin (); vi != callees_lhs_derefs->end (); vi++)
			RESULT ("%d, ", *vi);

#if DEBUG_CONTAINER
	DEBUG ("\ndef_deref + returned vars of callee:");
	for (vi = def_deref_ret_vars.begin (); vi != def_deref_ret_vars.end (); vi++)
		DEBUG ("%d, ", *vi);
#endif

	LIVE_VALUE_TYPE * def_deref_ret_rooted_value = new LIVE_VALUE_TYPE;
	value_out.extract_subgraph (def_deref_ret_vars, *def_deref_ret_rooted_value);
	return def_deref_ret_rooted_value;
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void * liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
get_dept_context_aux (struct cgraph_node * func)
{
        // This function works when there is one context per function in the dept analysis

        inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE> * dept_analysis = 
		get_dependent_analysis ();
        if (!dept_analysis)
        {
                RESULT ("\nError: dept_analysis not found");
                return NULL;
        }

        context<unlabeled_edges, LIVE_VALUE_TYPE> * existing_dest_context =
                dept_analysis->get_function_context (func);
        if (!existing_dest_context)
        {
                RESULT ("\nError: destination context not found");
                return NULL;
        }

	void * aux = existing_dest_context->get_aux_info ();
	return aux;
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
set<struct cgraph_node *> liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
get_called_functions (context<LIVE_VALUE_TYPE, unlabeled_edges> & src_context, 
	basic_block call_site, 
	tree function_pointer)
{
	inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE> * dept_analysis = 
		get_dependent_analysis ();
	context<unlabeled_edges, LIVE_VALUE_TYPE> * dept_context = 
		get_dependent_context (&src_context);
	set<struct cgraph_node *> dest_functions;
	if (dept_context)
		// Resolve function pointers
		dest_functions = dept_analysis->get_called_functions (*dept_context, call_site);
	else
	{
		// Cannot resolve function pointers
		RESULT ("\nError: No dependent context to find function pointee");
	}

	return dest_functions;
}

/**
 * It is okay to delete locals of function when analysis of function is done.
 * If a global is implicitly live (as link alias of a local of the function),
 * i.e. either local=global; or global=local;  was present. In the former, the
 * live local will anyway get transferred to global before being deleted. In
 * latter, global rooted path is anyway dead.
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
delete_local_variables (struct cgraph_node * src_function, 
	struct cgraph_node * function, 
	LIVE_VALUE_TYPE & in_value, 
	void * info)
{
	// FIXME: THIS context is not being called by a context of FUNCTION.
	// Instead of deleting locals of only FUNCTION, can we delete all
	// locals (even those other than FUNCTION) -- perhaps after checking
	// that there is no context of other that other function calling this
	// context..

	// If x->f->g (local) is live and address of g is taken or target of g
	// is address taken (which does not require ampersand e.g. z=x->f->g),
	// then also we cannot delete x->f->g because a recursive call (from
	// THIS function only) may be dependent on this live AP. 

	set<label> local_variables;
	program.get_local_variables (function, local_variables);
	program.get_function_parameters (function, local_variables);

#if DEBUG_CONTAINER
	set<label>::iterator vi;
	DEBUG ("\nLocal+parameter variables: ");
	for (vi = local_variables.begin (); vi != local_variables.end (); vi++)
		DEBUG ("%d, ", *vi);
#endif

	set<label>::iterator li;
	for (li = local_variables.begin (); li != local_variables.end (); li++)
	{
		label l = *li;
		in_value.delete_edge (in_value.stack, l, false);
	}

	in_value.clean ();
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
bool liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
is_dest_of_dept_context_exist (context<LIVE_VALUE_TYPE, unlabeled_edges> * src_context,
	basic_block call_site,
	struct cgraph_node * dest_function)
{
        DEBUG ("\nis_dest_dept_context_exist()");

	context<unlabeled_edges, LIVE_VALUE_TYPE> * dest_dept_context = 
		get_dest_of_dept_context (src_context, call_site, dest_function);
	if (!dest_dept_context)
		return false;

	basic_block end_block = dest_dept_context->get_end_block ();
	if (!end_block)
		RESULT ("\nError: end_block is null");
	unlabeled_edges * dest_fn_out_value = dest_dept_context->get_in_value (end_block);

	if (!dest_fn_out_value)
		return false;

	return true;
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
sync_pts_live_value (unlabeled_edges & pts_value,
	LIVE_VALUE_TYPE & live_value,
	map<label, set<LIVE_VALUE_SUBTYPE *> > & sync_pts_live_nodes,
	set<label> & internal_live_pts_nodes,
	set<label> & leaf_live_pts_nodes)
{
	sync_pts_live_value (0, live_value.stack, pts_value, live_value, sync_pts_live_nodes,
		internal_live_pts_nodes, leaf_live_pts_nodes);

#if DEBUG_CONTAINER
	typename map<label, set<LIVE_VALUE_SUBTYPE *> >::iterator pli;
	DEBUG ("\nsync_pts_live_nodes=");
	for (pli = sync_pts_live_nodes.begin (); pli != sync_pts_live_nodes.end (); pli++)
	{
		label pts_node = pli->first;
		set<LIVE_VALUE_SUBTYPE *> live_nodes = pli->second;
		typename set<LIVE_VALUE_SUBTYPE *>::iterator lni;
		for (lni = live_nodes.begin (); lni != live_nodes.end (); lni++)
		{
			LIVE_VALUE_SUBTYPE * live_node = *lni;
			DEBUG ("(%d,%d),", pts_node, live_node->get_node_id ());
		}
	}
#endif
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
sync_pts_live_value (unlabeled_edges & pts_value,
	LIVE_VALUE_TYPE & live_value,
	map<label, set<LIVE_VALUE_SUBTYPE *> > & sync_pts_live_nodes)
{
	set<label> internal_live_pts_nodes;
	set<label> leaf_live_pts_nodes;
	sync_pts_live_value (0, live_value.stack, pts_value, live_value, sync_pts_live_nodes,
		internal_live_pts_nodes, leaf_live_pts_nodes);

#if DEBUG_CONTAINER
	typename map<label, set<LIVE_VALUE_SUBTYPE *> >::iterator pli;
	DEBUG ("\nsync_pts_live_nodes=");
	for (pli = sync_pts_live_nodes.begin (); pli != sync_pts_live_nodes.end (); pli++)
	{
		label pts_node = pli->first;
		set<LIVE_VALUE_SUBTYPE *> live_nodes = pli->second;
		typename set<LIVE_VALUE_SUBTYPE *>::iterator lni;
		for (lni = live_nodes.begin (); lni != live_nodes.end (); lni++)
		{
			LIVE_VALUE_SUBTYPE * live_node = *lni;
			DEBUG ("(%d,%d),", pts_node, live_node->get_node_id ());
		}
	}
#endif
}

/**
 * This function maps points-to nodes with live nodes where both are pointed to
 * by pointer-aps (i.e. access paths with * in the end). It does not map
 * points-to nodes that are not pointed by pointer-aps (including stack/root
 * variables/aps).
 *
 * This function maps each pts node to its live node. It also collects the pts
 * nodes corresponding to internal live nodes in internal_live_pts_nodes and
 * collects pts nodes corresponding to the leaf live nodes in
 * leaf_live_pts_nodes.
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
sync_pts_live_value (label pts_node,
        LIVE_VALUE_SUBTYPE & live_node,
        unlabeled_edges & pts_value,
        LIVE_VALUE_TYPE & live_value,
        map<label, set<LIVE_VALUE_SUBTYPE *> > & sync_pts_live_nodes,
	set<label> & internal_live_pts_nodes,
	set<label> & leaf_live_pts_nodes)
{
        DEBUG ("\nsync_pts_live_value (pts=%d,live=%d)", pts_node, live_node.get_node_id ());
#if DEBUG_CONTAINER
        DEBUG ("\npoints-to");
        pts_value.print_value (NULL);
        DEBUG ("\nlive");
        live_value.print_value (NULL);
#endif

        if (sync_pts_live_nodes[pts_node].find (&live_node) 
		!= sync_pts_live_nodes[pts_node].end ())
                return;

        sync_pts_live_nodes[pts_node].insert (&live_node);

        set<label> out_edge_labels;
        live_node.get_out_edge_labels (out_edge_labels);

	if (pts_node)
	{
		// If live_node is an internal node
		if (out_edge_labels.size ())
			internal_live_pts_nodes.insert (pts_node);
		// Else if live_node is a leaf node
		else
			leaf_live_pts_nodes.insert (pts_node);
	}

        set<label>::iterator li;
        for (li = out_edge_labels.begin (); li != out_edge_labels.end (); li++)
        {
                // Live node for rho.L.*
                label l = *li;

		if (!pts_node)
			internal_live_pts_nodes.insert (l);

                set<LIVE_VALUE_SUBTYPE *> out_live_ns = live_value.get_destination_nodes (live_node, l);
                if (out_live_ns.empty ())
                {
                        RESULT ("\nError: dest of live_node=%d via l=%d not found", live_node.get_node_id (), l);
                        continue;
                }
                typename set<LIVE_VALUE_SUBTYPE *>::iterator ni;
                for (ni = out_live_ns.begin (); ni != out_live_ns.end (); ni++)
                {
                        LIVE_VALUE_SUBTYPE * out_live_n = *ni;
                        DEBUG ("\nlive=%d->%d->%d", live_node.get_node_id (), l, out_live_n->get_node_id ());

                        // Points-to node for rho.L.*
                        set<label> dest_vars;
                        if (pts_node)
			{
				if (l)
				{
					set<label> out_field_nodes = program.get_var_fields (pts_node, l);
#if DEBUG_CONTAINER
	                                set<label>::iterator ofni;
        	                        DEBUG ("\nout-field of pts node %d via field %d=", pts_node, l);
                	                for (ofni = out_field_nodes.begin (); ofni != out_field_nodes.end (); ofni++)
                        	                DEBUG ("%d,", *ofni);
#endif

					pts_value.get_destination_vars (out_field_nodes, dest_vars);

					internal_live_pts_nodes.insert (out_field_nodes.begin (), out_field_nodes.end ());
				}
				else
				{
					pts_value.get_destination_vars (pts_node, dest_vars);
				}
			}
                        else
                                pts_value.get_destination_vars (l, dest_vars);

                        set<label>::iterator pi;
                        for (pi = dest_vars.begin (); pi != dest_vars.end (); pi++)
                        {
                                label out_pts_n = *pi;
                                sync_pts_live_value (out_pts_n, *out_live_n, pts_value, live_value, 
					sync_pts_live_nodes, internal_live_pts_nodes, leaf_live_pts_nodes);
                        }
                }
        }
}

/**
 * Definition of a template specialized function should come before its call.
 */

/** 
 * Points-to edges x->h1, y->h1, h1.f->h2, h2.g->h3 
 * non_deterministic_graph liveness: (denoting a node with
 * label,alloc_site,use_site):
 * <0,0,0>->x-><x,-h1,0>, <x,-h1,0>->f-><f,-h2,0>, <f,-h2,0>->g-><g,-h3,0>. 
 * <0,0,0>->y-><y,-h1,0>, <y,-h1,0>->f-><f,-h2,0>, <f,-h2,0>->g-><g,-h3,0>.
 * Therefore, a points-to edge should be considered as many times we arrive
 * from a new root variable. 
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
generate_live_edge (label pts_src_nid,
	LIVE_VALUE_SUBTYPE & live_src_node,
	LIVE_VALUE_TYPE & live_value,
	unlabeled_edges & pts_value,
	set<label> & valid_pts_nodes,
	set<pair<label, label> > & visited_pts_live_nodes)
{
	label live_src_nid = live_src_node.get_node_id ();
	DEBUG ("\ngenerate_live_edge (pts_src_nid=%d, live_src_node=%d", 
		pts_src_nid, live_src_nid);

	if (valid_pts_nodes.find (pts_src_nid) == valid_pts_nodes.end ())
		return;

	if (visited_pts_live_nodes.find (make_pair (pts_src_nid, live_src_nid)) 
		!= visited_pts_live_nodes.end ())
		return;

	visited_pts_live_nodes.insert (make_pair (pts_src_nid, live_src_nid));

	label l;
	if (live_src_node.is_stack_node ())
		l = pts_src_nid;
	else
		l = 0;

	// Create live edge with label l (representing l.* in our liveness
	// graph), if pts_src_nid has out_edge on 0 i.e.  dereference with *.
	generate_live_edge (pts_src_nid, live_src_node, l, live_value, pts_value,
		valid_pts_nodes, visited_pts_live_nodes);

	// No live edges field f.* can be created from live stack node. Live
	// edges field f.* can be created only from an already existing access
	// path (non stack node).
	if (live_src_node.is_stack_node ())
		return;

	// Check if f.* is also present in pts_value 
	map<label, set<label> > out_field_edges;
	program.get_all_typecasted_out_fields (pts_src_nid, out_field_edges);
	map<label, set<label> >::iterator ei;
	for (ei = out_field_edges.begin (); ei != out_field_edges.end (); ei++)
	{
		l = ei->first;
		set<label> dests = ei->second;
		set<label>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
		{
			label out_field_n = *di;
			if (valid_pts_nodes.find (out_field_n) == valid_pts_nodes.end ())
				continue;
			
			// Append l.* in live edge if .* exists from out_field_n in pts_value
			generate_live_edge (out_field_n, live_src_node, l, live_value, pts_value,
				valid_pts_nodes, visited_pts_live_nodes);
		}
	}
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
generate_live_edge (label pts_src_nid,
	LIVE_VALUE_SUBTYPE & live_src_node,
	label l,
	LIVE_VALUE_TYPE & live_value,
	unlabeled_edges & pts_value,
	set<label> & valid_pts_nodes,
	set<pair<label, label> > & visited_pts_live_nodes)
{
	if (valid_pts_nodes.find (pts_src_nid) == valid_pts_nodes.end ())
		return;
	
        set<label> dest_vars;
        pts_value.get_destination_vars (pts_src_nid, dest_vars);
        set<label>::iterator pi;
        for (pi = dest_vars.begin (); pi != dest_vars.end (); pi++)
        {
                label out_pts_n = *pi;
		if (valid_pts_nodes.find (out_pts_n) == valid_pts_nodes.end ())
			continue;

		bool edge_type;
		#if LIVENESS_DETERMINISTIC 
			// edge_type denotes latest use-site recording option
			// used by only <deterministic_graph>. 
			#if LATEST_USE_SITE_ONLY
				edge_type = true;
			#else
				edge_type = false;
			#endif
		#else
			// edge_type denotes is_alloc_site option used by only
			// <non_deterministic_graph>.
			edge_type = true;
		#endif

		// We add live edge with site of pts node.
		LIVE_VALUE_SUBTYPE * live_dest_node = 
			live_value.insert_edge (live_src_node, l, out_pts_n * (ROOT_LINK), edge_type);
		
#if DEBUG_CONTAINER
		DEBUG ("\npts_edge %d->%d->%d", pts_src_nid, 0, out_pts_n);
		DEBUG ("\nlive_edge %d->%d->%d", 
			live_src_node.get_node_id (), l, live_dest_node->get_node_id ()); 
#endif

		generate_live_edge (out_pts_n, *live_dest_node, live_value, pts_value,
			valid_pts_nodes, visited_pts_live_nodes); 
        }
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
generate_live_access_paths (LIVE_VALUE_TYPE & live_value,
	unlabeled_edges & pts_value,
	set<label> & valid_pts_nodes)
{
	set<label>::iterator ni;
	for (ni = valid_pts_nodes.begin (); ni != valid_pts_nodes.end (); ni++)
	{
		label nid = *ni;
        	csvarinfo_t var = VEC_index (csvarinfo_t, program.variable_data, nid);

		// A pts-edge should be considered as many times as we arrive
		// from a new root variable. Therefore, reinitialize visited set.
		// A pts-node's out-edges should be considered every time for a
		// new corresponding live node. Therefore, use visited pair of
		// live,pts nodes rather than visited pts nodes.
		set<pair<label, label> > visited_pts_live_nodes;

		if (var && var->decl && !var->is_heap_var)
		{
			DEBUG ("\nvar=%s(%d)", var->name, var->id);
			generate_live_edge (nid, live_value.stack, live_value, pts_value, 
				valid_pts_nodes, visited_pts_live_nodes);
		}
	}
}

/**
 * Generate link alias closure of all live access paths. (KSK07).
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
generate_alias_closure (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, 
	basic_block current_block)
{
	DEBUG ("\ngenerate_alias_closure()");

	// FIXME: Get IN value + unaffected_context_indept_pta +
	// unaffected_context_dept_pta separately and sync with live graph
	// separately for efficiency. 

	unlabeled_edges * points_to_in = get_points_to_in_value (current_context, current_block);
	if (!points_to_in)
	{
		RESULT ("\nError: points_to_in of block=%d is NULL", current_block->index);
		return;
	}

	points_to_in->increment_reference_count ();

	set<label> reaching_nodes;

	// Find live pts nodes using flow-sensitive live value
	LIVE_VALUE_TYPE * live_value_in = current_context->get_in_value (current_block);
	if (!live_value_in)
		return;

	LIVE_VALUE_TYPE * unaffected_context_dept_live = 
		get_unaffected_live_value (*current_context);

#if DEBUG_CONTAINER
	DEBUG ("\npoints-to:");
	points_to_in->print_value (NULL);
	DEBUG ("\nliveness before alias closure:");
	live_value_in->print_value (NULL);
	DEBUG ("\nunaffected_context_dept_live before alias closure:");
	if (unaffected_context_dept_live)
		unaffected_context_dept_live->print_value (NULL);
#endif

	// FIXME: If live_value is simply x, then leaf node is node n pointed
	// to by x. However, link aliased paths are not all those that reach
	// reaching_nodes. It should be those paths that reach internal nodes
	// and use the last live link. e.g. pts_value = x->n->n, live_value =
	// x. Then x is internal_node, n is leaf_node, reaching_nodes=x,n. But
	// live APs are x only. not x.*, x.*.*, x.*.*.*.

	get_live_pts_nodes (*live_value_in, *points_to_in, reaching_nodes);
	generate_live_access_paths (*live_value_in, *points_to_in, reaching_nodes);
	reaching_nodes.clear ();

	if (unaffected_context_dept_live)
	{
		// Fetch live pts nodes using liveness of unaffected live value
		get_live_pts_nodes (*unaffected_context_dept_live, *points_to_in, reaching_nodes);
		// Generate link aliases in flow-sensitive live_value
		generate_live_access_paths (*live_value_in, *points_to_in, reaching_nodes);
	}

	// Call clean after generating alias closure -- in case of
	// deterministic_graph, due to make-deterministic operation, some nodes
	// may become unreachable.
	live_value_in->clean ();

	points_to_in->decrement_reference_count ();
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
get_live_pts_nodes (LIVE_VALUE_TYPE & live_value,
	unlabeled_edges & pts_value,
	set<label> & reaching_nodes)
{
	// Synchronize live and points-to nodes
	// Extract live_pts_nodes --- link and node aliased live pts nodes
	map<label, set<LIVE_VALUE_SUBTYPE *> > sync_pts_live_nodes;
	set<label> live_node_aliased_pts_nodes;
	set<label> live_leaf_link_aliased_pts_nodes;
	sync_pts_live_value (pts_value, live_value, sync_pts_live_nodes,
		live_node_aliased_pts_nodes, live_leaf_link_aliased_pts_nodes);

	// Find nodes reaching node aliased live pts nodes
	pts_value.compute_in_edge_list ();
	pts_value.get_reaching_vars (live_node_aliased_pts_nodes, reaching_nodes);

	// Add live link aliased pts nodes
	reaching_nodes.insert (live_leaf_link_aliased_pts_nodes.begin (),
		live_leaf_link_aliased_pts_nodes.end ());

#if DEBUG_CONTAINER
	set<label>::iterator di;
	DEBUG ("\nlive_node_aliased_pts_nodes=");
	for (di = live_node_aliased_pts_nodes.begin (); 
		di != live_node_aliased_pts_nodes.end (); 
		di++)
		DEBUG ("%d,", *di);
	DEBUG ("\nlive_leaf_link_aliased_pts_nodes=");
	for (di = live_leaf_link_aliased_pts_nodes.begin (); 
		di != live_leaf_link_aliased_pts_nodes.end (); 
		di++)
		DEBUG ("%d,", *di);
	DEBUG ("\nreaching_nodes=");
	for (di = reaching_nodes.begin (); 
		di != reaching_nodes.end (); 
		di++)
		DEBUG ("%d,", *di);
#endif
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
LIVE_VALUE_TYPE * liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
extract_changing_context_dept_live (context<LIVE_VALUE_TYPE, unlabeled_edges> & curr_context,
	LIVE_VALUE_TYPE & context_dept_live)
{
	struct cgraph_node * func = curr_context.get_function ();
	set<variable_id> callees_glob_defs_ret = program.get_return_vars (func);
	// Pass callees_global_defs (and not function_global_defs)
	// flow-sensitively because if v is killed in a transitive callee, it
	// is killed in the immediate callee just before the call to the
	// transitive callee also.

	set<variable_id> * callees_glob_defs = function_side_effects.get_callees_global_defs (func);
	if (callees_glob_defs)
		callees_glob_defs_ret.insert (callees_glob_defs->begin (), callees_glob_defs->end ());
	
	LIVE_VALUE_TYPE * def_ret_rooted_value = new LIVE_VALUE_TYPE;
	context_dept_live.extract_subgraph (callees_glob_defs_ret, *def_ret_rooted_value);
	return def_ret_rooted_value;
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
copy_unaffected_context_dept_aux (LIVE_VALUE_TYPE & src_graph, 
	context<LIVE_VALUE_TYPE, unlabeled_edges> & dest_context,
	bool is_erase_old)
{
#if DEBUG_CONTAINER
	RESULT ("\nsrc_graph=");
	src_graph.print_value (NULL);
#endif
	unaffected_live<LIVE_VALUE_TYPE> * dest_aux = 
		(unaffected_live<LIVE_VALUE_TYPE> *) dest_context.get_aux_info ();
	if (!dest_aux)
	{
		dest_aux = new unaffected_live<LIVE_VALUE_TYPE>;
		dest_context.set_aux_info (dest_aux);
	}

	// Each END value (context-dept value) has only one unaffected subset.
	// Therefore, erase any old data and set this new subset. This is
	// required if the same context is being reused for some other END
	// value.
#if DEBUG_CONTAINER
	DEBUG ("\ndest_graph aux (before erase)=")
	dest_aux->context_dept.print_value (NULL);
#endif
	if (is_erase_old)
		dest_aux->context_dept.erase ();
#if DEBUG_CONTAINER
	RESULT ("\ndest_graph aux (after erase)=")
	dest_aux->context_dept.print_value (NULL);
#endif
	dest_aux->context_dept.copy_value (src_graph, false);
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
copy_unaffected_context_dept_live (context<LIVE_VALUE_TYPE, unlabeled_edges> & src_context,
	basic_block call_site,
	struct cgraph_node * dest_function,
	LIVE_VALUE_TYPE & value)
{
	context<LIVE_VALUE_TYPE, unlabeled_edges> * dest_context = 
		src_context.get_destination_context (call_site, dest_function);
	if (!dest_context)
	{
		RESULT ("\nError: dest context of src-context=%d, function=%s not created",
			src_context.get_context_id (), cgraph_node_name (dest_function));
		return;
	}

	unaffected_live<LIVE_VALUE_TYPE> * aux = 
		(unaffected_live<LIVE_VALUE_TYPE> *) dest_context->get_aux_info ();
	if (!aux)
	{
		RESULT ("\nError: aux (LIVE_VALUE_TYPE) is NULL");
		return;
	}
	LIVE_VALUE_TYPE * unaffected_context_dept_live = &aux->context_dept;
	if (!unaffected_context_dept_live)
	{
		RESULT ("\nError: aux of dest_context is NULL");
		return;
	}
	value.copy_value (*unaffected_context_dept_live, false);
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
delete_aux_info (void * aux_info)
{
	DEBUG ("\nliveness_analysis::delete_aux_info()");
#if GC
        if (aux_info)
                delete ((unaffected_live<LIVE_VALUE_TYPE> *) aux_info);
#endif
}

/**
 * aux_info of allocation_site_based_analysis<variables> represents bypassed
 * points-to graph due to this call only. aux_info of
 * allocation_site_based_analysis <LIVE_VALUE_TYPE> (that is computed in
 * meet_over_valid_paths) represents bypassed points-to graph of all the
 * previous calls.
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>:: 
save_context_indept_live (context<LIVE_VALUE_TYPE, unlabeled_edges> & src_context,
        basic_block call_site,
        struct cgraph_node * dest_function,
        LIVE_VALUE_TYPE & context_indept_live)
{
        context<LIVE_VALUE_TYPE, unlabeled_edges> * dest_context =
                src_context.get_destination_context (call_site, dest_function);
        if (!dest_context)
        {
                RESULT ("\nError: dest context of src-context=%d, function=%s not created",
                        src_context.get_context_id (), cgraph_node_name (dest_function));
                return;
        }

        copy_context_indept_aux (context_indept_live, *dest_context);
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>:: 
copy_context_indept_aux (LIVE_VALUE_TYPE & src_value,
        context<LIVE_VALUE_TYPE, unlabeled_edges> & dest_context)
{
        unaffected_live<LIVE_VALUE_TYPE> * dest_aux = 
		(unaffected_live<LIVE_VALUE_TYPE> *) dest_context.get_aux_info ();
        if (!dest_aux)
        {
                dest_aux = new unaffected_live<LIVE_VALUE_TYPE>;
                DEBUG ("\ncopy_context_indept_aux new %x", dest_aux);
                dest_context.set_aux_info (dest_aux);
        }

        dest_aux->context_indept.copy_value (src_value, false);
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
copy_context_value (void * src_con, void * dest_con)
{
        context<LIVE_VALUE_TYPE, unlabeled_edges> * src_context =
                (context<LIVE_VALUE_TYPE, unlabeled_edges> *) src_con;
        context<LIVE_VALUE_TYPE, unlabeled_edges> * dest_context =
                (context<LIVE_VALUE_TYPE, unlabeled_edges> *) dest_con;

        unaffected_live<LIVE_VALUE_TYPE> * src_aux = 
		(unaffected_live<LIVE_VALUE_TYPE> *) src_context->get_aux_info ();
        if (!src_aux)
                return;

        copy_context_indept_aux (src_aux->context_indept, *dest_context);
        copy_unaffected_context_dept_aux (src_aux->context_dept, *dest_context, false);
}

/** 
 * Accumulate in callee, context_indept (aux) from callers.
 */

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
bool liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
caller_to_callee_info (context<LIVE_VALUE_TYPE, unlabeled_edges> & con)
{
        DEBUG ("\npull_info(unique_context=%d)", con.get_context_id ());

        unaffected_live<LIVE_VALUE_TYPE> * aux_info = 
		(unaffected_live<LIVE_VALUE_TYPE> *) con.get_aux_info ();
        // This is not error. aux of main is NULL.
        if (!aux_info)
                return true;

        LIVE_VALUE_TYPE * con_context_indept = &aux_info->context_indept;
        LIVE_VALUE_TYPE * old_con_context_indept = con_context_indept->copy_value (false);

        set<context<LIVE_VALUE_TYPE, unlabeled_edges> *> source_contexts;
        get_source_contexts (con, source_contexts);
        typename set<context<LIVE_VALUE_TYPE, unlabeled_edges> *>::iterator sci;
        for (sci = source_contexts.begin (); sci != source_contexts.end (); sci++)
        {
                context<LIVE_VALUE_TYPE, unlabeled_edges> * sc = *sci;
                unaffected_live<LIVE_VALUE_TYPE> * src_aux = 
			(unaffected_live<LIVE_VALUE_TYPE> *) sc->get_aux_info ();
                if (!src_aux)
                        continue;
                copy_context_indept_aux (src_aux->context_indept, con);
        }

        LIVE_VALUE_TYPE * new_con_context_indept = &aux_info->context_indept;
#if DEBUG_CONTAINER
        DEBUG ("\naux of context=%d", con.get_context_id ());
        new_con_context_indept->print_value (NULL);
#endif
        bool is_aux_same = new_con_context_indept->is_value_same (*old_con_context_indept);

        delete old_con_context_indept;

        return is_aux_same;
}


template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
print_aux_info (void * aux_info)
{
#if DEBUG_CONTAINER
	if (!aux_info)
	{
		DEBUG ("\naux=NULL");
		return;
	}

	unaffected_live<LIVE_VALUE_TYPE> * aux = 
		(unaffected_live<LIVE_VALUE_TYPE> *) aux_info;
	DEBUG ("\ncontext_indept aux=");
	aux->context_indept.print_value (NULL);

	DEBUG ("\ncontext_dept aux=");
	aux->context_dept.print_value (NULL);
#endif
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
copy_live_values (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, 
        basic_block current_block,
	LIVE_VALUE_TYPE & all_live_values)
{
        unaffected_live<LIVE_VALUE_TYPE> * aux = 
		(unaffected_live<LIVE_VALUE_TYPE> *) current_context->get_aux_info ();
        if (!aux)
        {
                RESULT ("\nError: aux (unaffected context_dept value) is NULL");
                return;
        }

	if (function_side_effects.get_is_unimp_blocks_ready ())
	{
		struct cgraph_node * func = current_context->get_function ();
		if (function_side_effects.is_block_unimportant (func, current_block->index))
			return;
	}

        // Get IN value + unaffected_context_indept_live + unaffected_context_dept_live
        LIVE_VALUE_TYPE * unaffected_context_indept_live = &aux->context_indept;
        LIVE_VALUE_TYPE * unaffected_context_dept_live = &aux->context_dept;
        LIVE_VALUE_TYPE * fs_context_dept_live = current_context->get_in_value (current_block);

	if (unaffected_context_indept_live)
		all_live_values.copy_value (*unaffected_context_indept_live, false);
	if (unaffected_context_dept_live)
		all_live_values.copy_value (*unaffected_context_dept_live, false);
	if (fs_context_dept_live)
		all_live_values.copy_value (*fs_context_dept_live, false);

	all_live_values.clean ();
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
get_access_paths (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, 
        basic_block current_block,
	set<list<label> > & all_aps,
	unsigned int & tot_aps,
	bool is_accum_aps)
{
        unaffected_live<LIVE_VALUE_TYPE> * aux = 
		(unaffected_live<LIVE_VALUE_TYPE> *) current_context->get_aux_info ();
        if (!aux)
        {
                RESULT ("\nError: aux (unaffected context_dept value) is NULL");
                return;
        }

	if (function_side_effects.get_is_unimp_blocks_ready ())
	{
		struct cgraph_node * func = current_context->get_function ();
		if (function_side_effects.is_block_unimportant (func, current_block->index))
			return;
	}

        // Get IN value + unaffected_context_indept_live + unaffected_context_dept_live
        LIVE_VALUE_TYPE * unaffected_context_indept_live = &aux->context_indept;
        LIVE_VALUE_TYPE * unaffected_context_dept_live = &aux->context_dept;
        LIVE_VALUE_TYPE * fs_context_dept_live = current_context->get_in_value (current_block);

	struct cgraph_node * cnode = current_context->get_function ();

	// Since get_k_access_paths() is not collect unique APs, tot_aps may
	// have repetitions for following three graphs.
	if (unaffected_context_indept_live)
		unaffected_context_indept_live->get_k_access_paths (all_aps, tot_aps, is_accum_aps, cnode);
	if (unaffected_context_dept_live)
		unaffected_context_dept_live->get_k_access_paths (all_aps, tot_aps, is_accum_aps, cnode);
	if (fs_context_dept_live)
		fs_context_dept_live->get_k_access_paths  (all_aps, tot_aps, is_accum_aps, cnode);
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
get_access_paths_stats (set<list<label> > & aps,
	unsigned int & local_aps,
	unsigned int & global_aps)
{
	set<list<label> >::iterator api;
	for (api = aps.begin (); api != aps.end (); api++)
	{
		label v = *(api->begin ());
		if (program.global_var (v))
			global_aps++;
		else
			local_aps++;
	}
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
get_pt_live_stats (context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context, 
        basic_block current_block,
	LIVE_VALUE_TYPE & all_live_values,
	unsigned int & tot_program_aps_count,
	unsigned int & tot_pta_aps_count, 
	unsigned int & tot_valid_aps_count,
	unsigned int (& valid_percent_func_count)[21],
	map<function_index, unsigned int> & func_pta,
	float & valid_percent,
	unsigned int & pt_aps_locals,
	unsigned int & pt_aps_globals,
	unsigned int & valid_aps_locals,
	unsigned int & valid_aps_globals)
{
	struct cgraph_node * function = current_context->get_function ();
	block_index block_id = current_block->index;
	unsigned int tot_aps = 0;
	bool is_accum_aps;

	/////////////////////////////////////////////////////////////////////////////////////

	// Extract APs from all contexts of the block
#if INFO_CONTAINER
	//all_live_values.print_value (NULL);
#endif
	// Accumulate live_aps so that intersection of live and pt aps can be taken
	is_accum_aps = true;
	set<list<label> > live_aps;
	all_live_values.get_k_access_paths (live_aps, tot_aps, is_accum_aps, function);
	STATS ("\n    live in-bb=%d", block_id);
	STATS ("\n\t\ttot_aps=%d", tot_aps);
	#if INFO_CONTAINER
	LIVE_VALUE_TYPE::print_access_paths (live_aps);
	#endif
	tot_program_aps_count += tot_aps;
			
	/////////////////////////////////////////////////////////////////////////////////////

	unlabeled_edges * points_to_in = get_points_to_in_value (current_context, current_block);
	if (!points_to_in)
	{
		STATS ("\nError: points-to-in of bb=%d NULL", block_id);
		return;
	}

	points_to_in->increment_reference_count ();

	set<list<label> > pt_aps;
	points_to_in->get_access_paths (pt_aps, function);
	STATS ("\n    pta in-bb=%d", block_id);
	STATS ("\n\t\ttot_pta_aps=%d", pt_aps.size ());
	#if INFO_CONTAINER
	LIVE_VALUE_TYPE::print_access_paths (pt_aps);
	#endif
	unsigned int pta_aps_count = pt_aps.size ();
	tot_pta_aps_count += pta_aps_count;
	func_pta[function->uid] = pta_aps_count;

	points_to_in->decrement_reference_count ();

	/////////////////////////////////////////////////////////////////////////////////////

	// Sync live and pta graphs then find live APs over nodes that have
	// corresponding pta node. This is imprecise. Some valid live nodes may
	// contain in-fields/APs that may still not be present in points-to
	// graph. mcf therefore gets more valid APs than points-to APs.

	unsigned int valid_aps_count = 0;
	set<list<label> > valid_aps;
	STATS ("\n    valid live in-bb=%d", block_id);
	set<list<label> >::iterator api;
	for (api = live_aps.begin (); api != live_aps.end (); api++)
	{
		list<label> ap = *api;
		if (pt_aps.find (ap) != pt_aps.end ())
		{
			valid_aps_count++;
			// valid_aps.insert (ap);
			#if INFO_CONTAINER
			LIVE_VALUE_TYPE::print_access_path (ap);
			#endif
		}
	}	
	STATS ("\n\t\tvalid_aps_count=%d", valid_aps_count);
	tot_valid_aps_count += valid_aps_count;

	FILE * stat_file = fopen (STAT_FILE, "a");
	fprintf (stat_file, "\n\ttot_mem = %d", pta_aps_count);
	fprintf (stat_file, "\n\tvalid_mem = %d", valid_aps_count);
	fclose (stat_file);

	/////////////////////////////////////////////////////////////////////////////////////

	if (pta_aps_count)
		valid_percent += ((float) valid_aps_count) / pta_aps_count;

	/////////////////////////////////////////////////////////////////////////////////////

//	unsigned int this_pt_aps_locals = 0;
//	unsigned int this_pt_aps_globals = 0;
//	unsigned int this_valid_aps_locals = 0;
//	unsigned int this_valid_aps_globals = 0;
//	get_access_paths_stats (pt_aps, this_pt_aps_locals, this_pt_aps_globals);
//	get_access_paths_stats (valid_aps, this_valid_aps_locals, this_valid_aps_globals);
//	STATS ("\nthis_pt_local_aps=%d, this_pt_global_aps=%d, this_valid_local_aps=%d, this_valid_global_aps=%d",
//		this_pt_aps_locals, this_pt_aps_globals, this_valid_aps_locals, this_valid_aps_globals);
//		
//	pt_aps_locals += this_pt_aps_locals;
//	pt_aps_globals += this_pt_aps_globals;
//	valid_aps_locals += this_valid_aps_locals;
//	valid_aps_globals += this_valid_aps_globals;

	if (valid_aps_count > pta_aps_count)
	{
		STATS ("\nErorr: valid_aps_count > pta_aps_count");
		return; 
	}

	if (pta_aps_count)
	{
		float valid_percent = valid_aps_count / ((float) pta_aps_count);
		unsigned int slot = valid_percent * 20;
		if (slot == 20)
			slot = 19;
		valid_percent_func_count[slot]++;
		STATS ("\nvalid percent = %f \%", valid_percent * 100);
	}
	else
	{
		valid_percent_func_count[20]++;
		STATS ("\nvalid percent = 0 (no pta)");
	}
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
print_value (LIVE_VALUE_TYPE & g)
{
	g.print_value (OPEN_FST_FILE);
}

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
print_analysis_statistics (map<function_index, context_enums<LIVE_VALUE_TYPE, unlabeled_edges> > & function_contexts)
{
	STATS ("\nLIVENESS ANALYSIS (MAX_LEN_PRINT=%d)\n===============\n", MAX_LEN_PRINT);

	map<function_index, unsigned int> func_pta;
	unsigned int valid_percent_func_count[21] = {0};
	float valid_percent = 0.0;
	unsigned int tot_program_aps_count = 0;
	unsigned int tot_pta_aps_count = 0;
	unsigned int tot_valid_aps_count = 0;

	unsigned int pt_aps_locals = 0;
	unsigned int pt_aps_globals = 0;
	unsigned int valid_aps_locals = 0;
	unsigned int valid_aps_globals = 0;

	unsigned int node_count = 0;
	unsigned int edge_count = 0;
	unsigned int use_sites_count = 0;
	set<site> unique_use_sites;

	unsigned int program_blocks = 0;
	unsigned int contexts_count = 0;
	unsigned int function_count = 0;
	unsigned int max_contexts_per_function = 0;
	unsigned int count_reuses = 0;
	unsigned int max_reuses = 0;

	// We use FUNCTION_CONTEXTS_MAP instead of PROGRAM_CONTEXTS of
	// inter_procedural_analysis.hh so that the statistics are printed in
	// order of functions. This makes it easier to compare to files of
	// statistics.
	typename map<function_index, context_enums<LIVE_VALUE_TYPE, unlabeled_edges> >::iterator fi;
	for (fi = function_contexts.begin (); fi != function_contexts.end (); fi++)
	{
		struct cgraph_node * function = program.get_cgraph_node (fi->first);
		const char * function_name = cgraph_node_name (function);
		STATS ("\nFunction %s", function_name);
		struct function * function_decl = DECL_STRUCT_FUNCTION (function->decl);

		context_enums<LIVE_VALUE_TYPE, unlabeled_edges> contexts = fi->second;
		contexts_count += contexts.size ();
		function_count++;
		if (max_contexts_per_function < contexts.size ())
			max_contexts_per_function = contexts.size ();

		bool collected_context_indept = false;
		bool collected_function = false;

		unsigned int function_use_points = 0;
		basic_block block;
		FOR_EACH_BB_FN (block, function_decl)
		{
			program_blocks++;

			if (collected_function)
				continue;

			unsigned int block_id = block->index;
        		LIVE_VALUE_TYPE all_live_values;

			// Compute meet of all the contexts for this basic block

			typename context_enums<LIVE_VALUE_TYPE, unlabeled_edges>::iterator ci;
			for (ci = contexts.begin (); ci != contexts.end (); ci++)
			{
				context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context =
					ci->second;
				DEBUG ("\nbb=%d,context=%d", block->index, current_context->get_context_id ());

				///////////////////////////////////////////////////////////////////////////

				// In value
#if GREEDY_ALIAS_CLOSURE == 0
				// If greedy alias closure is not performed,
				// alias closure should be performed after the
				// analysis i.e., now.
				generate_alias_closure (current_context, block);
#endif
				copy_live_values (current_context, block, all_live_values);
	
				// DEBUG ("\nget_graph_statistics in");
				// get_access_paths (current_context, block, in_block_aps, tot_aps, false);
				// DEBUG ("\ndone get_graph_statistics program");

				////////////////////////////////////////////////////////////////////////////

				if (collected_context_indept)
					continue;

				////////////////////////////////////////////////////////////////////////////

	                        int curr_reuses = current_context->get_source_contexts ().size ();
       		                count_reuses += curr_reuses;
                        	if (max_reuses < curr_reuses)
                                	max_reuses = curr_reuses;
				STATS ("\n\tcontext=%d curr_reuses=%d", 
					current_context->get_context_id (), curr_reuses);

				///////////////////////////////////////////////////////////////////////////

				// Out value

				///////////////////////////////////////////////////////////////////////////
			}

			collected_context_indept = true;

			////////////////////////////////////////////////////////////////////////////

			// There is only one context for pta per function
			// (because at this point we have movp pta). Count once
			// since liveness is also counted once after taking
			// meet of all contexts at the block.
			ci = contexts.begin ();
			if (ci != contexts.end ())
			{
				context<LIVE_VALUE_TYPE, unlabeled_edges> * current_context = ci->second;
				if (current_context)
				{
					#if INFO_CONTAINER
					all_live_values.print_value (NULL);
					#endif
					get_pt_live_stats (current_context, block, all_live_values,
						tot_program_aps_count, tot_pta_aps_count, tot_valid_aps_count, 
						valid_percent_func_count, func_pta, valid_percent,
						pt_aps_locals, pt_aps_globals, valid_aps_locals, valid_aps_globals);

					// all_live_values.get_graph_stats (node_count, edge_count, use_sites_count, unique_use_sites);
				}
			}

			////////////////////////////////////////////////////////////////////////////

			collected_function = true;
		}
	}

	unsigned int tot_pta = 0;
	map<function_index, unsigned int>::iterator fpti;
	for (fpti = func_pta.begin (); fpti != func_pta.end (); fpti++)
	{
		tot_pta += fpti->second;
	}
	RESULT ("\ntot_pta=%d", tot_pta);
	unsigned int pta_percent_func_count[20] = {0};
	for (fpti = func_pta.begin (); fpti != func_pta.end (); fpti++)
	{
		unsigned int slot = (fpti->second / (float) tot_pta) * 20;
		if (slot == 20)
			slot = 19;
		pta_percent_func_count[slot]++;
	}
	
	/////////////////////////////////////////////////////////////////

	if (tot_pta_aps_count < tot_program_aps_count)
		RESULT ("\nTOTAL pta aps < live aps");
	STATS ("\nTotal live access paths = %d", tot_program_aps_count);
	STATS ("\nTotal pta access paths = %d", tot_pta_aps_count);
	STATS ("\nTotal valid live access paths = %d", tot_valid_aps_count);
	STATS ("\npt_local_aps=%d, pt_global_aps=%d, valid_local_aps=%d, valid_global_aps=%d",
		pt_aps_locals, pt_aps_globals, valid_aps_locals, valid_aps_globals);
	for (unsigned int i = 0; i < 20; i++)
		STATS ("\nFunc # with %d-%d percent pta aps = %d", 
			i*5 , (i+1)*5, pta_percent_func_count[i]);
	for (unsigned int i = 0; i < 20; i++)
		STATS ("\nFunc # with %d-%d percent valid live aps = %d", 
			i*5 , (i+1)*5, valid_percent_func_count[i]);
	STATS ("\nFunc # with no pta aps = %d", valid_percent_func_count[20]);
	STATS ("\nnode_count=%d, edge_count=%d, use_sites_count=%d, unique_use_sites_count=%d", 
		node_count, edge_count, use_sites_count, unique_use_sites.size ());
	STATS ("\nValid percent=%f", valid_percent / function_count);

	program.print_statistics ();

	INFO ("\n");
        STATS ("\nTotal program blocks=%d", program_blocks);
	STATS ("\nFunction count=%d", function_count);
        STATS ("\nTotal value contexts=%d", contexts_count);
	STATS ("\nAvg contexts per function=%f", (float) contexts_count / function_count);
	STATS ("\nMax contexts per function=%d", max_contexts_per_function);
        STATS ("\ncontext: count_reuses = %d, avg_reuses=%f, max_reuses=%d",
        	count_reuses, (float) count_reuses / contexts_count, max_reuses);

	FILE * stat_file = fopen (STAT_FILE, "a");

	fprintf (stat_file, "\nMAX_LEN_PRINT = %d", MAX_LEN_PRINT);
	fprintf (stat_file, "\nTotal live access paths = %d", tot_program_aps_count);
	fprintf (stat_file, "\nTotal pta access paths = %d", tot_pta_aps_count);
	fprintf (stat_file, "\nTotal valid live access paths = %d", tot_valid_aps_count);
	fprintf (stat_file, "\npt_local_aps=%d, pt_global_aps=%d, valid_local_aps=%d, valid_global_aps=%d",
		pt_aps_locals, pt_aps_globals, valid_aps_locals, valid_aps_globals);
	fprintf (stat_file, "\nValid percent=%f", valid_percent / function_count);
	for (unsigned int i = 0; i < 20; i++)
		fprintf (stat_file, "\nFunc # with %d-%d percent pta aps = %d", 
			i*5 , (i+1)*5, pta_percent_func_count[i]);
	for (unsigned int i = 0; i < 20; i++)
		fprintf (stat_file, "\nFunc # with %d-%d percent valid live aps = %d", 
			i*5, (i+1)*5, valid_percent_func_count[i]);
	fprintf (stat_file, "\nFunc # with no pta aps = %d", valid_percent_func_count[20]);
	fprintf (stat_file, "\nnode_count=%d, edge_count=%d, use_sites_count=%d, unique_use_sites_count=%d", 
		node_count, edge_count, use_sites_count, unique_use_sites.size ());

	fprintf (stat_file, "\nTotal program blocks=%d", program_blocks);
	fprintf (stat_file, "\nFunction count=%d", function_count);
        fprintf (stat_file, "\nTotal value contexts=%d", contexts_count);
	fprintf (stat_file, "\nAvg contexts per function=%f", (float) contexts_count / function_count);
	fprintf (stat_file, "\nMax contexts per function=%d", max_contexts_per_function);
        fprintf (stat_file, "\ncontext: count_reuses = %d, avg_reuses=%f, max_reuses=%d",
        	count_reuses, (float) count_reuses / contexts_count, max_reuses);

	fclose (stat_file);

	// ACCUMULATE CONTEXT-INDEPT values
	// Should we accumulate context-indept bypassed value to print it at
	// each program point? No not needed. Since we are printing only
	// lhs/rhs used/side-effected variables of a function, any accumulated
	// context-indept points-to pair will anyway not be printed.
}

// The client analysis can modify the control flow graph to use our 
// inter-procedural analysis, which assumes that each function call
// is the only statement in a basic block. Also, each pointer statement
// is made the only statement of a basic block for bi-directional 
// inter-procedural analysis.

template <class LIVE_VALUE_TYPE, class LIVE_VALUE_SUBTYPE>
void liveness_analysis<LIVE_VALUE_TYPE, LIVE_VALUE_SUBTYPE>::
preprocess_and_parse_program ()
{
	// If a pre-analysis has already set main, do not reinitialize.
	if (!program.main_cnode)
	{
		program.initialization ();
		program.preprocess_control_flow_graph ();
	}
#if SKIP_EMPTY_CFG
        program.is_cfg_ptr_asgn_empty ();
#endif
	set_blocks_order ();

//	inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE> * dept_analysis 
//		= get_dependent_analysis ();
//	set<function_index> recursive_fns;
//	dept_analysis->find_recursive_functions (recursive_fns);
//	program.get_loop_use_sites (recursive_fns);

#if DEBUG_CONTAINER
	program.print_parsed_data ();
	// program.print_variable_data ();
	// program.print_assignment_data ();
#endif
}

template class liveness_analysis<deterministic_graph, deterministic_node>;
template class liveness_analysis<non_deterministic_graph, non_deterministic_node>;

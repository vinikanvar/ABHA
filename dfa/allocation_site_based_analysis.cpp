
/************************
 * @author Vini Kanvar
************************/

#include "allocation_site_based_analysis.hh"
#include "langhooks.h"

#define LIVENESS_BASED 1

#define DEBUG_CONTAINER 0
//#define RESULT_CONTAINER 1
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

unaffected_pta::
unaffected_pta ()
{
	DEBUG ("\nalloc unaffected_pta=%x", this);
	NEW_ADDR ("\nnew unaffected_pta %x", this);
}

unaffected_pta::
~unaffected_pta ()
{
	DEBUG ("\ndealloc unaffected_pta=%x", this);
	GC_ADDR ("\ngc unaffected_pta %x", this);
}

template <class LIVE_VALUE_TYPE>
allocation_site_based_analysis<LIVE_VALUE_TYPE>::
allocation_site_based_analysis (bool is_val_context):
	forward_inter_procedural_analysis<unlabeled_edges, LIVE_VALUE_TYPE> (is_val_context)
{
	tot_stmttouch = 0;
	tot_update_points = 0;
}

template <class LIVE_VALUE_TYPE>
allocation_site_based_analysis<LIVE_VALUE_TYPE>::
~allocation_site_based_analysis ()
{
	DEBUG ("\ngc allocation_site_based_analysis");
	delete_context_aux_info ();
}

/** 
 * @returns the top data flow value of the lattice.  This is the default data
 * flow value.
 */

template <class LIVE_VALUE_TYPE>
unlabeled_edges * allocation_site_based_analysis<LIVE_VALUE_TYPE>::
initial_value ()
{
	DEBUG ("\ninitial_value()");
	return new unlabeled_edges;
}

/**
 * Initialize all globals with null_id. But since we are not saving null_id
 * pointees, the boundary value is empty.
 */

template <class LIVE_VALUE_TYPE>
unlabeled_edges * allocation_site_based_analysis<LIVE_VALUE_TYPE>::
boundary_value ()
{
	DEBUG ("\nboundary_value()");
	unlabeled_edges * boundary = new unlabeled_edges ();

	// FIXME: Eliminate non-pointers.
#if UNDEF_LOCATION
	set<label> global_vars = program.get_global_heap_variables ();
	set<label> undef;
	undef.insert (undef_id);

	boundary->gen (global_vars, undef);
#endif
	return boundary;
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
initialize_locals (unlabeled_edges & start_value_copy,
        context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context)
{
#if UNDEF_LOCATION
        struct cgraph_node * curr_function = current_context.get_function ();
	// Do not add parameters as parameters are already initialized.
	// FIXME: Eliminate non-pointers.
        set<label> local_variables = program.get_local_variables (curr_function);
        DEBUG ("\ngot live locals");
	set<label> undef;
	undef.insert (undef_id);

        start_value_copy.gen (local_variables, undef);
#endif
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
process_in_value (context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context, basic_block current_block)
{
}

/** Retrieves a value context at the called function if it exists, and returns the value
 *  after evaluation through the called function.
 *  If the value context does not exist at the called function, this function creates one,
 *  adds it to the set of contexts at the called function, and returns the TOP value (as 
 *  the evaluated value of the new created context, since this has not yet been evaluated).
 */

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
process_call_statement (context<unlabeled_edges, LIVE_VALUE_TYPE> * src_context, basic_block call_site)
{
	DEBUG ("\nprocess_call_stmt()");

        if (!src_context)
	{
		RESULT ("\nError: Current context is NULL\n");
		return;
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
	DEBUG ("\ndest_functions fetched");
	if (!dest_functions.size ())
	{
		RESULT ("\nError: Cannot find called/destination function");
		// src_context->set_out_value (call_site, initial_value ());
		return;
	}
	DEBUG ("\nnon empty dest_functions");

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

#if SKIP_EMPTY_CFG
		if (program.is_cfg_ptr_asgn_empty (dest_function))
		{
			// We need to set IN so that the adjacent blocks get added
			copy_in_to_out (src_context, call_site);
			continue;
		}
#endif

		// If destination of dependent context does not exist, then do
		// not proceed.
		if (!is_dest_of_dept_context_exist (src_context, call_site, dest_function))
		{
			RESULT ("\nError: dept context of called function does not exist");
			// src_context->set_out_value (call_site, initial_value ());
			continue;
		}

		// Every called function (via function pointer) has different
		// function parameters. Therefore, a different copy of
		// calling_value should be passed.

		unlabeled_edges * in_value = src_context->get_in_value (call_site);
		if (!in_value)
		{
			RESULT ("\nError: in_value is NULL");
		}

		// IS_LOOP_MERGE = FALSE
		DEBUG ("\nin_value->copy_value()");
		unlabeled_edges in_value_copy;
		in_value_copy.copy_value (*in_value, false);
#if DEBUG_CONTAINER
		DEBUG ("\nin_value_copy of function call (before function parameter mapping)");
		in_value_copy.print_value (NULL);
#endif

		// Map actual parameters to formal parameters
		// process_parsed_data called by this function restores
		// unaffected context_dept pta.
		process_function_arguments (src_context, call_site, &in_value_copy, dest_function);

#if DEBUG_CONTAINER
		DEBUG ("\ncalling_value + argument_mapping of function %s",
			cgraph_node_name (dest_function));
		in_value_copy.print_value (NULL);
#endif

		// Add memoized pta graph
		restore_unaffected_context_dept_pta (*src_context, in_value_copy);

#if DEBUG_CONTAINER
		DEBUG ("\nin_value_copy after restore_unaffected_context_dept_pta");
		in_value_copy.print_value (NULL);
#endif

		// Propagate part of the value which is reachable from the parameters
		// of the function and global variables.  The
		// parameter-and-global-var-unreachable part is left with IN_VALUE_COPY
		// and the parameter-and-global-var-reachable part is returned. 
		// FIXME: Extract pointers reachable variables which are live in the
		// called function rather than those that are reachable from
		// parameters.

		// Extract par_glob_reachable value from in_value_copy and not out_value_copy. 
		// Extract par_glob reachable and not arg_glob reachable. Eg.
		// func(int *x) called with func(&y); then only y reachable
		// will be passed and "x points to y" will be wrongly bypassed.
		// Alternative: extract arg_glob then map_function_args.
		unlabeled_edges * par_glob_reachable_value =
			extract_par_glob_reachable_value (dest_function, in_value_copy);
		unlabeled_edges * calling_value = par_glob_reachable_value;
#if INTERMEDIATE_RESULT
		RESULT ("\nin_value_copy left with par_glob-unreachable nodes");
		in_value_copy.print_value (NULL);
		RESULT ("\ncalling_value function %s", cgraph_node_name (dest_function));
		calling_value->print_value (NULL);
#endif

		// Process called context
		unlabeled_edges * function_out_value =
			process_destination_context (*src_context, call_site, dest_function, calling_value);

		DEBUG ("\nprocess_destination_context done");

		// Save only this bypassed value in the called context. For
		// accumulation of bypassed values of all previous transitive
		// calls, we perform fixed point computation using
		// ipa::analyze_context_info_worklist().
		save_context_indept_pta (*src_context, call_site, dest_function, in_value_copy);
		DEBUG ("\nsave_context_indept_pta done");

		if (!function_out_value)
			continue;

		initialize_out_value (src_context, call_site);

		// Restore par_glob_unreachable value only if function returns.
		// If function does not return (e.g. it has exit(0)), then do
		// not restore.

		// Rohan Padhye: IN = OUT_pred U IN. Take self-meet to ensure monotonic results. 
		// IS_LOOP_MERGE = FALSE
		// Copy par_glob_unreachable value to out_value.
		DEBUG ("\nCopying par_glob-unreachable value to out");
		// IS_LOOP_MERGE = FALSE
		DEBUG ("\nin_value->copy_value() to out_value");
		unlabeled_edges * out_value = src_context->get_out_value (call_site);
		out_value->copy_value (in_value_copy, false);
		DEBUG ("\nin_value_copy done");

		// Create a copy of FUNCTION_OUT_VALUE to OUT of call-site. OUT
		// of the call-site contains par_glob-unreachable nodes. The
		// par_glob-reachable nodes are in FUNCTION_OUT_VALUE.
		// Therefore, FUNCTION_OUT_VALUE should be appended to the OUT
		// of the call-site.
		// IS_LOOP_MERGE = FALSE

		DEBUG ("\nfunction_out_value->copy_value() to out_value");
		out_value->copy_value (*function_out_value, false);
		DEBUG ("\nfunction_out_value copy done");
		
		// Add memoized pta graph of called context
		restore_unaffected_context_dept_pta (*src_context, call_site, dest_function, *out_value);
		DEBUG ("\nrestore_unaffected_context_dept_pta done");

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
		out_value->print_value (NULL);
		// unlabeled_edges * out_value_pointer = src_context->get_out_value (call_site);
		// DEBUG ("\nout_value from out of call_site %d", call_site->index);
		// out_value_pointer->print_value (NULL);
#endif

		// Delete local variables in OUT_VALUE under the condition that
		// the SRC_CONTEXT has never been called by a context of
		// DEST_FUNCTION.
		// FIXME: Delete all variables whose address does not escape.
		// Delete all locals if SRC_CONTEXT has never been called by a
		// context of DEST_FUNCTION.
		// check_and_delete_local_variables (*src_context, dest_function, *out_value, NULL);

		// It is possible that src_context is not in recursion in
		// ALLOC_BASED but it is in recursion in ACCESS_BASED.
		// (This happens in libquantum: in ALLOC_BASED, quantum_toffoli
		// calls quantum_qec_counter.constprop.3 (context 148) but
		// quantum_cnot_ft recursively calls
		// quantum_qec_counter.constprop.3 (context 134) and not
		// context 148. In ACCESS_BASED, quantum_toffoli and
		// quantum_cnot_ft both call quantum_qec_counter.constprop.3
		// (context 69) and quantum_cnot_ft is recursive call.)
		// Then locals are deleted in ALLOC_BASED but not in
		// ACCESS_BASED.
		// Fix: Delete all locals if a context of SRC_FUNCTION has
		// never been called by a context of DEST_FUNCTION.

		// Locals of caller should not be deleted
		check_and_delete_local_variables (*src_context, dest_function, *out_value, NULL);
		// #if ALLOC_EFFICIENT == 0
		// check_and_delete_local_variables (src_context->get_function (), dest_function, *out_value, NULL);
		// #endif
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
	unlabeled_edges * out_value = src_context->get_out_value (call_site);
	out_value = src_context->get_out_value (call_site);


	// Propagate only function_par_defs and callees_global_defs
	if (out_value)
		remove_unaffected_context_dept_pta (*src_context, *out_value);


#if DEBUG_CONTAINER
	DEBUG ("\nValue before deleting dead pointers");
	if (out_value)
		out_value->print_value (NULL);
#endif

#if LIVENESS_BASED
	if (out_value)
		get_live_data (*out_value, *src_context, call_site);
#endif
	if (out_value)
		out_value->clean ();
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
initialize_out_value (context<unlabeled_edges, LIVE_VALUE_TYPE> * src_context, basic_block call_site)
{
	unlabeled_edges * out_value = src_context->get_out_value (call_site);
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
		DEBUG ("\nout_value->copy_value()");
		unlabeled_edges * out_value_copy = out_value->copy_value (false);
		out_value = out_value_copy;
	}
	src_context->set_out_value (call_site, out_value);
	
#if DEBUG_CONTAINER
	DEBUG ("\nValue at out of call-site");
	out_value->print_value (NULL);
#endif
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

template <class LIVE_VALUE_TYPE>
bool allocation_site_based_analysis<LIVE_VALUE_TYPE>::
process_parsed_data (context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context, 
	basic_block current_block, 
	unlabeled_edges * calling_value, 
	bool to_kill)
{
	DEBUG ("\nprocess_parsed_data");
	DEBUG ("\nto_kill=%d", to_kill);

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

	// Initialize all locals to UNDEF.
	// START block is empty.
	if (block_type & START_BLOCK)
	{
		DEBUG ("\nSTART_BLOCK");
		if (first_stmt (current_block))
		{
		         RESULT ("\nError: start block is not empty");
		         return false;
		}
		DEBUG ("\nNo statement found in START_BLOCK");
		bool is_out_initialized = true;

		unlabeled_edges * in_value = current_context->get_in_value (current_block);
		unlabeled_edges in_value_copy;

#if BYPASSING_UNAFFECTED
		in_value_copy.copy_value (*in_value, false);
		unlabeled_edges * changing_context_dept_pta = 
			extract_changing_context_dept_pta (*current_context, in_value_copy);
		current_context->set_out_value (current_block, changing_context_dept_pta);
		// copy_in_to_out (current_context, current_block);
		initialize_locals (*changing_context_dept_pta, *current_context);
#else
		copy_in_to_out (current_context, current_block);
#endif

		// IN_VALUE_COPY contains the unaffected part 
		copy_unaffected_context_dept_aux (in_value_copy, *current_context, true);
		RESULT ("\nunaffected_context_dept=");
		in_value_copy.print_value (NULL);

		

		return is_out_initialized;
	}

	// The OUT of CALL blocks is initialized in process_call_statement().
	// Initialize other blocks here.
	// if (block_type & END_BLOCK)
	//	current_context->set_out_value (current_block, initial_value ());
	if (!(block_type & CALL_BLOCK))
		copy_in_to_out (current_context, current_block);

	// We initialize OUT of all blocks even if OUT is only same as IN.
	bool is_out_initialized = true;

	unlabeled_edges * value;
	if ((block_type & CALL_BLOCK) && (value = calling_value));
	else
		value = current_context->get_out_value (current_block);


	// Add memoized pta graph
	restore_unaffected_context_dept_pta (*current_context, *value);


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
			process_assignment_statement (*value, current_context, current_block, index, to_kill);
		}
		else
		{
#if DEBUG_CONTAINER
			program.print_variable_data (index);
#endif
			DEBUG ("\nNo need to process use statements for points-to analysis");
		}
	}

	// If this is a call-block, then we do nothing more i.e. we keep VALUE
	// restricted to Lin only (instead of Lout) (which it already was).
	// This is because these values (even though dead in Lout i.e. after
	// the function call) might be reachable from actual parameter in the
	// called function. 
	// FIXME: We have retained variables which are reachable and which
	// reach the actual parameter. However, we need to retain only the
	// former; we can delete the latter if dead in Lout.
	if (block_type & CALL_BLOCK)
	{
		// Propagate only function_par_defs and callees_global_defs
		remove_unaffected_context_dept_pta (*current_context, *value);

		return is_out_initialized;
	}

	// If this is not a call-block.
	// Restrict OUT value to liveness only after computing all the
	// points-to values of the whole block. Otherwise problem: for example,
	// x=&y;z=x; block with only z live at out. If we perform
	// liveness-restriction after every points-to computation, then x=&y
	// will get deleted before z=x is processed. Therefore, z=&y will not
	// get derived.

#if LIVENESS_BASED
	// Restrict OUT value to liveness only after computing all the
	// points-to values of the whole block. Otherwise problem: for example,
	// x=&y;z=x; block with only z live at out. If we perform
	// liveness-restriction after every points-to computation, then x=&y
	// will get deleted before z=x is processed. Therefore, z=&y will not
	// get derived.

	get_live_data (*value, *current_context, current_block);
#endif

	value->clean ();

	// Propagate only function_par_defs and callees_global_defs
	remove_unaffected_context_dept_pta (*current_context, *value);


	// Reuse: Delete a graph if it repeats at the successor program point.
	unlabeled_edges * value_in = current_context->get_in_value (current_block);
	unlabeled_edges * value_out = current_context->get_out_value (current_block);
	if (value_out->is_value_same (*value_in))
	{
		current_context->set_out_value (current_block, value_in);
	}

	return is_out_initialized;
}

template <class LIVE_VALUE_TYPE>
bool allocation_site_based_analysis<LIVE_VALUE_TYPE>::
process_assignment_statement (unlabeled_edges & value,
	context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context,
	basic_block current_block,
	unsigned int assignment_data_index,
	bool to_kill)
{
	DEBUG ("\nprocess_assignment_statement");
	DEBUG ("\nto_kill=%d", to_kill);

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
	      return true;

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

#if DEBUG_CONTAINER
	DEBUG ("\npt_vars value");
	value.print_value (NULL);
#endif

	set<label> must_lhs_vars;
	set<label> may_lhs_vars;
	set<label> rhs_vars;

//	if (lhs.pointer_arithmetic || rhs.pointer_arithmetic)
//		return;
	// Assume all pointer arithmetic happen only on arrays. Ignoring
	// pointer arithmeitc on fields of structures.
	if (lhs.pointer_arithmetic)
		lhs.offset = 0;
	if (rhs.pointer_arithmetic)
		rhs.offset = 0;

	get_rhs_vars (value, rhs, rhs_vars);
	get_lhs_vars (value, lhs, may_lhs_vars, must_lhs_vars);

#if DEBUG_CONTAINER
	set<label>::iterator pi;
	DEBUG ("\nMay LHS:");
	for (pi = may_lhs_vars.begin (); pi != may_lhs_vars.end (); pi++)
		DEBUG ("%d,", *pi);
	DEBUG ("\nLHS-offset=%d", lhs.offset);
	DEBUG ("\nRHS:");
	for (pi = rhs_vars.begin (); pi != rhs_vars.end (); pi++)
		DEBUG ("%d,", *pi);
	if (must_lhs_vars.size ())
		DEBUG ("\nmust LHS %d:", lhs.var);
	for (pi = must_lhs_vars.begin (); pi != must_lhs_vars.end (); pi++)
		DEBUG ("%d,", *pi);
#endif

	if (!to_kill)
	{
		DEBUG ("\nto_kill=%d -- no killing", to_kill);
		must_lhs_vars.clear ();
	}

#if DEBUG_CONTAINER
	DEBUG ("\nValue before gen,kill");
	value.print_value (NULL);
#endif

	value.kill (must_lhs_vars);

#if DEBUG_CONTAINER
	DEBUG ("\nValue after kill");
	value.print_value (NULL);
#endif

	value.gen (may_lhs_vars, rhs_vars);

#if ALLOC_STATISTICS_CONTAINER
	tot_update_points++;
	// r-value of right hand side
	tot_stmttouch += rhs_vars.size ();

	// Old pointees of l-value of left hand side
	set<label>::iterator lti;
	for (lti = must_lhs_vars.begin (); lti != must_lhs_vars.end (); lti++)
	{
		label v = *lti;
		if (value.out_edge_list.find (v) == value.out_edge_list.end ())
			continue;
		tot_stmttouch += value.out_edge_list[v].size ();
	}
#endif

	return true;
}

/**
 * This function gets the rhs vars for the variable RHS in RHS_NODES.
 */

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_rhs_vars (unlabeled_edges & value,
        constraint_expr & rhs,
        set<label> & rhs_vars)
{
	DEBUG ("\nget_rhs_vars()");
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
		// Ignore ...=&(rhs->f) case since (for efficiency), in
		// dfa/points_to_analysis_fi, we are not explicating
		// non-pointer fields, which means fields are not addressable.
		if (rhs.offset)
		{
			csvarinfo_t rinfo = program.cs_get_varinfo (rhs.var);
			RESULT ("\nIGNORE &(rhs=%s(%d)->f=%d)", rinfo->name, rinfo->id, 
				rhs.offset);
			break;
		}
#endif
		// Will get undef node if it is required
		value.get_pointer_vars (rhs.var, rhs.offset, rhs_vars);
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

		if (program.is_proper_var (rhs.var))
			rhs_vars.insert (rhs.var);

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

		value.get_deref_vars (rhs.var, rhs.offset, rhs_vars);

		break;
	}

	default:
		RESULT ("\nError: rhs.type cannot hold a fourth type");
		break;
	}
}

/**
 * This function populates lhs vars for the variable LHS in MAY_LHS_NODES and
 * MUST_LHS_NODES, and gets any required vars provided IS_RHS_NON_EMPTY
 * is true.
 */

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_lhs_vars (unlabeled_edges & value,
	constraint_expr & lhs,
	set<label> & may_lhs_vars,
	set<label> & must_lhs_vars)
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

		if (!program.is_array (lhs.var) && !program.is_union (lhs.var))
			must_lhs_vars.insert (lhs.var);
		may_lhs_vars.insert (lhs.var);

		break;
	}

	// lhs->f=... or *lhs=...
	case DEREF:
	{
		DEBUG ("\nlhs.type == DEREF");

#if STRONG_UPDATES
		value.get_must_pointer_vars (lhs.var, lhs.offset, must_lhs_vars);
#endif
		DEBUG ("\nFor lhs->f=... rhs_vars is non-empty");

		value.get_pointer_vars (lhs.var, lhs.offset, may_lhs_vars);

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

/**
 * Add to assignment_data of the CALL_SITE, mappings of actual parameters to
 * formal parameters of CALLED_FUNCTION. Then process them and delete the
 * mappings if the CALL_SITE is a function pointer call.
 */

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
process_function_arguments (context<unlabeled_edges, LIVE_VALUE_TYPE> * src_context,
        basic_block call_site,
        unlabeled_edges * value,
        struct cgraph_node * called_function)
{
        DEBUG ("\nprocess_function_arguments()");

        if (!value)
        {
                RESULT ("\nError: Null value");
                return;
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

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
process_return_value (context<unlabeled_edges, LIVE_VALUE_TYPE> * src_context,
        basic_block call_site,
        unlabeled_edges * value,
        struct cgraph_node * called_function,
	bool to_kill)
{
        DEBUG ("\nprocess_return_values()");

        if (!value)
        {
                DEBUG ("\nNUll value");
                return;
        }

#if DEBUG_CONTAINER
	const char * function_name = cgraph_node_name (called_function);
        DEBUG ("\nParsed data of bb=%d (function=%s) BEFORE adding return values", 
		call_site->index, function_name);
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
        DEBUG ("\nParsed data of bb=%d (function=%s) AFTER adding return values", 
		call_site->index, function_name);
        program.print_parsed_data (call_site);
#endif

        // Erase the mappings
        ((block_information *)(call_site->aux))->erase_assignment_indices ();
}

template <class LIVE_VALUE_TYPE>
set<struct cgraph_node *> allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_called_functions (context<unlabeled_edges, LIVE_VALUE_TYPE> & src_context, 
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
		
	unlabeled_edges * in_value = src_context.get_in_value (call_site);
	if (!in_value)
	{
		RESULT ("\nError: Function pointer cant be found, IN value is NULL");
		set<struct cgraph_node *> empty;
		return empty;
	}
	// Add memoized pta graph of called context
	restore_unaffected_context_dept_pta (src_context, *in_value);
	set<label> called_function_ids;
	in_value->get_destination_vars (fp_info->id, called_function_ids);

#if INTERMEDIATE_RESULT
	RESULT ("\nFunction pointees: ");
#endif
	set<struct cgraph_node *> called_functions;
	set<label>::iterator fi;
	for (fi = called_function_ids.begin (); fi != called_function_ids.end (); fi++)
	{
		DEBUG ("\nPrinting called_functions");
		csvarinfo_t called_function_info = VEC_index (csvarinfo_t, program.variable_data, *fi);
		if (!called_function_info)
		{
			RESULT ("\nError: Function pointer is not pointing to function");
			continue;
		}
		DEBUG ("\nFunction var=%s(%d)", called_function_info->name, called_function_info->id);
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

	// Propagate only function_par_defs and callees_global_defs
	remove_unaffected_context_dept_pta (src_context, *in_value);

	return called_functions;
}
	
/** 
 * Extracts the part of the value which is reachable from any function parameter
 * or a global variable. We should not extract argument reachable variables,
 * but parameter reachable variables since argument has no role to play in the
 * called function unless it is accessible from the parameter, in which case
 * parameter reachable variables will still suffice. Also it is wrong. Eg.
 * func(int *x) called with func(&y); then only y reachable will be passed and
 * "x points to y" will be wrongly bypassed.
 */

template <class LIVE_VALUE_TYPE>
unlabeled_edges * allocation_site_based_analysis<LIVE_VALUE_TYPE>::
extract_par_glob_reachable_value (struct cgraph_node * dest_function, 
	unlabeled_edges & value_in)
{
//	unlabeled_edges * par_glob_reachable_value = boundary_value ();

#if (BYPASSING_UNUSED == 0 && BYPASSING_UNREACHABLE == 0)
	unlabeled_edges * par_glob_reachable_value_full = value_in.copy_value (false);
	value_in.erase ();
	return par_glob_reachable_value_full;
#endif

        set<unsigned int> par_glob_vars;

#if BYPASSING_UNREACHABLE
	set<unsigned int> glob_heap_vars = program.get_global_variables ();
	par_glob_vars.insert (glob_heap_vars.begin (), glob_heap_vars.end ());
#endif

        DEBUG ("\nextract_par_glob_reachable_value ()");

        set<unsigned int> function_parameters =
                program.get_function_parameters (dest_function);
        par_glob_vars.insert (function_parameters.begin (), function_parameters.end ());

        // FIXME: Exclude function names, otherwise local function pointers are
        // unnecessarily propagated since they point to global variables (i.e.
        // function names). There propagation is unnecessary because there is
        // no precision gain of replicating function name nodes.
        // FIXME: Exclude local function pointers. They do not get excluded
        // since their pointees (i.e. function names) are global variables.
        // set<unsigned int> global_vars = program.get_global_variables ();
        // par_glob_vars.insert (global_vars.begin (), global_vars.end ());

	// Note: In access based analysis we have included only global
	// variables and not heap variables. This is because the effect on
	// precision will be the same. In allocation site based analysis, we
	// have spuriously included both global and heap variables because
	// otherwise precision improvement on bzip2 is less.
	// Used for liveness_analysis_deterministic/non_deterministic
	// #if ALLOC_EFFICIENT == 0
	// Used for comparison with ACCESS_BASED
        // set<unsigned int> global_vars = program.get_global_heap_variables ();
	// #endif
        // par_glob_vars.insert (global_vars.begin (), global_vars.end ());

	// Pass callees_global_defs and vars reachable from callees_global_uses.

	set<unsigned int> * callees_global_defs = 
		function_side_effects.get_callees_global_defs (dest_function);
	set<unsigned int> * callees_global_uses = 
		function_side_effects.get_callees_global_uses (dest_function);
	if (callees_global_uses)
		par_glob_vars.insert (callees_global_uses->begin (), callees_global_uses->end ());

#if DEBUG_CONTAINER
        set<unsigned int>::iterator vi;
        DEBUG ("\nGlobals + function parameters of function:");
        for (vi = par_glob_vars.begin (); vi != par_glob_vars.end (); vi++)
                DEBUG ("%d, ", *vi);
#endif

	// Extract vars reachable from pars and callees_global_uses.

	// Do not extract vars reachable from callees_global_defs, just immediate pointees.

	if (!callees_global_defs)
	{
		set<variable_id> vars;
		callees_global_defs = &vars;
	}
        unlabeled_edges * par_glob_reachable_value = 
		value_in.extract_value (par_glob_vars, *callees_global_defs);

#if DEBUG_CONTAINER
        DEBUG ("\nvalue left with par_glob-unreachable vars");
        value_in.print_value (NULL);
        DEBUG ("\nExtracted graph with par_glob-unreachable vars");
        par_glob_reachable_value->print_value (NULL);
#endif

        return par_glob_reachable_value;
}

template <class LIVE_VALUE_TYPE>
unlabeled_edges * allocation_site_based_analysis<LIVE_VALUE_TYPE>::
extract_changing_context_dept_pta (context<unlabeled_edges, LIVE_VALUE_TYPE> & curr_context,
	unlabeled_edges & context_dept_pta)
{
	set<variable_id> callees_glob_par_defs;
	get_callees_glob_par_defs (curr_context, callees_glob_par_defs);

	unlabeled_edges * glob_par_edges = new unlabeled_edges;
	context_dept_pta.extract_destination_edges (callees_glob_par_defs, *glob_par_edges);
	return glob_par_edges;
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
remove_unaffected_context_dept_pta (context<unlabeled_edges, LIVE_VALUE_TYPE> & curr_context,
	unlabeled_edges & context_dept_pta)
{
	// If we remove all destination edges of callees_glob_par_defs at this
	// program point, we will end up removing even those edges that have
	// been newly generated at this program point, and are not valid at
	// program points before it. 
	// set<variable_id> * callees_glob_par_defs = get_callees_glob_par_defs (curr_context);
	// if (!callees_glob_par_defs)
	// {
	//	RESULT ("\nError: callees_glob_par_defs NULL");
	//	return;
	// }
	// context_dept_pta.remove_destination_edges (*callees_glob_par_defs);

	// Remove only those destination edges that were removed at START of
	// the context -- saved in aux_info->context_dept.
	unaffected_pta * aux = (unaffected_pta *) curr_context.get_aux_info ();
	if (!aux)
	{
		RESULT ("\nError: aux (unaffected context_dept value) is NULL");
		return;
	}
	unlabeled_edges * unaffected_context_dept_pta = &aux->context_dept;
	unaffected_context_dept_pta->kill_out_edges (context_dept_pta);
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
restore_unaffected_context_dept_pta (context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context,
	unlabeled_edges & value)
{
	unaffected_pta * aux = (unaffected_pta *) current_context.get_aux_info ();
	if (!aux)
	{
		RESULT ("\nError: aux (unaffected context_dept value) is NULL");
		return;
	}
	unlabeled_edges * unaffected_context_dept_pta = &aux->context_dept;
#if BYPASSING_UNAFFECTED == 0
	if (unaffected_context_dept_pta->out_edge_list.size ())
		RESULT ("\nError: unaffected_context_dept_pta is being used");
#endif
	value.copy_value (*unaffected_context_dept_pta, false);
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
restore_unaffected_context_dept_pta (context<unlabeled_edges, LIVE_VALUE_TYPE> & src_context,
	basic_block call_site,
	struct cgraph_node * dest_function,
	unlabeled_edges & value)
{
	context<unlabeled_edges, LIVE_VALUE_TYPE> * dest_context = 
		src_context.get_destination_context (call_site, dest_function);
	if (!dest_context)
	{
		RESULT ("\nError: dest context of src-context=%d, function=%s not created",
			src_context.get_context_id (), cgraph_node_name (dest_function));
		return;
	}

	unaffected_pta * aux = (unaffected_pta *) dest_context->get_aux_info ();
	if (!aux)
	{
		RESULT ("\nError: aux (unaffected context_dept value) of dest_context is NULL");
		return;
	}
	unlabeled_edges * unaffected_context_dept_pta = &aux->context_dept;
	value.copy_value (*unaffected_context_dept_pta, false);
}

template <class LIVE_VALUE_TYPE>
LIVE_VALUE_TYPE * allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_dept_function_in_value (struct cgraph_node * func)
{
	// This function works when there is one context per function in the dept analysis

	inter_procedural_analysis<LIVE_VALUE_TYPE, unlabeled_edges> * dept_analysis = get_dependent_analysis ();
	if (!dept_analysis)
	{
		RESULT ("\nError: dept_analysis not found");
		return NULL;
	}

	context<LIVE_VALUE_TYPE, unlabeled_edges> * existing_dest_context = 
		dept_analysis->get_function_context (func);
	if (!existing_dest_context)
	{
		RESULT ("\nError: destination context not found");
		return NULL;
	}

	// Get the value at the START block of EXISTING_DEST_CONTEXT.
	basic_block start_block = existing_dest_context->get_start_block ();
	if (!start_block)
		RESULT ("\nError: start_block is null");

	LIVE_VALUE_TYPE * function_in_value = existing_dest_context->get_in_value (start_block);
	return function_in_value;
}

/** 
 * Since points-to analysis is a forwards analysis, we want to delete both the
 * local and formal parameters, since neither of them will be used by the
 * calling function.
 */

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
delete_local_variables (struct cgraph_node * src_function, struct cgraph_node * function, unlabeled_edges & out_value, void * info)
{
	// FIXME: THIS context is not being called by a context of FUNCTION.
	// Instead of deleting locals of only FUNCTION, can we delete all
	// locals (even those other than FUNCTION) -- perhaps after checking
	// that there is no context of other that other function calling this
	// context..

	set<label> local_variables;
	program.get_local_variables (function, local_variables);
	program.get_function_parameters (function, local_variables);

#if DEBUG_CONTAINER
	set<label>::iterator vi;
	DEBUG ("\nLocal+parameter variables: ");
	for (vi = local_variables.begin (); vi != local_variables.end (); vi++)
		DEBUG ("%d, ", *vi);
#endif

	// kill local_variables in pointers
	out_value.kill (local_variables);

	// kill local_variables in pointees
	out_value.kill_pointees (local_variables);
}

/**
 * This function fetches dead variables from Lout of the CURRENT_BLOCK. Using
 * this set, it returns the pointer variables in VALUE which are dead. 
 */

template <>
set<unsigned int> allocation_site_based_analysis<variables>::
get_dead_variables (unlabeled_edges & value,
        context<unlabeled_edges, variables> & current_context,
        basic_block current_block)
{
        DEBUG ("\nget_dead_variables()");
        variables * out_liveness = get_live_out_value (current_context, current_block);

        struct cgraph_node * function = current_context.get_function ();
	// set<variable_id>
        set<unsigned int> all_variables;
	program.get_local_variables (function, all_variables);

        set<unsigned int> dead_variables;
        if (out_liveness)
                dead_variables = out_liveness->get_dead_variables (all_variables);
        else
                dead_variables = all_variables;

#if ALLOC_STATISTICS_CONTAINER
	if (out_liveness)
	{
		dead_locals_stats.live_locals_pp.insert (out_liveness->live_vars.begin (), out_liveness->live_vars.end ());
		dead_locals_stats.tot_live_locals_pp += out_liveness->live_vars.size ();
	}
	dead_locals_stats.dead_locals_pp.insert (dead_variables.begin (), dead_variables.end ());
	dead_locals_stats.tot_dead_locals_pp += dead_variables.size ();
#endif

        return dead_variables;
}

template <>
void allocation_site_based_analysis<variables>::
get_live_data (unlabeled_edges & out_value,
        context<unlabeled_edges, variables> & current_context,
        basic_block current_block)
{
        DEBUG ("\nget_live_data");
	// The return variable is live at IN of return block and dead at IN and OUT of
	// END_BLOCK. We do not want to kill it at IN of END_BLOCK because
	// otherwise the caller function will get called context's value
	// without the return variable (because context's value is picked from
	// IN of END_BLOCK). We do not want to kill it at OUT of END_BLOCK
	// because whether or not is_value_same is true depends on OUT value. 

	unsigned int bt = ((block_information *)(current_block->aux))->get_block_type ();
        if (program.is_pred_of_end_block (current_block) || (bt & END_BLOCK))
		return;

	// This returns only dead locals 
        set<label> dead_variables = 
		get_dead_variables (out_value, current_context, current_block);
#if INTERMEDIATE_RESULT
	set<label>::iterator vi;
	if (dead_variables.size ())
		RESULT ("\nDead vars=");
	for (vi = dead_variables.begin (); vi != dead_variables.end (); vi++)
	{
		csvarinfo_t var = program.cs_get_varinfo (*vi);
		RESULT ("%s(%d),", var->name, *vi);
	}
#endif

#if ALLOC_STATISTICS_CONTAINER
	out_value.count_dead_vars (dead_variables);
#endif

	out_value.kill (dead_variables);
}

/**
 * This function maps points-to nodes with live nodes. It maps each points-to
 * node rho.f.* to live path rho.f.*, where f is a field. It marks each such
 * points-to node as live_pts_node and also marks the corresponding rho.f also
 * as live_pts_node.
 */

template <>
void allocation_site_based_analysis<deterministic_graph>::
sync_pts_live_value (label pts_node,
	deterministic_node & live_node,
	unlabeled_edges & pts_value, 
	deterministic_graph & live_value,
	map<label, set<deterministic_node *> > & sync_pts_live_nodes,
	set<label> & live_pts_nodes)
{
        DEBUG ("\nsync_pts_live_value (pts=%d,live=%d)", pts_node, live_node.get_node_id ());
    
        if (sync_pts_live_nodes[pts_node].find (&live_node) != sync_pts_live_nodes[pts_node].end ())
                return;

        sync_pts_live_nodes[pts_node].insert (&live_node);
	// Mark rho.L.* as live
	live_pts_nodes.insert (pts_node);

        set<label> out_edge_labels;
        live_node.get_out_edge_labels (out_edge_labels);
        set<label>::iterator li;
        for (li = out_edge_labels.begin (); li != out_edge_labels.end (); li++)
        {
                // Live node for rho.L.*
                label l = *li;
                deterministic_node * out_live_n = live_value.get_destination_node (live_node, l);
                if (!out_live_n)
                {
                        RESULT ("\nError: dest of live_node=%d via l=%d not found", live_node.get_node_id (), l);
                        continue;
                }
                DEBUG ("\nlive=%d->%d->%d", live_node.get_node_id (), l, out_live_n->get_node_id ());

                // Points-to node for rho.L.*
                set<label> dest_vars;
                if (pts_node)
		{
			set<label> var_fields = program.get_var_fields (pts_node, l);
			set<label>::iterator vfi;
			for (vfi = var_fields.begin (); vfi != var_fields.end (); vfi++)
			{
				label var_field_pts_node = *vfi;
				// Mark rho.L as live
				live_pts_nodes.insert (var_field_pts_node);
				// Collect rho.L.*
				pts_value.get_destination_vars (var_field_pts_node, dest_vars);
			}
		}
                else
		{
			// Mark rho.L as live
			live_pts_nodes.insert (l);
			// Collect L.*
                        pts_value.get_destination_vars (l, dest_vars);
		}
        
                set<label>::iterator pi;
                for (pi = dest_vars.begin (); pi != dest_vars.end (); pi++)
                {
                        label out_pts_n = *pi;
                        sync_pts_live_value (out_pts_n, *out_live_n, pts_value, live_value, 
				sync_pts_live_nodes, live_pts_nodes);
                }
        }
}

/**
 * Definition of a template specialized function (sync_pts_live_value) should
 * come before its call.
 */

template <>
void allocation_site_based_analysis<deterministic_graph>::
kill_dead_pts_edges (unlabeled_edges & pts_value,
        context<unlabeled_edges, deterministic_graph> & current_context,
        basic_block current_block)
{
	// Synchronize pta with live graph (flow-sensitive, context-indept,
	// context-dept). Since liveness is a separable framework, we can
	// synchronize one by one.

        map<label, set<deterministic_node *> > sync_pts_live_nodes;
	set<label> live_pts_nodes;

        deterministic_graph * fs_out_live = get_live_out_value (current_context, current_block);
#if DEBUG_CONTAINER
	DEBUG ("\nfs_out_live=");
	if (fs_out_live)
		fs_out_live->print_value (NULL);
#endif
	if (fs_out_live)
		sync_pts_live_value (0, fs_out_live->stack, pts_value, *fs_out_live, 
			sync_pts_live_nodes, live_pts_nodes);

	// get unaffected context_dept and context_indept liveness
        context<deterministic_graph, unlabeled_edges> * dept_context = get_dependent_context (&current_context);
        if (!dept_context)
        {
                RESULT ("\nError: No dependent context to find dead pointers");
		return;
        }
        unaffected_live<deterministic_graph> * aux = 
		(unaffected_live<deterministic_graph> *) dept_context->get_aux_info ();
        if (!aux)
        {
		RESULT ("\nError:  aux (deterministic_graph) is NULL");
                return;
        }

	deterministic_graph * unaffected_context_dept_live = &aux->context_dept;
#if DEBUG_CONTAINER
	DEBUG ("\nunaffected_context_dept_live=");
	unaffected_context_dept_live->print_value (NULL);
#endif
	sync_pts_live_nodes.clear ();
	sync_pts_live_value (0, unaffected_context_dept_live->stack, 
		pts_value, *unaffected_context_dept_live, 
		sync_pts_live_nodes, live_pts_nodes);

	// This is required because var x may be unaffected by liveness of the
	// context but may be affected by points-to of the context. However, in
	// case of recursion, locals of earlier context may be live and the
	// points-to of locals are not killed.
	deterministic_graph * unaffected_context_indept_live = &aux->context_indept;
#if DEBUG_CONTAINER
	DEBUG ("\nunaffected_context_indept_live=");
	unaffected_context_indept_live->print_value (NULL);
#endif
	sync_pts_live_nodes.clear ();
	sync_pts_live_value (0, unaffected_context_indept_live->stack, 
		pts_value, *unaffected_context_indept_live, 
		sync_pts_live_nodes, live_pts_nodes);

	pts_value.kill_dead_pts_edges (live_pts_nodes);
}

/**
 * Definition of a template specialized function (kill_dead_pts_edges) should
 * come before its call.
 */

template <>
void allocation_site_based_analysis<deterministic_graph>::
get_live_data (unlabeled_edges & out_value,
        context<unlabeled_edges, deterministic_graph> & current_context,
        basic_block current_block)
{
        DEBUG ("\nget_live_data");
	// The return variable is live at IN of return block and dead at IN and OUT of
	// END_BLOCK. We do not want to kill it at IN of END_BLOCK because
	// otherwise the caller function will get called context's value
	// without the return variable (because context's value is picked from
	// IN of END_BLOCK). We do not want to kill it at OUT of END_BLOCK
	// because whether or not is_value_same is true depends on OUT value. 

	unsigned int bt = ((block_information *)(current_block->aux))->get_block_type ();
        if (program.is_pred_of_end_block (current_block) || (bt & END_BLOCK))
		return;

#if DEBUG_CONTAINER
	DEBUG ("\nbefore kill_dead_pts_edges()=");
	out_value.print_value (NULL);
#endif

	kill_dead_pts_edges (out_value, current_context, current_block);
}

template <class LIVE_VALUE_TYPE>
LIVE_VALUE_TYPE * allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_live_out_value (context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context,
        basic_block current_block)
{
        DEBUG ("\nget_dead_variables()");
        context<LIVE_VALUE_TYPE, unlabeled_edges> * dept_context = get_dependent_context (&current_context);
        if (!dept_context)
        {
                RESULT ("\nError: No dependent context to find dead pointers");
		return NULL;
        }
        LIVE_VALUE_TYPE * out_liveness = dept_context->get_out_value (current_block);
        if (!out_liveness)
                RESULT ("\nError: Block %d is unreachable by dept_context",
                        current_block->index);
	return out_liveness;
}

template <>
void allocation_site_based_analysis<non_deterministic_graph>::
get_live_data (unlabeled_edges & out_value,
        context<unlabeled_edges, non_deterministic_graph> & current_context,
        basic_block current_block)
{
	RESULT ("\nError: allocation-sites analysis filtered by non-deterministic liveness is not defined");
}

template <class LIVE_VALUE_TYPE>
bool allocation_site_based_analysis<LIVE_VALUE_TYPE>::
is_dest_of_dept_context_exist (context<unlabeled_edges, LIVE_VALUE_TYPE> * src_context,
	basic_block call_site,
	struct cgraph_node * dest_function)
{
        DEBUG ("\nis_dest_dept_context_exist(src=%d, call_site=%d, dest_func=%s)",
		src_context->get_context_id (), call_site->index, cgraph_node_name (dest_function));

	context<LIVE_VALUE_TYPE, unlabeled_edges> * dest_dept_context = 
		get_dest_of_dept_context (src_context, call_site, dest_function);
	if (!dest_dept_context)
	{
		DEBUG ("\ndest of dept context does not exist");
		return false;
	}

	basic_block start_block = dest_dept_context->get_start_block ();
	if (!start_block)
		RESULT ("\nError: start_block is null");
	LIVE_VALUE_TYPE * dest_fn_in_value = dest_dept_context->get_in_value (start_block);

	if (!dest_fn_in_value)
	{
		DEBUG ("\nIN value of start of dest of dept con=%d does not exist",
			dest_dept_context->get_context_id ());
		return false;
	}

	return true;
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_callees_glob_par_defs (context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context,
	set<variable_id> & callees_glob_par_defs)
{
	struct cgraph_node * curr_func = current_context.get_function ();
	set<variable_id> * callees_global_defs = function_side_effects.get_callees_global_defs (curr_func);
	if (callees_global_defs)
		callees_glob_par_defs.insert (callees_global_defs->begin (), callees_global_defs->end ());

	set<variable_id> * function_param_defs = function_side_effects.get_function_param_defs (curr_func);
	if (function_param_defs)
		callees_glob_par_defs.insert (function_param_defs->begin (), function_param_defs->end ());
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
delete_aux_info (void * aux_info)
{
	DEBUG ("\nallocation_site_based_analysis::delete_aux_info()");
#if GC
	if (aux_info)
	{
		DEBUG ("\nallocation_site_based_analysis::delete_aux_info() %x %x %x", aux_info, 
			&((unaffected_pta *) aux_info)->context_indept, &((unaffected_pta *) aux_info)->context_dept);
		delete ((unaffected_pta *) aux_info);
	}
#endif
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
print_aux_info (void * aux_info)
{
#if DEBUG_CONTAINER
	if (!aux_info)
	{
		DEBUG ("\naux=NULL");
		return;
	}

	unaffected_pta * aux = (unaffected_pta *) aux_info;
	DEBUG ("\ncontext_indept aux=");
	aux->context_indept.print_value (NULL);

	DEBUG ("\ncontext_dept aux=");
	aux->context_dept.print_value (NULL);
#endif
}

/**
 * aux_info of allocation_site_based_analysis<variables> represents bypassed
 * points-to graph due to this call only. aux_info of
 * allocation_site_based_analysis <deterministic_graph> (that is computed in
 * meet_over_valid_paths) represents bypassed points-to graph of all the
 * previous calls.
 */

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
save_context_indept_pta (context<unlabeled_edges, LIVE_VALUE_TYPE> & src_context,
	basic_block call_site,
	struct cgraph_node * dest_function,
	unlabeled_edges & context_indept_pta)
{
	context<unlabeled_edges, LIVE_VALUE_TYPE> * dest_context = 
		src_context.get_destination_context (call_site, dest_function);
	if (!dest_context)
	{
		RESULT ("\nError: dest context of src-context=%d, function=%s not created",
			src_context.get_context_id (), cgraph_node_name (dest_function));
		return;
	}

	copy_context_indept_aux (context_indept_pta, *dest_context);
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
copy_context_indept_aux (unlabeled_edges & src_value, 
	context<unlabeled_edges, LIVE_VALUE_TYPE> & dest_context)
{
        struct unaffected_pta * dest_aux = 
		(unaffected_pta *) dest_context.get_aux_info ();
        if (!dest_aux)
        {
                dest_aux = new unaffected_pta;
		DEBUG ("\ncopy_context_indept_aux new %x", dest_aux);
		dest_context.set_aux_info (dest_aux);
        }

	dest_aux->context_indept.copy_value (src_value, false);
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
copy_unaffected_context_dept_aux (unlabeled_edges & src_value, 
	context<unlabeled_edges, LIVE_VALUE_TYPE> & dest_context,
	bool is_erase_old)
{
        struct unaffected_pta * dest_aux = 
		(unaffected_pta *) dest_context.get_aux_info ();
        if (!dest_aux)
        {
                dest_aux = new unaffected_pta;
		dest_context.set_aux_info (dest_aux);
        }

	// Each START value (context-dept value) has only one unaffected subset.
	// Therefore, erase any old data and set this new subset. This is
	// required if the same context is being reused for some other START
	// value.
	if (is_erase_old)
		dest_aux->context_dept.erase ();
	dest_aux->context_dept.copy_value (src_value, false);
#if DEBUG_CONTAINER
	dest_aux = (unaffected_pta *) dest_context.get_aux_info ();
	DEBUG ("\nsaved: unaffected context_dept=");
	dest_aux->context_dept.print_value (NULL);
#endif

}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
copy_context_value (void * src_con, void * dest_con)
{
	context<unlabeled_edges, variables> * src_context = 
		(context<unlabeled_edges, variables> *) src_con;
	context<unlabeled_edges, LIVE_VALUE_TYPE> * dest_context = 
		(context<unlabeled_edges, LIVE_VALUE_TYPE> *) dest_con;

        unaffected_pta * src_aux = (unaffected_pta *) src_context->get_aux_info ();   
        if (!src_aux)
		return;

	copy_context_indept_aux (src_aux->context_indept, *dest_context); 
	copy_unaffected_context_dept_aux (src_aux->context_dept, *dest_context, false); 
}

/** 
 * Accumulate in callee, context_indept (aux) from callers.
 */
template <class LIVE_VALUE_TYPE>
bool allocation_site_based_analysis<LIVE_VALUE_TYPE>::
caller_to_callee_info (context<unlabeled_edges, LIVE_VALUE_TYPE> & con)
{
	DEBUG ("\npull_info(unique_context=%d)", con.get_context_id ());

	unaffected_pta * aux_info = (unaffected_pta *) con.get_aux_info ();
	// This is not error. aux of main is NULL.
	if (!aux_info)
		return true; 

	unlabeled_edges * con_context_indept = &aux_info->context_indept;
	unlabeled_edges * old_con_context_indept = con_context_indept->copy_value (false);

	set<context<unlabeled_edges, LIVE_VALUE_TYPE> *> source_contexts;
	get_source_contexts (con, source_contexts);
	typename set<context<unlabeled_edges, LIVE_VALUE_TYPE> *>::iterator sci;
	for (sci = source_contexts.begin (); sci != source_contexts.end (); sci++)
	{
		context<unlabeled_edges, LIVE_VALUE_TYPE> * sc = *sci;
		unaffected_pta * src_aux = (unaffected_pta *) sc->get_aux_info ();   
        	if (!src_aux)
			continue;
		copy_context_indept_aux (src_aux->context_indept, con); 
	}

	unlabeled_edges * new_con_context_indept = &aux_info->context_indept;
#if DEBUG_CONTAINER
	DEBUG ("\naux of context=%d", con.get_context_id ());
	new_con_context_indept->print_value (NULL);
#endif
	bool is_aux_same = new_con_context_indept->is_value_same (*old_con_context_indept);

	delete old_con_context_indept;

	return is_aux_same;
}

/** 
 * Accumulate in caller, callees_lhs_derefs (aux) from callees.
 */
template <class LIVE_VALUE_TYPE>
bool allocation_site_based_analysis<LIVE_VALUE_TYPE>::
callee_to_caller_info (context<unlabeled_edges, LIVE_VALUE_TYPE> & con)
{
	DEBUG ("\npush_info(unique_context=%d)", con.get_context_id ());
	struct cgraph_node * func = con.get_function ();
	DEBUG ("\nbefore get_old_lhs_derefs");
	set<variable_id> * ptr_old_lhs_derefs = function_side_effects.get_callees_lhs_derefs (func);
	set<variable_id> old_lhs_derefs;
	if (ptr_old_lhs_derefs)
		old_lhs_derefs = *ptr_old_lhs_derefs;
	DEBUG ("\nafter get_old_lhs_derefs");

	map<pair<block_index, function_index>, context<unlabeled_edges, LIVE_VALUE_TYPE> *> destination_contexts;
	get_destination_contexts (con, destination_contexts);
	typename map<pair<block_index, function_index>, context<unlabeled_edges, LIVE_VALUE_TYPE> *>::iterator dci;
	for (dci = destination_contexts.begin (); dci != destination_contexts.end (); dci++)
	{
		context<unlabeled_edges, LIVE_VALUE_TYPE> * dc = dci->second;
		DEBUG ("\ndest_con=%d", dc->get_context_id ());
		struct cgraph_node * dest_func = dc->get_function ();
		set<variable_id> * callee_lhs_derefs = function_side_effects.get_callees_lhs_derefs (dest_func);
		if (callee_lhs_derefs)
			function_side_effects.add_callees_lhs_derefs (func, *callee_lhs_derefs);
	}

	set<variable_id> * new_lhs_derefs = function_side_effects.get_callees_lhs_derefs (func);
	
	if (!new_lhs_derefs)
		return false;

	if (old_lhs_derefs.size () != new_lhs_derefs->size ())
	{
		DEBUG ("\nold_lhs_derefs.size != new_lhs_derefs->size");
		return false;
	}

#if DEBUG_CONTAINER
	DEBUG ("old_lhs_derefs==*new_lhs_derefs = %d", (old_lhs_derefs == (*new_lhs_derefs)));
#endif

	return (old_lhs_derefs == (*new_lhs_derefs));
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
store_context_info (context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context)
{
	set<variable_id> lhs_derefs;
	compute_lhs_derefs (current_context, lhs_derefs);
	struct cgraph_node * func = current_context.get_function ();
	function_side_effects.add_callees_lhs_derefs (func, lhs_derefs);
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
compute_lhs_derefs (context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context,
	set<variable_id> & lhs_derefs)
{
	struct cgraph_node * func = current_context.get_function ();
	struct function * function_decl = DECL_STRUCT_FUNCTION (func->decl);
	basic_block current_block;
	FOR_EACH_BB_FN (current_block, function_decl)
	{
		list<pair<unsigned int, bool> > parsed_data_indices =
			((block_information *)(current_block->aux))->get_parsed_data_indices ();
		DEBUG ("\nFetched parsed data");

		list<pair<unsigned int, bool> >::iterator it;
		for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
		{
			unsigned int index = (*it).first;
			bool is_assignment = (*it).second;
			DEBUG ("\nParsed data: index %d, bool %d, ", index, is_assignment);
			if (is_assignment)
			{
				constraint_t assignment = 
					VEC_index (constraint_t, program.assignment_data, index);
				constraint_expr lhs = assignment->lhs;
				constraint_expr rhs = assignment->rhs;
				csvarinfo_t rhs_var = VEC_index (csvarinfo_t, program.variable_data, rhs.var);
				// If lhs is DEREF and rhs is a variable whose
				// liveness can be generated in
				// dfa/liveness_analysis_deterministic/non_deterministic
				if (lhs.type == DEREF && rhs_var && rhs_var->decl)
					compute_alias_def_deref (lhs.var, lhs.offset, current_block, current_context, lhs_derefs);
			}
		}
	}
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
compute_alias_def_deref (variable_id var,
	label var_offset,
	basic_block current_block,
	context<unlabeled_edges, LIVE_VALUE_TYPE> & current_context,
	set<variable_id> & lhs_derefs)
{
	DEBUG ("\ncompute_alias_def_deref (var=%d)", var);
	lhs_derefs.insert (var);

	unaffected_pta * aux = (unaffected_pta *) current_context.get_aux_info ();
	if (!aux)
	{
		RESULT ("\nError: aux (unaffected context_dept value) is NULL");
		return;
	}

	// Link alias of lhs_derefs need unaffected_context_indept_pta i.e.
	// par_unreachable_pta also.

	unlabeled_edges * unaffected_context_indept_pta = &aux->context_indept;
	unlabeled_edges * unaffected_context_dept_pta = &aux->context_dept;
	// Get IN pta and not OUT pta since pointers required by the statement
	// may be dead at OUT.
	unlabeled_edges * fs_context_dept_pta = current_context.get_in_value (current_block);
	unlabeled_edges temp;
	if (!fs_context_dept_pta)
		fs_context_dept_pta = &temp;

	set<variable_id> dest_vars;
	// Find variables reaching VAR also.
	dest_vars.insert (var);
	unaffected_context_indept_pta->get_destination_vars (var, dest_vars);
	unaffected_context_dept_pta->get_destination_vars (var, dest_vars);
	fs_context_dept_pta->get_destination_vars (var, dest_vars);

	// If dest_var is a non-heap, e.g. VAR V points to W, then W.offset
	// should be added to lhs_derefs. Adding only W will not help.  Do not
	// add W.offset to dest_vars because we do not want things reaching
	// W.offset but things reaching W (for link aliases).
	set<variable_id> dest_vars_offset;
	if (var_offset)
		dest_vars_offset = program.get_var_fields (dest_vars, var_offset);

	if  (!dest_vars.size ())
		return;

	unaffected_context_indept_pta->compute_in_edge_list ();
	unaffected_context_dept_pta->compute_in_edge_list ();
	fs_context_dept_pta->compute_in_edge_list ();

	// Points-to analysis is not a separable framework. These need to be
	// combined and then reachable vars need to be found, or alternatively,
	// find in_edge_list from all parts of the points-to graph at the same
	// time.

	set<variable_id> reaching_vars;
	get_reaching_vars (dest_vars, reaching_vars,
		unaffected_context_indept_pta->in_edge_list,
		unaffected_context_dept_pta->in_edge_list,
		fs_context_dept_pta->in_edge_list);
	// unaffected_context_indept_pta->get_reaching_vars (dest_vars, reaching_vars);
	// unaffected_context_dept_pta->get_reaching_vars (dest_vars, reaching_vars);
	// fs_context_dept_pta->get_reaching_vars (dest_vars, reaching_vars);

	reaching_vars.insert (dest_vars_offset.begin (), dest_vars_offset.end ());

	set<variable_id>::iterator vi;
	for (vi = reaching_vars.begin (); vi != reaching_vars.end (); vi++)
	{
		variable_id vid = *vi;
		DEBUG ("\nreaching_vars=%d", vid);
		csvarinfo_t var = VEC_index (csvarinfo_t, program.variable_data, vid);
		if (!var)
			continue;
		DEBUG ("\nreaching_vars=%s(%d)", var->name, var->id);
		if (var->is_heap_var)
			continue;
		if (!var->decl)
			continue;
		lhs_derefs.insert (vid);
	}
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_reaching_vars (set<label> & vars, 
	set<label> & reaching_vars,
	map<label, set<label> > & in_edge_list_1,
	map<label, set<label> > & in_edge_list_2,
	map<label, set<label> > & in_edge_list_3)
{
	// Get all typecasts
	set<csvarinfo_t> var_typecasts;
	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
	{
		program.cs_lookup_vi_for_typecasts (*vi, var_typecasts);
		DEBUG ("\nFound %d types for var_decl=%d", var_typecasts.size (), *vi);
	}
	set<csvarinfo_t>::iterator vti;
	// Get reaching from all typecasts
	for (vti = var_typecasts.begin (); vti != var_typecasts.end (); vti++)
	{
		csvarinfo_t vt = *vti;
		DEBUG ("\nget_reaching_vars(%s(%d))", vt->name, vt->id);
		get_reaching_vars (vt->id, reaching_vars,
			in_edge_list_1, in_edge_list_2, in_edge_list_3);
	}
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_reaching_vars (label var, 
	set<label> & reaching_vars,
	map<label, set<label> > & in_edge_list_1,
	map<label, set<label> > & in_edge_list_2,
	map<label, set<label> > & in_edge_list_3)
{
	// If var has already been considered
	if (reaching_vars.find (var) != reaching_vars.end ())
		return;

	DEBUG ("\nget_reaching_vars(var=%d)", var);

	reaching_vars.insert (var);

	set<label> in_vars;
	if (in_edge_list_1.find (var) != in_edge_list_1.end ())
	{
		DEBUG ("\nin_edge_list of var=%d", var);
		set<label> temp_in_vars;
		temp_in_vars = in_edge_list_1[var];
		in_vars.insert (temp_in_vars.begin (), temp_in_vars.end ());
	}
	if (in_edge_list_2.find (var) != in_edge_list_2.end ())
	{
		DEBUG ("\nin_edge_list of var=%d", var);
		set<label> temp_in_vars;
		temp_in_vars = in_edge_list_2[var];
		in_vars.insert (temp_in_vars.begin (), temp_in_vars.end ());
	}
	if (in_edge_list_3.find (var) != in_edge_list_3.end ())
	{
		DEBUG ("\nin_edge_list of var=%d", var);
		set<label> temp_in_vars;
		temp_in_vars = in_edge_list_3[var];
		in_vars.insert (temp_in_vars.begin (), temp_in_vars.end ());
	}

	// Computing only those fields reaching src_var is difficult.
	// Over-approximately include all fields less than src_var->offset.
#if DEBUG_CONTAINER
	csvarinfo_t src_var = program.cs_get_varinfo (var);
	DEBUG ("\nget_field_var_ids(var=%s(%d))", src_var->name, var);
#endif
	program.get_prev_field_var_ids (var, in_vars);

	get_reaching_vars (in_vars, reaching_vars,
		in_edge_list_1, in_edge_list_2, in_edge_list_3);
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
print_value (unlabeled_edges & value)
{
	value.print_value (NULL);
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_path_prefixes (list<label> & path,
	set<list<label> > & paths)
{
	list<label> src_path, dest_path;

	list<label>::iterator li;
	for (li = path.begin (); li != path.end (); li++)
	{
		label l = *li;
		dest_path = src_path;
		dest_path.push_back (l);
		paths.insert (dest_path);
		src_path = dest_path;
	}	
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_useful_paths (unsigned int index,
	bool is_assignment_index,
	set<list<label> > & useful_paths)
{
	DEBUG ("\nget_useful_pt_ap_nodes()");

	// Use data index

	if (!is_assignment_index)
	{
		csvarinfo_t var = VEC_index (csvarinfo_t, program.variable_data, index);

		list<label> useful_path;
		useful_path.push_back (var->id);
		useful_path.push_back (ASTERISK);
		// No need to append offset sequence.
		// (a) int D.1234=x->d; return D.1234; No need to find aliases of x->d as d is non-integer.
		// (b) int * D.1234=x->p; return D.1234; x->p is covered in assignment statement -- not here.

		get_path_prefixes (useful_path, useful_paths);

		return;
	}

	// Assignement data index

	constraint_t assignment = 
		VEC_index (constraint_t, program.assignment_data, index);
	constraint_expr lhs = assignment->lhs;
	constraint_expr rhs = assignment->rhs;	
	// Ignore PHI statements of the following type
	if (lhs.var == rhs.var && lhs.type == rhs.type && lhs.offset == rhs.offset)
		return;

	DEBUG ("\nlhs=%d->%lld (%d), rhs=%d->%lld (%d)", lhs.var, lhs.offset, lhs.type,
		rhs.var, rhs.offset, rhs.type);

	set<list<label> > useful_lhs_paths, useful_rhs_paths;

	get_useful_lhs_paths (lhs, useful_lhs_paths);
	useful_paths.insert (useful_lhs_paths.begin (), useful_lhs_paths.end ());

	get_useful_rhs_paths (rhs, useful_rhs_paths);
	useful_paths.insert (useful_rhs_paths.begin (), useful_rhs_paths.end ());

}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_useful_rhs_paths (constraint_expr & rhs,
	set<list<label> > & rhs_paths)
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

		rhs_path.push_back (rhs.var);
		rhs_path.push_back (ASTERISK);
		list<label>::iterator li;
		if (rhs.offset_sequence)
		{
			for (li = rhs.offset_sequence->begin (); li != rhs.offset_sequence->end (); li++)
				if (*li)
					rhs_path.push_back (*li);
		}

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

		rhs_path.push_back (rhs.var);
		rhs_path.push_back (ASTERISK);
		list<label>::iterator li;
		if (rhs.offset_sequence)
		{
			for (li = rhs.offset_sequence->begin (); li != rhs.offset_sequence->end (); li++)
				if (*li)
					rhs_path.push_back (*li);
		
			rhs_path.push_back (ASTERISK);
		}

		break;
	}
	default:
		RESULT ("\nError: rhs.type cannot hold a fourth type");
	}

	get_path_prefixes (rhs_path, rhs_paths);
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_useful_lhs_paths (constraint_expr & lhs,
	set<list<label> > & lhs_paths)
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

		lhs_path.push_back (lhs.var);
		if (lhs.offset_sequence && lhs.offset_sequence->size ())
			lhs_path.push_back (ASTERISK);

		break;
	}

	case ADDRESSOF:
		DEBUG ("\nlhs.type == ADDRESSOF");
		break;

	default:
		RESULT ("\nError: lhs.type cannot hold a fourth type");
	}

	get_path_prefixes (lhs_path, lhs_paths);
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

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
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

		set<list<label> > useful_paths;
       		get_useful_paths (index, is_assignment, useful_paths);

		// Counted an alias pair as many times as it is useful
		map<list<label>, set<list<label> > >::iterator api;
		for (api = in_ap_alias_set.begin (); api != in_ap_alias_set.end (); api++)
		{
			list<label> ap = api->first;
			if (!unlabeled_edges::is_useful_path (ap, useful_paths))
				continue;

			set<list<label> > aps = api->second;
			set<list<label> >::iterator li;
			for (li = aps.begin (); li != aps.end (); li++)
				if (*li != ap)
					repeating_useful_ap_alias_set[ap].push_back (*li);
		}
	}
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
dump_useful_aps (unsigned int funcid,
	basic_block current_block,
	FILE * useful_ap_file_ptr)
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

		set<list<label> > useful_paths;
       		get_useful_paths (index, is_assignment, useful_paths);

		set<list<label> >::iterator si;
		for (si = useful_paths.begin (); si != useful_paths.end (); si++)
		{
			fprintf (useful_ap_file_ptr, "%d %d ", funcid, current_block->index);
			list<label> ap = *si;
			list<label>::iterator li;
			for (li = ap.begin (); li != ap.end (); li++)
				fprintf (useful_ap_file_ptr, "%d ", *li);
			fprintf (useful_ap_file_ptr, "\n");
		}
	}
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
print_alias_analysis_statistics (map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> > & function_contexts)
{
	INFO ("\nNAME-BASED POINTS-TO PAIRS\n===============\n");

#if DUMP_ANALYSIS
	RESULT ("\nDumping analysis");
	dump_analysis (function_contexts);
	RESULT ("\nDone dumping analysis");
#endif

#if ALIAS_STATISTICS_CONTAINER == 0 && DATA_SIZE_STATISTICS == 0
	return;
#endif

	map<function_index, unsigned int> program_use_points;
	unsigned int max_num_nodes = 0;
	float max_avg_out_edges = 0;
	set<set<list<int> > > program_aliases;
	int tot_program_points_to_pairs = 0;
	map<label, set<label> > program_points_to_pairs;
	map<list<label>, set<list<label> > > unique_ap_alias_set;
	map<list<label>, set<list<label> > > unique_ap_alias_set_non_temp;

	unsigned int count_ap_alias_set = 0;
	unsigned int count_ap_alias_set_non_temp = 0;
	unsigned int count_useful_ap_alias_set = 0;
	unsigned int count_useful_ap_alias_set_non_temp = 0;
	unsigned int program_blocks = 0;
	unsigned int useful_program_blocks = 0;
	unsigned int max_acyclic_ap_len = 0;
	unsigned int heap_to_stack_pointers = 0;
	unsigned int contexts_count = 0;
	unsigned int function_count = 0;
	unsigned int max_contexts_per_function = 0;
	unsigned int count_explicit_valid_nodes = 0;
	unsigned int count_explicit_valid_edges = 0;
	unsigned int count_valid_nodes = 0;
	unsigned int count_valid_edges = 0;
	unsigned int pcount = 0;
	unsigned int num_tot_ap = 0;
	unsigned int num_useful_ap = 0;

	set<label> heap_to_stack_pointees;
	// Map from already encountered points-to pairs to the number of alias pairs computed.
	map<map<label, set<label> >, map<list<label>, set<list<label> > > > memoized_points_to_alias;

	// We use FUNCTION_CONTEXTS_MAP instead of PROGRAM_CONTEXTS of
	// inter_procedural_analysis.hh so that the statistics are printed in
	// order of functions. This makes it easier to compare to files of
	// statistics.
	typename map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> >::iterator fi;
	for (fi = function_contexts.begin (); fi != function_contexts.end (); fi++)
	{
		struct cgraph_node * function = program.get_cgraph_node (fi->first);
		const char * function_name = cgraph_node_name (function);
		RESULT ("\nFunction %s", function_name);
		struct function * function_decl = DECL_STRUCT_FUNCTION (function->decl);

		context_enums<unlabeled_edges, LIVE_VALUE_TYPE> contexts = fi->second;
		contexts_count += contexts.size ();
		function_count++;
		if (max_contexts_per_function < contexts.size ())
			max_contexts_per_function = contexts.size ();

		unsigned int function_use_points = 0;
		basic_block block;
		FOR_EACH_BB_FN (block, function_decl)
		{
			program_blocks++;

			unsigned int block_id = block->index;
			map<label, set<label> > in_block_points_to_pairs;
			map<label, set<label> > out_block_points_to_pairs;
			map<label, set<label> > in_block_root_aliases;
			map<label, set<label> > out_block_root_aliases;
			set<set<list<int> > > in_block_aliases;
			set<set<list<int> > > out_block_aliases;
			map<label, set<label> > in_block_reachable_roots;
			map<label, set<label> > out_block_reachable_roots;
			map<label, set<list<label> > > in_aliases;
			map<label, set<list<label> > > out_aliases;
			map<list<label>, set<list<label> > > in_ap_alias_set;			// value includes key
			map<list<label>, set<list<label> > > out_ap_alias_set;
			map<list<label>, set<list<label> > > in_ap_alias_set_non_temp;		// value includes key
			map<list<label>, set<list<label> > > out_ap_alias_set_non_temp;
			map<list<label>, list<list<label> > > repeating_useful_ap_alias_set;	// value does not include key
			map<list<label>, list<list<label> > > repeating_useful_ap_alias_set_non_temp;
			set<unlabeled_edges *> in_values;

			// Compute meet of all the contexts for this basic block

			typename context_enums<unlabeled_edges, LIVE_VALUE_TYPE>::iterator ci;
			for (ci = contexts.begin (); ci != contexts.end (); ci++)
			{
				context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context =
					ci->second;
				DEBUG ("\nbb=%d,context=%d", block->index, current_context->get_context_id ());
				unlabeled_edges * g;

				///////////////////////////////////////////////////////////////////////////

				// In value
				DEBUG ("\nget_graph_statistics in");
				g = current_context->get_in_value (block);
				if (!g)
				{
					RESULT ("\nError: in value of block=%d is NULL", block->index);
					continue;
				}
				// Add memoized pta graph of called context
				restore_unaffected_context_dept_pta (*current_context, *g);
				g->get_graph_statistics (max_num_nodes, max_avg_out_edges,
					in_block_points_to_pairs,
					in_block_root_aliases,
					in_block_aliases,
					in_block_reachable_roots,
					in_ap_alias_set_non_temp,
					memoized_points_to_alias,
					false);
				// Propagate only function_par_defs and callees_global_defs
				remove_unaffected_context_dept_pta (*current_context, *g);
				DEBUG ("\ndone get_graph_statistics in");
	
				///////////////////////////////////////////////////////////////////////////

				// Collecting IN values of all contexts at this program point
				in_values.insert (g);

				///////////////////////////////////////////////////////////////////////////

				// Out value
				DEBUG ("\nget_graph_statistics out");
				g = current_context->get_out_value (block);
				if (!g)
				{
					RESULT ("\nError: out value of block=%d is NULL", block->index);
					continue;
				}
				// Add memoized pta graph of called context
				restore_unaffected_context_dept_pta (*current_context, *g);
				g->get_graph_statistics (max_num_nodes, max_avg_out_edges, 
					out_block_points_to_pairs, 
					out_block_root_aliases, 
					out_block_aliases,
					out_block_reachable_roots,
					out_ap_alias_set_non_temp,
					memoized_points_to_alias,
					false);

				// Propagate only function_par_defs and callees_global_defs
				remove_unaffected_context_dept_pta (*current_context, *g);
				DEBUG ("\ndone get_graph_statistics out");

				///////////////////////////////////////////////////////////////////////////
			}

			////////////////////////////////////////////////////////////////////////////

			// unlabeled_edges g;
			// if (program.print_source_location (block))
			//	g.print_points_to_pairs (in_block_points_to_pairs, true);

			////////////////////////////////////////////////////////////////////////////

			// unsigned int c = unlabeled_edges::get_max_acyclic_ap_len (in_block_points_to_pairs);
			// if (max_acyclic_ap_len < c)
			//	max_acyclic_ap_len = c;

			////////////////////////////////////////////////////////////////////////////


			RESULT ("\n    in-bb=%d", block_id);
#if POINTS_TO
			// function_use_points += print_block_points_to_pairs (block, contexts, true, true);
			unsigned int c = unlabeled_edges::print_points_to_pairs (in_block_points_to_pairs, heap_to_stack_pointees);
			heap_to_stack_pointers += c;
#endif

#if DATA_SIZE_STATISTICS
#if POINTS_TO
			unlabeled_edges::get_valid_graph_statistics (in_block_points_to_pairs, 
				count_explicit_valid_nodes, count_explicit_valid_edges, count_valid_nodes, count_valid_edges);
#endif
#endif

#if ALIAS_STATISTICS_CONTAINER
			// g.print_access_paths (in_aliases);
			// pcount = count_map_size (in_ap_alias_set);
                        // RESULT ("\n\tIN All=%d", pcount);
			// unlabeled_edges::print_ap_alias_set (in_ap_alias_set);
			// g.print_root_aliases (in_block_root_aliases);
			// g.print_aliases (in_block_aliases);
			// g.print_reachable_roots (in_block_reachable_roots);
			// count_ap_alias_set += pcount; 

			////////////////////////////////////////////////////////////////////////////

                        // NON_TEMP ALL program points
                        // unlabeled_edges::get_non_temp_ap_alias_set (in_ap_alias_set, in_ap_alias_set_non_temp);
			pcount = 0;
			count_map_size (in_ap_alias_set_non_temp, pcount, num_tot_ap);
                        count_ap_alias_set_non_temp += pcount;
                        RESULT ("\n\tIN Non-temp=%d", pcount);
                        unlabeled_edges::print_ap_alias_set (in_ap_alias_set_non_temp);

			// in_ap_alias_set.clear ();
			// map<list<label>, set<list<label> > >().swap (in_ap_alias_set); 
			// in_ap_alias_set = map<list<label>, set<list<label> > >();

                        ////////////////////////////////////////////////////////////////////////////

                        // NON_TEMP USEFUL program points
			// Print unique ap alias set fora statement over all the
			// contexts at this program point.
			get_useful_ap_alias_set (in_ap_alias_set_non_temp, block, 
				repeating_useful_ap_alias_set_non_temp);
			pcount = 0;
			count_map_size (repeating_useful_ap_alias_set_non_temp, pcount, num_useful_ap);
                        count_useful_ap_alias_set_non_temp += pcount;
                        RESULT ("\n\tUseful non-temp=%d, useful_program_blocks=%d", pcount, useful_program_blocks);
                        unlabeled_edges::print_ap_alias_set (repeating_useful_ap_alias_set_non_temp);
                        if (pcount)
                                useful_program_blocks++;

			// repeating_useful_ap_alias_set_non_temp.clear ();
			// map<list<label>, list<list<label> > >().swap (repeating_useful_ap_alias_set_non_temp); 
			repeating_useful_ap_alias_set_non_temp = map<list<label>, list<list<label> > >(); 

			////////////////////////////////////////////////////////////////////////////

                        // NON_TEMP USEFUL program points
//                        unlabeled_edges::get_non_temp_ap_alias_set (repeating_useful_ap_alias_set,
//                                repeating_useful_ap_alias_set_non_temp);
//			pcount = count_map_size (repeating_useful_ap_alias_set_non_temp);
//                        RESULT ("\n\tuseful non-temp=%d", pcount);
//                        unlabeled_edges::print_ap_alias_set (repeating_useful_ap_alias_set_non_temp);
//                        count_useful_ap_alias_set_non_temp += pcount;

			merge_map (in_ap_alias_set_non_temp, unique_ap_alias_set_non_temp);

			// in_ap_alias_set_non_temp.clear ();
			// map<list<label>, set<list<label> > >().swap (in_ap_alias_set_non_temp); 
			in_ap_alias_set_non_temp = map<list<label>, set<list<label> > >();

			////////////////////////////////////////////////////////////////////////////

			// c = unlabeled_edges::get_max_acyclic_ap_len (out_block_points_to_pairs);
			// if (max_acyclic_ap_len < c)
			//	max_acyclic_ap_len = c;

#endif
			////////////////////////////////////////////////////////////////////////////

			RESULT ("\n    out-bb=%d", block_id);
#if POINTS_TO
			c = unlabeled_edges::print_points_to_pairs (out_block_points_to_pairs, heap_to_stack_pointees);
			heap_to_stack_pointers += c;
#endif

#if DATA_SIZE_STATISTICS
#if POINTS_TO
			unlabeled_edges::get_valid_graph_statistics (out_block_points_to_pairs, 
				count_explicit_valid_nodes, count_explicit_valid_edges, count_valid_nodes, count_valid_edges);
#endif
#endif

#if ALIAS_STATISTICS_CONTAINER
			// g.print_access_paths (out_aliases);
			// pcount = count_map_size (out_ap_alias_set);
                        // RESULT ("\n\tOUT All=%d", pcount);
			// unlabeled_edges::print_ap_alias_set (out_ap_alias_set);
			// g.print_root_aliases (out_block_root_aliases);
			// g.print_aliases (out_block_aliases);
			// g.print_reachable_roots (out_block_reachable_roots);
			// count_ap_alias_set += pcount;

                        ////////////////////////////////////////////////////////////////////////////

                        // NON_TEMP ALL program points
                        // unlabeled_edges::get_non_temp_ap_alias_set (out_ap_alias_set, out_ap_alias_set_non_temp);
			pcount = 0;
			count_map_size (out_ap_alias_set_non_temp, pcount, num_tot_ap);
                        count_ap_alias_set_non_temp += pcount;
                        RESULT ("\n\tOUT Non-temp=%d", pcount);
                        unlabeled_edges::print_ap_alias_set (out_ap_alias_set_non_temp);

			// out_ap_alias_set.clear ();
			// map<list<label>, set<list<label> > >().swap (out_ap_alias_set); 
			// out_ap_alias_set = map<list<label>, set<list<label> > >();

			merge_map (out_ap_alias_set_non_temp, unique_ap_alias_set_non_temp);

			// out_ap_alias_set_non_temp.clear ();
			// map<list<label>, set<list<label> > >().swap (out_ap_alias_set_non_temp); 
			out_ap_alias_set_non_temp = map<list<label>, set<list<label> > >();
#endif

#if POINTS_TO
			// Copy all edges from in/out_block_points_to_pairs to program_points_to_pairs
			map<label, set<label> >::iterator pi;
			for (pi = in_block_points_to_pairs.begin (); 
				pi != in_block_points_to_pairs.end (); 
				pi++)
			{
				label src = pi->first;
				set<label> dests = pi->second;
				program_points_to_pairs[src].insert (dests.begin (), dests.end ());
				dests.erase (undef_id);
				tot_program_points_to_pairs += dests.size ();
			}
			for (pi = out_block_points_to_pairs.begin (); 
				pi != out_block_points_to_pairs.end (); 
				pi++)
			{
				label src = pi->first;
				set<label> dests = pi->second;
				program_points_to_pairs[src].insert (dests.begin (), dests.end ());
				dests.erase (undef_id);
				tot_program_points_to_pairs += dests.size ();
			}
#endif
		}

		// DEBUG ("\nfunction=%s use-points=%d", function_name, function_use_points);
		// program_use_points[function->uid] = function_use_points;
	}

	RESULT ("\n------------\n");
	int unique_program_points_to_pairs = 0;
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
	RESULT ("\nTotal heap_to_stack program points-to pairs=%d",
		heap_to_stack_pointers);
#endif

	map<label, set<label> > heap_to_stack_program_pointers;
	unlabeled_edges::print_points_to_pairs (program_points_to_pairs, heap_to_stack_pointees);
#if SUMM_K_CONSISTENT
        RESULT ("\nTotal heap_to_stack pointees=%d", heap_to_stack_pointees.size ());
#endif

//	pcount = count_map_size (unique_ap_alias_set);
//	RESULT ("\nUnique program ap alias set=%d", pcount);
//	unlabeled_edges::print_ap_alias_set (unique_ap_alias_set);

	unsigned int pcount_non_temp = 0, num_unique_ap = 0;
	count_map_size (unique_ap_alias_set_non_temp, pcount_non_temp, num_unique_ap);
//	unlabeled_edges::get_non_temp_ap_alias_set (unique_ap_alias_set, unique_ap_alias_set_non_temp);
	RESULT ("\nUnique (non-temp) program ap alias set=%d", pcount_non_temp);
	unlabeled_edges::print_ap_alias_set (unique_ap_alias_set_non_temp);

#if 0
	unsigned int use_points = 0;
	map<function_index, unsigned int>::iterator ui;
	for (ui = program_use_points.begin (); ui != program_use_points.end (); ui++)
		use_points += ui->second;
	RESULT ("\nTotal use points = %d", use_points);

	RESULT ("\nGraph with maximum |N+E| has num_nodes=%d, avg_out_edges=%.2f",
		max_num_nodes, max_avg_out_edges);
	unlabeled_edges g;
	g.print_aliases (program_aliases);
#endif

//      print_original_gcc_points_to_pairs ();
	program.print_statistics ();

	INFO ("\n");
	// RESULT ("\nmax_acyclic_ap_len=%d\n", max_acyclic_ap_len);
        RESULT ("\nTotal ap alias set=%d", count_ap_alias_set);
        RESULT ("\nTotal program blocks=%d", program_blocks);
	RESULT ("\nFunction count=%d", function_count);
        RESULT ("\nTotal value contexts=%d", contexts_count);
	RESULT ("\nAvg contexts per function=%f", (float) contexts_count / function_count);
	RESULT ("\nMax contexts per function=%d", max_contexts_per_function);
	RESULT ("\nTotal explicit valid nodes=%d", count_explicit_valid_nodes);
	RESULT ("\nTotal explicit valid edges=%d", count_explicit_valid_edges);
	RESULT ("\nTotal valid nodes=%d", count_valid_nodes);
	RESULT ("\nTotal valid edges=%d", count_valid_edges);
	RESULT ("\nAvg explicit valid nodes per program point=%f", (float) count_explicit_valid_nodes / (program_blocks*2));
	RESULT ("\nAvg explicit valid edges per program point=%f", (float) count_explicit_valid_edges / (program_blocks*2));
	RESULT ("\nAvg valid nodes per program point=%f", (float) count_valid_nodes / (program_blocks*2));
	RESULT ("\nAvg valid edges per program point=%f", (float) count_valid_edges / (program_blocks*2));
	RESULT ("\ntot_update_points where stmttouch=%d", tot_update_points);
	RESULT ("\nAvg stmttouch per program point=%f", (float) tot_stmttouch / tot_update_points);
        RESULT ("\nTotal ap alias set non-temp=%d", count_ap_alias_set_non_temp);
        RESULT ("\nTotal useful ap alias set=%d", count_useful_ap_alias_set);
        RESULT ("\nTotal useful ap alias set non-temp=%d", count_useful_ap_alias_set_non_temp);
        RESULT ("\nTotal useful program blocks=%d", useful_program_blocks);
	RESULT ("\nnum_unique_ap=%d", num_unique_ap);
	RESULT ("\nnum_tot_ap=%d", num_tot_ap);
	RESULT ("\nnum_useful_ap=%d", num_useful_ap);

	FILE * stat_file = fopen (STAT_FILE, "a");
	fprintf (stat_file, "\nALLOC_BASED,L=%d", MAX_LEN_PRINT);
	fprintf (stat_file, "\nTotal program blocks=%d", program_blocks);
	fprintf (stat_file, "\nFunction count=%d", function_count);
        fprintf (stat_file, "\nTotal value contexts=%d", contexts_count);
	fprintf (stat_file, "\nAvg contexts per function=%f", (float) contexts_count / function_count);
	fprintf (stat_file, "\nMax contexts per function=%d", max_contexts_per_function);
	fprintf (stat_file, "\nTotal explicit valid nodes=%d", count_explicit_valid_nodes);
	fprintf (stat_file, "\nTotal explicit valid edges=%d", count_explicit_valid_edges);
	fprintf (stat_file, "\nTotal valid nodes=%d", count_valid_nodes);
	fprintf (stat_file, "\nTotal valid edges=%d", count_valid_edges);
	fprintf (stat_file, "\nAvg explicit valid nodes per program point=%f", (float) count_explicit_valid_nodes / (program_blocks*2));
	fprintf (stat_file, "\nAvg explicit valid edges per program point=%f", (float) count_explicit_valid_edges / (program_blocks*2));
	fprintf (stat_file, "\nAvg valid nodes per program point=%f", (float) count_valid_nodes / (program_blocks*2));
	fprintf (stat_file, "\nAvg valid edges per program point=%f", (float) count_valid_edges / (program_blocks*2));
	fprintf (stat_file, "\ntot_update_points where stmttouch=%d", tot_update_points);
	fprintf (stat_file, "\nAvg affected nodes per program point=%f", (float) tot_stmttouch / tot_update_points);
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

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
dump_analysis (map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> > & function_contexts)
{
	FILE * edge_file_ptr = fopen (EDGE_FILE, "w");
	FILE * unique_edge_file_ptr = fopen (UNIQUE_EDGE_FILE, "w");
	FILE * heap_file_ptr = fopen (HEAP_FILE, "w");
	FILE * useful_ap_file_ptr = fopen (USEFUL_AP_FILE, "w");
	fprintf (edge_file_ptr, "\n");
	fprintf (unique_edge_file_ptr, "\n");
	fprintf (heap_file_ptr, "\n");
	fprintf (useful_ap_file_ptr, "\n");
	fclose (edge_file_ptr);
	fclose (unique_edge_file_ptr);
	fclose (heap_file_ptr);
	fclose (useful_ap_file_ptr);
	edge_file_ptr = fopen (EDGE_FILE, "a");
	unique_edge_file_ptr = fopen (UNIQUE_EDGE_FILE, "a");
	heap_file_ptr = fopen (HEAP_FILE, "a");
	useful_ap_file_ptr = fopen (USEFUL_AP_FILE, "a");

	set<map<label, map<label, set<label> > > > unique_points_to_graphs;

	// We use FUNCTION_CONTEXTS_MAP instead of PROGRAM_CONTEXTS of
	// inter_procedural_analysis.hh so that the statistics are printed in
	// order of functions. This makes it easier to compare to files of
	// statistics.
	typename map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> >::iterator fi;
	for (fi = function_contexts.begin (); fi != function_contexts.end (); fi++)
	{
		struct cgraph_node * function = program.get_cgraph_node (fi->first);
		const char * function_name = cgraph_node_name (function);
		RESULT ("\nFunction %s", function_name);
		struct function * function_decl = DECL_STRUCT_FUNCTION (function->decl);

		context_enums<unlabeled_edges, LIVE_VALUE_TYPE> contexts = fi->second;

		basic_block block;
		FOR_EACH_BB_FN (block, function_decl)
		{
			// Compute meet of all the contexts for this basic block

			typename context_enums<unlabeled_edges, LIVE_VALUE_TYPE>::iterator ci;
			for (ci = contexts.begin (); ci != contexts.end (); ci++)
			{
				context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context =
					ci->second;
				// In value
#if GC_ON_THE_FLY
				unlabeled_edges etemp;
				unlabeled_edges * e = &etemp;
#else
				unlabeled_edges * e = current_context->get_in_value (block);
				// Add memoized pta graph of called context
				restore_unaffected_context_dept_pta (*current_context, *e);
#endif
				if (!e)
				{
					RESULT ("\nError: in value of block=%d is NULL", block->index);
					continue;
				}
				e->dump_data_flow_value (fi->first, block->index, 0, 
					edge_file_ptr, heap_file_ptr, 
					unique_edge_file_ptr, unique_points_to_graphs);

				// Propagate only function_par_defs and callees_global_defs
				remove_unaffected_context_dept_pta (*current_context, *e);
			}
			dump_useful_aps (fi->first, block, useful_ap_file_ptr);

			for (ci = contexts.begin (); ci != contexts.end (); ci++)
			{
				context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context =
					ci->second;
				// Out value
#if GC_ON_THE_FLY
				unlabeled_edges etemp;
				unlabeled_edges * e = &etemp;
#else
				unlabeled_edges * e = current_context->get_out_value (block);
				// Add memoized pta graph of called context
				restore_unaffected_context_dept_pta (*current_context, *e);
#endif
				if (!e)
				{
					RESULT ("\nError: out value of block=%d is NULL", block->index);
					continue;
				}
				e->dump_data_flow_value (fi->first, block->index, 1, 
					edge_file_ptr, heap_file_ptr, 
					unique_edge_file_ptr, unique_points_to_graphs);

				// Propagate only function_par_defs and callees_global_defs
				remove_unaffected_context_dept_pta (*current_context, *e);
			}
		}
	}

	// Print empty line to denote end of context
	fprintf (edge_file_ptr, "\n");
	fprintf (unique_edge_file_ptr, "\n");

	fclose (edge_file_ptr);
	fclose (unique_edge_file_ptr);
	fclose (heap_file_ptr);
	fclose (useful_ap_file_ptr);
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_dead_locals_stats ()
{
#if ALLOC_STATISTICS_CONTAINER
#if DEBUG_CONTAINER
	set<label>::iterator vi;
	DEBUG ("\ndead_locals_pta=");
	for (vi = dead_locals_stats.dead_locals_pta.begin (); 
		vi != dead_locals_stats.dead_locals_pta.end (); 
		vi++)
	{	
		csvarinfo_t var = program.cs_get_varinfo (*vi);
		DEBUG ("%s(%d),", var->name, var->id);
	}
	DEBUG ("\ndead_locals_pp=");
	for (vi = dead_locals_stats.dead_locals_pp.begin (); 
		vi != dead_locals_stats.dead_locals_pp.end (); 
		vi++)
	{	
		csvarinfo_t var = program.cs_get_varinfo (*vi);
		DEBUG ("%s(%d),", var->name, var->id);
	}
	DEBUG ("\nlive_locals_pp=");
	for (vi = dead_locals_stats.live_locals_pp.begin (); 
		vi != dead_locals_stats.live_locals_pp.end (); 
		vi++)
	{	
		csvarinfo_t var = program.cs_get_varinfo (*vi);
		DEBUG ("%s(%d),", var->name, var->id);
	}
#endif

	RESULT ("\ntot_dead_locals_pta=%d, tot_dead_locals_pp=%d, tot_live_locals_pp=%d, tot_filterings=%d",
		dead_locals_stats.tot_dead_locals_pta, 
		dead_locals_stats.tot_dead_locals_pp, 
		dead_locals_stats.tot_live_locals_pp, 
		dead_locals_stats.tot_filterings);
	RESULT ("\nunique_dead_locals_pta=%d, unique_dead_locals_pp=%d, unique_live_locals=%d",
		dead_locals_stats.dead_locals_pta.size (), 
		dead_locals_stats.dead_locals_pp.size (), 
		dead_locals_stats.live_locals_pp.size ());

	FILE * stat_file = fopen (STAT_FILE, "a");
	fprintf (stat_file, "\ntot_dead_locals_pta=%d, tot_dead_locals_pp=%d, tot_live_locals_pp=%d, tot_filterings=%d",
		dead_locals_stats.tot_dead_locals_pta, 
		dead_locals_stats.tot_dead_locals_pp, 
		dead_locals_stats.tot_live_locals_pp, 
		dead_locals_stats.tot_filterings);
	fprintf (stat_file, "\nunique_dead_locals_pta=%d, unique_dead_locals_pp=%d, unique_live_locals=%d",
		dead_locals_stats.dead_locals_pta.size (), 
		dead_locals_stats.dead_locals_pp.size (), 
		dead_locals_stats.live_locals_pp.size ());
	fclose (stat_file);


	dead_locals_stats.dead_locals_pta.clear ();
	dead_locals_stats.dead_locals_pp.clear ();
	dead_locals_stats.live_locals_pp.clear ();
#endif
}

template <class LIVE_VALUE_TYPE>
unlabeled_edges * allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_pts_context_indept_value (context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context)
{
        unaffected_pta * aux = (unaffected_pta *) current_context->get_aux_info ();
        if (!aux)
        {
                RESULT ("\nError: aux (unaffected context_dept value) is NULL");
                return NULL;
        }

        unlabeled_edges * context_indept_pta = &aux->context_indept;
	return context_indept_pta;
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
get_points_to_in_value (context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context, 
        basic_block current_block,
	unlabeled_edges & points_to_in)
{
        unaffected_pta * aux = (unaffected_pta *) current_context->get_aux_info ();
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

        // Get IN value + unaffected_context_indept_pta + unaffected_context_dept_pta
        unlabeled_edges * unaffected_context_indept_pta = &aux->context_indept;
        unlabeled_edges * unaffected_context_dept_pta = &aux->context_dept;
        unlabeled_edges * fs_context_dept_pta = current_context->get_in_value (current_block);

	if (unaffected_context_indept_pta)
	        points_to_in.copy_value (*unaffected_context_indept_pta, false);
	if (unaffected_context_dept_pta)
	        points_to_in.copy_value (*unaffected_context_dept_pta, false);
	if (fs_context_dept_pta)
	        points_to_in.copy_value (*fs_context_dept_pta, false);

#if DEBUG_CONTAINER
        DEBUG ("\nlink alias pta=");
        points_to_in.print_value (NULL);
#endif
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
print_bypassing_analysis_statistics (map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> > & function_contexts)
{
	INFO ("\nALLOC-BASED POINTS-TO PAIRS (bypassing)\n===============\n");

	unsigned int tot_context_indept_ptee_count = 0;
	unsigned int tot_context_indept_local_ptee_count = 0;
	unsigned int tot_context_indept_global_ptee_count = 0;
	unsigned int tot_context_indept_heap_ptee_count = 0;

	unsigned int unique_context_indept_ptee_count = 0;
	unsigned int unique_context_indept_local_ptee_count = 0;
	unsigned int unique_context_indept_global_ptee_count = 0;
	unsigned int unique_context_indept_heap_ptee_count = 0;

	unsigned int tot_context_indept_ptr_count = 0;
	unsigned int tot_context_indept_local_ptr_count = 0;
	unsigned int tot_context_indept_global_ptr_count = 0;
	unsigned int tot_context_indept_heap_ptr_count = 0;

	unsigned int unique_context_indept_ptr_count = 0;
	unsigned int unique_context_indept_local_ptr_count = 0;
	unsigned int unique_context_indept_global_ptr_count = 0;
	unsigned int unique_context_indept_heap_ptr_count = 0;

	map<label, set<label> > program_context_indept_points_to_pairs;

	// We use FUNCTION_CONTEXTS_MAP instead of PROGRAM_CONTEXTS of
	// inter_procedural_analysis.hh so that the statistics are printed in
	// order of functions. This makes it easier to compare to files of
	// statistics.
	typename map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> >::iterator fi;
	for (fi = function_contexts.begin (); fi != function_contexts.end (); fi++)
	{
		struct cgraph_node * function = program.get_cgraph_node (fi->first);
		const char * function_name = cgraph_node_name (function);
		RESULT ("\nFunction %s", function_name);
		struct function * function_decl = DECL_STRUCT_FUNCTION (function->decl);

		context_enums<unlabeled_edges, LIVE_VALUE_TYPE> contexts = fi->second;

		unsigned int function_use_points = 0;
		map<label, set<label> > context_indept_points_to_pairs;

		// Compute meet of all the contexts for this basic block

		typename context_enums<unlabeled_edges, LIVE_VALUE_TYPE>::iterator ci;
		for (ci = contexts.begin (); ci != contexts.end (); ci++)
		{
			context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context =
				ci->second;
			DEBUG ("\ncontext=%d", current_context->get_context_id ());

			///////////////////////////////////////////////////////////////////////////

			unlabeled_edges * g_context_indept = get_pts_context_indept_value (current_context);
			if (!g_context_indept)
				continue;
			g_context_indept->get_graph_statistics (context_indept_points_to_pairs);
			g_context_indept->get_graph_statistics (program_context_indept_points_to_pairs);
			unsigned int context_indept_ptee_count = 0;
			unsigned int context_indept_local_ptee_count = 0;
			unsigned int context_indept_global_ptee_count = 0;
			unsigned int context_indept_heap_ptee_count = 0;
			unsigned int context_indept_ptr_count = 0;
			unsigned int context_indept_local_ptr_count = 0;
			unsigned int context_indept_global_ptr_count = 0;
			unsigned int context_indept_heap_ptr_count = 0;
			unlabeled_edges::get_points_to_pairs_statistics (context_indept_points_to_pairs,
				context_indept_ptee_count,		
				context_indept_local_ptee_count,
				context_indept_global_ptee_count,
				context_indept_heap_ptee_count,
				context_indept_ptr_count,
				context_indept_local_ptr_count,
				context_indept_global_ptr_count,
				context_indept_heap_ptr_count);
			tot_context_indept_ptee_count += context_indept_ptee_count;
			tot_context_indept_local_ptee_count += context_indept_local_ptee_count;
			tot_context_indept_global_ptee_count += context_indept_global_ptee_count;
			tot_context_indept_heap_ptee_count += context_indept_heap_ptee_count;
			tot_context_indept_ptr_count += context_indept_ptr_count;
			tot_context_indept_local_ptr_count += context_indept_local_ptr_count;
			tot_context_indept_global_ptr_count += context_indept_global_ptr_count;
			tot_context_indept_heap_ptr_count += context_indept_heap_ptr_count;

			RESULT ("\n    context=%d, context_indept=", current_context->get_context_id ());
			unlabeled_edges::print_points_to_pairs (context_indept_points_to_pairs);
		}
	}

	unlabeled_edges::get_points_to_pairs_statistics (program_context_indept_points_to_pairs,
		unique_context_indept_ptee_count,
		unique_context_indept_local_ptee_count,
		unique_context_indept_global_ptee_count,
		unique_context_indept_heap_ptee_count,
		unique_context_indept_ptr_count,
		unique_context_indept_local_ptr_count,
		unique_context_indept_global_ptr_count,
		unique_context_indept_heap_ptr_count);
	RESULT ("\n\nprogram unique context_indept=");
	unlabeled_edges::print_points_to_pairs (program_context_indept_points_to_pairs);

	RESULT ("\nTotal context_indept pointees, pointers: tot=%d, local=%d, global=%d, heap=%d, tot=%d, local=%d, global=%d, heap=%d",
		tot_context_indept_ptee_count,
		tot_context_indept_local_ptee_count,
		tot_context_indept_global_ptee_count,
		tot_context_indept_heap_ptee_count,
		tot_context_indept_ptr_count,
		tot_context_indept_local_ptr_count,
		tot_context_indept_global_ptr_count,
		tot_context_indept_heap_ptr_count);
	RESULT ("\nUnique context_indept pointees, ptrs: unique=%d, local=%d, global=%d, heap=%d, unique=%d, local=%d, global=%d, heap=%d",
		unique_context_indept_ptee_count,
		unique_context_indept_local_ptee_count,
		unique_context_indept_global_ptee_count,
		unique_context_indept_heap_ptee_count,
		unique_context_indept_ptr_count,
		unique_context_indept_local_ptr_count,
		unique_context_indept_global_ptr_count,
		unique_context_indept_heap_ptr_count);

	FILE * stat_file = fopen (STAT_FILE, "a");
	fprintf (stat_file, "\nTotal context_indept pointees, pointers: tot=%d, local=%d, global=%d, heap=%d, tot=%d, local=%d, global=%d, heap=%d",
		tot_context_indept_ptee_count,
		tot_context_indept_local_ptee_count,
		tot_context_indept_global_ptee_count,
		tot_context_indept_heap_ptee_count,
		tot_context_indept_ptr_count,
		tot_context_indept_local_ptr_count,
		tot_context_indept_global_ptr_count,
		tot_context_indept_heap_ptr_count);
	fprintf (stat_file, "\nUnique context_indept pointees, ptrs: unique=%d, local=%d, global=%d, heap=%d, unique=%d, local=%d, global=%d, heap=%d",
		unique_context_indept_ptee_count,
		unique_context_indept_local_ptee_count,
		unique_context_indept_global_ptee_count,
		unique_context_indept_heap_ptee_count,
		unique_context_indept_ptr_count,
		unique_context_indept_local_ptr_count,
		unique_context_indept_global_ptr_count,
		unique_context_indept_heap_ptr_count);

	fclose (stat_file);
}

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
print_analysis_statistics (map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> > & function_contexts)
{
#if ALLOC_STATISTICS_CONTAINER
	INFO ("\nALLOC-BASED USED POINTS-TO PAIRS\n===============\n");

	unsigned int max_num_nodes = 0;
	float max_avg_out_edges = 0;
	unsigned int tot_program_ptee_count = 0;
	unsigned int tot_program_local_ptee_count = 0;
	unsigned int tot_program_global_ptee_count = 0;
	unsigned int tot_program_heap_ptee_count = 0;

	unsigned int tot_program_ptr_count = 0;
	unsigned int tot_program_local_ptr_count = 0;
	unsigned int tot_program_global_ptr_count = 0;
	unsigned int tot_program_heap_ptr_count = 0;

	map<label, set<label> > program_points_to_pairs;
	map<label, set<label> > used_points_to_pairs;
	map<context_index, map<label, set<label> > > context_used_points_to_pairs;

	unsigned int program_blocks = 0;
	unsigned int heap_to_stack_pointers = 0;
	unsigned int contexts_count = 0;
	unsigned int function_count = 0;
	unsigned int max_contexts_per_function = 0;
	unsigned int count_reuses = 0;
	unsigned int max_reuses = 0;

	// We use FUNCTION_CONTEXTS_MAP instead of PROGRAM_CONTEXTS of
	// inter_procedural_analysis.hh so that the statistics are printed in
	// order of functions. This makes it easier to compare to files of
	// statistics.
	typename map<function_index, context_enums<unlabeled_edges, LIVE_VALUE_TYPE> >::iterator fi;
	for (fi = function_contexts.begin (); fi != function_contexts.end (); fi++)
	{
		struct cgraph_node * function = program.get_cgraph_node (fi->first);
		const char * function_name = cgraph_node_name (function);
		RESULT ("\nFunction %s", function_name);
		struct function * function_decl = DECL_STRUCT_FUNCTION (function->decl);

		context_enums<unlabeled_edges, LIVE_VALUE_TYPE> contexts = fi->second;
		contexts_count += contexts.size ();
		function_count++;
		if (max_contexts_per_function < contexts.size ())
			max_contexts_per_function = contexts.size ();

		bool collected_context_indept = false;

		unsigned int function_use_points = 0;
		basic_block block;
		FOR_EACH_BB_FN (block, function_decl)
		{
			program_blocks++;

			unsigned int block_id = block->index;
			map<label, set<label> > in_block_points_to_pairs;

			// Compute meet of all the contexts for this basic block

			typename context_enums<unlabeled_edges, LIVE_VALUE_TYPE>::iterator ci;
			for (ci = contexts.begin (); ci != contexts.end (); ci++)
			{
				context<unlabeled_edges, LIVE_VALUE_TYPE> * current_context =
					ci->second;
				context_index cid = current_context->get_context_id ();
				DEBUG ("\nbb=%d,context=%d", block->index, cid);

				///////////////////////////////////////////////////////////////////////////

				// In value
				DEBUG ("\nget_graph_statistics in");
				unlabeled_edges g_in;
				get_points_to_in_value (current_context, block, g_in);
				DEBUG ("\ndone get_points_to_in_value");
				g_in.get_graph_statistics (in_block_points_to_pairs);
				DEBUG ("\ndone get_graph_statistics in");
				g_in.get_graph_statistics (program_points_to_pairs);
				DEBUG ("\ndone get_graph_statistics program");

				////////////////////////////////////////////////////////////////////////////

				map<label, set<label> > context_in_block_points_to_pairs;
				g_in.get_graph_statistics (context_in_block_points_to_pairs);
				unlabeled_edges::get_used_points_to_pairs (context_in_block_points_to_pairs, 
					block, context_used_points_to_pairs[cid]);

				////////////////////////////////////////////////////////////////////////////

				if (collected_context_indept)
					continue;

				///////////////////////////////////////////////////////////////////////////

	                        int curr_reuses = current_context->get_source_contexts ().size ();
       		                count_reuses += curr_reuses;
                        	if (max_reuses < curr_reuses)
                                	max_reuses = curr_reuses;
				RESULT ("\n\tcontext=%d curr_reuses=%d", current_context->get_context_id (), curr_reuses);

				///////////////////////////////////////////////////////////////////////////

				// Out value

				///////////////////////////////////////////////////////////////////////////
			}

			collected_context_indept = true;

			////////////////////////////////////////////////////////////////////////////

		
			RESULT ("\n    in-bb=%d", block_id);
			// unlabeled_edges::print_points_to_pairs (in_block_points_to_pairs);
			RESULT ("\n\t\t---------------------USED----------------------------");
			unlabeled_edges::print_used_points_to_pairs (in_block_points_to_pairs, block);
			unlabeled_edges::get_used_points_to_pairs (in_block_points_to_pairs, block, used_points_to_pairs);

			// Analyze in_block_points_to_pairs
			unsigned int in_block_ptee_count = 0;
			unsigned int in_block_local_ptee_count = 0;
			unsigned int in_block_global_ptee_count = 0;
			unsigned int in_block_heap_ptee_count = 0;
			unsigned int in_block_ptr_count = 0;
			unsigned int in_block_local_ptr_count = 0;
			unsigned int in_block_global_ptr_count = 0;
			unsigned int in_block_heap_ptr_count = 0;

			unlabeled_edges::get_points_to_pairs_statistics (in_block_points_to_pairs,
				in_block_ptee_count,
				in_block_local_ptee_count,
				in_block_global_ptee_count,
				in_block_heap_ptee_count,
				in_block_ptr_count,
				in_block_local_ptr_count,
				in_block_global_ptr_count,
				in_block_heap_ptr_count);
			tot_program_ptee_count += in_block_ptee_count;
			tot_program_local_ptee_count += in_block_local_ptee_count;
			tot_program_global_ptee_count += in_block_global_ptee_count;
			tot_program_heap_ptee_count += in_block_heap_ptee_count;
			tot_program_ptr_count += in_block_ptr_count;
			tot_program_local_ptr_count += in_block_local_ptr_count;
			tot_program_global_ptr_count += in_block_global_ptr_count;
			tot_program_heap_ptr_count += in_block_heap_ptr_count;

			////////////////////////////////////////////////////////////////////////////

		}
	}

	unsigned int unique_program_ptee_count = 0;
	unsigned int unique_program_local_ptee_count = 0;
	unsigned int unique_program_global_ptee_count = 0;
	unsigned int unique_program_heap_ptee_count = 0;

	unsigned int unique_program_ptr_count = 0;
	unsigned int unique_program_local_ptr_count = 0;
	unsigned int unique_program_global_ptr_count = 0;
	unsigned int unique_program_heap_ptr_count = 0;

	RESULT ("\n------------\n");
	unlabeled_edges::get_points_to_pairs_statistics (program_points_to_pairs,
		unique_program_ptee_count,
		unique_program_local_ptee_count,
		unique_program_global_ptee_count,
		unique_program_heap_ptee_count,
		unique_program_ptr_count,
		unique_program_local_ptr_count,
		unique_program_global_ptr_count,
		unique_program_heap_ptr_count);

	unsigned int unique_used_ptee_count = 0;
	unsigned int unique_used_local_ptee_count = 0;
	unsigned int unique_used_global_ptee_count = 0;
	unsigned int unique_used_heap_ptee_count = 0;

	unsigned int unique_used_ptr_count = 0;
	unsigned int unique_used_local_ptr_count = 0;
	unsigned int unique_used_global_ptr_count = 0;
	unsigned int unique_used_heap_ptr_count = 0;

	unlabeled_edges::get_points_to_pairs_statistics (used_points_to_pairs,
		unique_used_ptee_count,
		unique_used_local_ptee_count,
		unique_used_global_ptee_count,
		unique_used_heap_ptee_count,
		unique_used_ptr_count,
		unique_used_local_ptr_count,
		unique_used_global_ptr_count,
		unique_used_heap_ptr_count);

	float avg_context_ptr_used_ptees = 0.0;
	float avg_context_local_ptr_used_ptees = 0.0;
	float avg_context_global_ptr_used_ptees = 0.0;
	float avg_context_heap_ptr_used_ptees = 0.0;

	unlabeled_edges::get_context_used_points_to_pairs_statistics (context_used_points_to_pairs,
		avg_context_ptr_used_ptees,
		avg_context_local_ptr_used_ptees,
		avg_context_global_ptr_used_ptees,
		avg_context_heap_ptr_used_ptees);

	RESULT ("\nTotal program pointees, pointers: tot=%d, local=%d, global=%d, heap=%d, tot=%d, local=%d, global=%d, heap=%d",
		tot_program_ptee_count,
		tot_program_local_ptee_count,
		tot_program_global_ptee_count,
		tot_program_heap_ptee_count,
		tot_program_ptr_count,
		tot_program_local_ptr_count,
		tot_program_global_ptr_count,
		tot_program_heap_ptr_count);
	RESULT ("\nUnique program pointees, pointers: unique=%d, local=%d, global=%d, heap=%d, unique=%d, local=%d, global=%d, heap=%d",
		unique_program_ptee_count,
		unique_program_local_ptee_count,
		unique_program_global_ptee_count,
		unique_program_heap_ptee_count,
		unique_program_ptr_count,
		unique_program_local_ptr_count,
		unique_program_global_ptr_count,
		unique_program_heap_ptr_count);
	RESULT ("\nUnique used pointees, pointers: unique=%d, local=%d, global=%d, heap=%d, unique=%d, local=%d, global=%d, heap=%d",
		unique_used_ptee_count,
		unique_used_local_ptee_count,
		unique_used_global_ptee_count,
		unique_used_heap_ptee_count,
		unique_used_ptr_count,
		unique_used_local_ptr_count,
		unique_used_global_ptr_count,
		unique_used_heap_ptr_count);
	RESULT ("\nUnique used pointees per pointer per context: unique=%f, local=%f, global=%f, heap=%f",
		avg_context_ptr_used_ptees,
		avg_context_local_ptr_used_ptees,
		avg_context_global_ptr_used_ptees,
		avg_context_heap_ptr_used_ptees);

	unlabeled_edges::print_points_to_pairs (program_points_to_pairs);

	program.print_statistics ();

	INFO ("\n");
        RESULT ("\nTotal program blocks=%d", program_blocks);
	RESULT ("\nFunction count=%d", function_count);
        RESULT ("\nTotal value contexts=%d", contexts_count);
	RESULT ("\nAvg contexts per function=%f", (float) contexts_count / function_count);
	RESULT ("\nMax contexts per function=%d", max_contexts_per_function);
        RESULT ("\ncontext: count_reuses = %d, avg_reuses=%f, max_reuses=%d",
        	count_reuses, (float) count_reuses / contexts_count, max_reuses);

	FILE * stat_file = fopen (STAT_FILE, "a");
	fprintf (stat_file, "\nTotal program pointees, pointers: tot=%d, local=%d, global=%d, heap=%d, tot=%d, local=%d, global=%d, heap=%d",
		tot_program_ptee_count,
		tot_program_local_ptee_count,
		tot_program_global_ptee_count,
		tot_program_heap_ptee_count,
		tot_program_ptr_count,
		tot_program_local_ptr_count,
		tot_program_global_ptr_count,
		tot_program_heap_ptr_count);
	fprintf (stat_file, "\nUnique program pointees, pointers: unique=%d, local=%d, global=%d, heap=%d, unique=%d, local=%d, global=%d, heap=%d",
		unique_program_ptee_count,
		unique_program_local_ptee_count,
		unique_program_global_ptee_count,
		unique_program_heap_ptee_count,
		unique_program_ptr_count,
		unique_program_local_ptr_count,
		unique_program_global_ptr_count,
		unique_program_heap_ptr_count);
	fprintf (stat_file, "\nUnique used pointees, pointers: unique=%d, local=%d, global=%d, heap=%d, unique=%d, local=%d, global=%d, heap=%d",
		unique_used_ptee_count,
		unique_used_local_ptee_count,
		unique_used_global_ptee_count,
		unique_used_heap_ptee_count,
		unique_used_ptr_count,
		unique_used_local_ptr_count,
		unique_used_global_ptr_count,
		unique_used_heap_ptr_count);
	fprintf (stat_file, "\nUnique used pointees per pointer per context: unique=%f, local=%f, global=%f, heap=%f",
		avg_context_ptr_used_ptees,
		avg_context_local_ptr_used_ptees,
		avg_context_global_ptr_used_ptees,
		avg_context_heap_ptr_used_ptees);

	fprintf (stat_file, "\nTotal program blocks=%d", program_blocks);
	fprintf (stat_file, "\nFunction count=%d", function_count);
        fprintf (stat_file, "\nTotal value contexts=%d", contexts_count);
	fprintf (stat_file, "\nAvg contexts per function=%f", (float) contexts_count / function_count);
	fprintf (stat_file, "\nMax contexts per function=%d", max_contexts_per_function);
        fprintf (stat_file, "\ncontext: count_reuses = %d, avg_reuses=%f, max_reuses=%d",
        	count_reuses, (float) count_reuses / contexts_count, max_reuses);

	fclose (stat_file);

	get_dead_locals_stats ();

	// ACCUMULATE CONTEXT-INDEPT values
	// Should we accumulate context-indept bypassed value to print it at
	// each program point? No not needed. Since we are printing only
	// lhs/rhs used/side-effected variables of a function, any accumulated
	// context-indept points-to pair will anyway not be printed.
#endif
}

/**
 * The client analysis can modify the control flow graph to use our
 * inter-procedural analysis, which assumes that each function call is the only
 * statement in a basic block. Also, each pointer statement is made the only
 * statement of a basic block for bi-directional inter-procedural analysis.
 */

template <class LIVE_VALUE_TYPE>
void allocation_site_based_analysis<LIVE_VALUE_TYPE>::
preprocess_and_parse_program ()
{
#if DEBUG_CONTAINER
	program.print_original_cfg ();
#endif

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

#if DEBUG_CONTAINER
	program.print_parsed_data ();
	// program.print_variable_data ();
	// program.print_assignment_data ();
	program.print_heap_to_alloc_site ();
#endif
}


template class allocation_site_based_analysis<variables>; 
template class allocation_site_based_analysis<deterministic_graph>; 
template class allocation_site_based_analysis<non_deterministic_graph>; 

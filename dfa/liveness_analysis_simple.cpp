
/************************
 * @author Vini Kanvar
************************/

#include "liveness_analysis_simple.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

// This file implements side effect analysis (b.1). It also implements
// intra-procedural (summary based) liveness, using is_value-context=true and
// passing return_value=NULL to the callee.  IS_VALUE_CONTEXT=true is required
// for side effect analysis.

//=============================================================================
// Liveness. Types of liveness.
// (a) Intra-procedural liveness.
// (b) Inter-procedural liveness.
//     (b.1) Live then Pta. 
//     (b.2) Pta then Live.
//           (b.2.1) Live roots and their access paths (not heap allocs).
//           (b.2.2) Live links in terms of heap allocs
//=============================================================================
// Liveness. Bypassing
// (a) No bypassing.
// (b.1) Implicit liveness not generated in callee as Pta unknown. For
//       soundness, statement level liveness is over-approx.
// (b.2.1) Implicit liveness generated in callee (using Pta).
// (b.2.2) Links indicate both explicit and implicit liveness.
//=============================================================================
// Liveness. Statements
// (a) Mark reachable (addr-taken) roots (implicit) as live. rhs is marked live
//     assuming reaching vars on lhs as live. 
// (b.1) x->f=rhs. Unconditionally mark rhs as live as pta unknown.
// (b.2.1) x->f=rhs. If lhs is live, mark rhs as live as pta known.
// (b.2.2) x->f=rhs. If lhs is live, mark rhs as live as pta known.
//=============================================================================
// Liveness. Pta after liveness i.e., pta based on this liveness.
// (a) In Pta, param/glob reachable vars are assumed live. 
// (b.1) In Pta, assume reaching and reachable (i.e. implicit) roots also
//       live.
// (b.2.1) In Pta, no need to assume reaching and reachable (i.e.
//         implicit) roots as live.
// (b.2.2) In Pta, pass live links only.
//=============================================================================
// (a) process_call_statement_indept(), process_assignment_statement_indept()
// (b.1) Too approx
// (b.2.1) Implemented in dfa/liveness_analysis_deterministic
// (b.2.2) process_call_statement_dept(), process_assignment_statement_dept()
//=============================================================================


liveness_analysis_simple::
liveness_analysis_simple (bool is_val_context) : 
	backward_inter_procedural_analysis (is_val_context)
{
}

liveness_analysis_simple::
~liveness_analysis_simple ()
{
	DEBUG ("\ngc liveness_analysis_simple");
	delete_context_aux_info ();
}

void liveness_analysis_simple::
delete_aux_info (void * aux_info)
{
	DEBUG ("\nliveness_analysis_simple::delete_aux_info()");
}

variables * liveness_analysis_simple::
boundary_value ()
{
	variables * vars = new variables;
	vars->gen_important_block ();
	return vars;
}

/* Returns the top data flow value of the lattice. 
 * This is the default data flow value.
 */

variables * liveness_analysis_simple::
initial_value ()
{
	return new variables;
}

/** Retrieves a value context at the called function if it exists, and returns the value
 *  after evaluation through the called function.
 *  If the value context does not exist at the called function, this function creates one,
 *  adds it to the set of contexts at the called function, and returns the TOP value (as 
 *  the evaluated value of the new created context, since this has not yet been evaluated).
 */

void liveness_analysis_simple::
process_call_statement (context<variables, PT_VALUE_TYPE> * src_context, basic_block call_site)
{
	struct timeval start;
	start_timer (start);

#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif

	if (!src_context)
		RESULT ("\nError: Current context is NULL\n");

	unsigned int block_type = ((block_information *)(call_site->aux))->get_block_type ();
	if (block_type & AUX_BLOCK)
	{
		copy_out_to_in (src_context, call_site);
		return;
	}

	set<struct cgraph_node *> dest_functions = get_called_functions (*src_context, call_site);
	if (!dest_functions.size ())
	{
		RESULT ("\nError: Did not find called/destination function");
		// Process parsed information to deal with statements
		// formal-params:=actual-params and to make function pointers
		// (used in a function call) as live.
		// process_parsed_data (src_context, call_site, NULL);
		// src_context->set_in_value (call_site, initial_value ());

		DEBUG ("\nDid not find called/destination function");
		stop_timer (start, backward_process_call_statement_stats);
		return;
	}

	// Iterate over all functions pointed by a function pointer.
	set<struct cgraph_node *>::iterator fi;
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
		// returned variable. Therefore, a different copy of
		// return_value should be passed.

		variables * out_value = src_context->get_out_value (call_site);
		DEBUG ("\nout_value->copy_value()");
		variables out_value_copy;
		out_value_copy.copy_value (*out_value, false);
#if DEBUG_CONTAINER
		DEBUG ("\nout_value_copy of function call (before return-receive mapping)");
		out_value_copy.print_value (NULL);
#endif

		// Map returned value to receiving value.
		// process_return_value() does not kill the previous liveness of
		// the returned variable (rhs) which was computed from the
		// previous called function (via function pointer).

		bool to_kill = false;
		// Kill if there is only one function call.
		if (dest_functions.size () == 1)
			to_kill = true;
		process_return_value (src_context, call_site, &out_value_copy, dest_function, to_kill);

#if INTERMEDIATE_RESULT
		RESULT ("\nout_value + return mapping of function %s",
			cgraph_node_name (dest_function));
		out_value_copy.print_value (NULL);
#endif

		// Bypass locals that do not belong to callee. Since, this is
		// greedy liveness of only root variables, we need not pass
		// addr-taken locals to callee.

		// Extract arg_ret_glob_reachable value from out_value_copy and
		// not in_value_copy. 

		// Since we are computing summary based liveness, do not
		// extract any live_vars (except return variable of called
		// function) from OUT_VALUE_COPY. Since side effect analysis
		// does not pass any defs/uses from called function, do not
		// extract any callee_global_defs/uses.
	
		struct cgraph_node * src_function = src_context->get_function ();
		variables * arg_ret_glob_reachable_value =
			extract_arg_ret_glob_reachable_value (src_function, call_site, dest_function, out_value_copy);
		variables * return_value = arg_ret_glob_reachable_value;
#if INTERMEDIATE_RESULT
		RESULT ("\nout_value_copy left with arg_ret_glob-unreachable nodes");
		out_value_copy.print_value (NULL);
		RESULT ("\nreturn_value function %s", cgraph_node_name (dest_function));
		return_value->print_value (NULL);
#endif
		// return var of called function is over-approximately marked
		// live at OUT(1), IN(1), and OUT of return block of called
		// function. But anyway, we do not kill dead vars at these
		// program points in points-to analysis.

		// Process called context
		variables * function_in_value =
			process_destination_context (*src_context, call_site, dest_function, return_value);

		if (!function_in_value)
		{
			DEBUG ("\n!function_in_value");
			continue;
		}

		// FUNCTION_IN_VALUE belongs to START block of called function.
		// It should not be modified. Work on its copy.
		variables function_in_value_copy;
		function_in_value_copy.copy_value (*function_in_value, false);

		// Map actual parameters to formal parameters
		// Parameters are anyway not global. So they are not added to
		// callee_global_defs/uses. All addr-taken locals of callee
		// function are added by rhs (args).
		process_function_arguments (src_context, call_site, &function_in_value_copy, dest_function);
#if DEBUG_CONTAINER
		DEBUG ("\nreturn_value + argument_mapping of function %s",
			cgraph_node_name (dest_function));
		function_in_value_copy.print_value (NULL);
#endif

		// In summary based liveness, globals are anyway not marked.
		// Therefore, we do not want any live_vars from called
		// function. We want all callee_global_defs/uses of callee.
		delete_local_variables (src_context->get_function (), dest_function, function_in_value_copy, NULL);
#if DEBUG_CONTAINER
		DEBUG ("\ndelete_local_variables:");
		function_in_value_copy.print_value (NULL);
#endif

		initialize_in_value (src_context, call_site);

		// Rohan Padhye: OUT = IN_succ U OUT. Take self-meet to ensure
		// monotonic results. 
		// Create a copy of FUNCTION_IN_VALUE to IN of call-site. 
		DEBUG ("\nfunction_in_value->copy_value() to in_value");
		variables * in_value = src_context->get_in_value (call_site);
		in_value->copy_value (function_in_value_copy, false);

		// Copy arg_ret_glob_unreachable value to in_value.
		DEBUG ("\nCopying arg_ret_glob-unreachable value to in");
		DEBUG ("\nout_value->copy_value() to in_value");
		in_value->copy_value (out_value_copy, false);

		// Keep an OR of important_blocks if there are multiple
		// function callees. Else, do not take OR with out_value_copy
		// and set it as it is in function_in_value.
		if (to_kill)
			// Set in_value = function_in_value in terms of
			// important_block
			function_in_value->transfer_important_block (*in_value);
	}

	stop_timer (start, backward_process_call_statement_stats);
}

void liveness_analysis_simple::
initialize_in_value (context<variables, PT_VALUE_TYPE> * src_context, 
	basic_block call_site)
{
	// Initialize in_value to non-NULL only when we now know that called
	// function's computed value is non-NULL.

	variables * in_value = src_context->get_in_value (call_site);
	if (!in_value)
		in_value = initial_value ();
	// We do not change the old IN value; we change a copy of the old IN
	// value. This is because old IN value saved in COPY_OLD_IN_VALUE (in
	// ipa/backward_inter_procedural_analysis.cpp) should not be modified.
	else
	{
		DEBUG ("\nCreating new in_value");
		DEBUG ("\nin_value->copy_value()");
		variables * in_value_copy = in_value->copy_value (false);
		in_value = in_value_copy;
	}
	src_context->set_in_value (call_site, in_value);

#if DEBUG_CONTAINER
	DEBUG ("\nValue at in of call-site");
	in_value->print_value (NULL);
#endif
}

bool liveness_analysis_simple::
process_parsed_data (context<variables, PT_VALUE_TYPE> * current_context, 
	basic_block current_block, 
	variables * returning_value, 
	bool to_kill)
{
#if DEBUG_CONTAINER
	DEBUG ("\nprocess_parsed_data");
	DEBUG ("\nprint_parsed_data (current_block=%d)", current_block->index);
	program.print_parsed_data (current_block);
#endif

	list<pair<unsigned int, bool> > parsed_data_indices = 
		((block_information *)(current_block->aux))->get_parsed_data_indices ();

	bool is_in_initialized = false;
	unsigned int block_type = ((block_information *)(current_block->aux))->get_block_type ();
	if (block_type & AUX_BLOCK)
	{
		copy_out_to_in (current_context, current_block);
		return true;
	}

	if (block_type & NORETURN_BLOCK)
	{
		bool is_in_initialized = true;
		// current_context->set_in_value (current_block, initial_value ());
		DEBUG ("\nempty IN");
		variables * value = initial_value ();
		current_context->set_in_value (current_block, value);
		return is_in_initialized;
	}

	// The IN of CALL_BLOCKs is initialized in process_call_statement().
	// Initialize other blocks here.
	if (!(block_type & CALL_BLOCK))
	{
		copy_out_to_in (current_context, current_block);
		is_in_initialized = true;
	}

	variables * value;
	if ((block_type & CALL_BLOCK) && (value = returning_value));
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

			// In liveness analysis, the variables at OUT are either
			// (a) killed by lhs and transferred through rhs to (in) VALUE, or
			// (b) transferred without change from OUT to (in) VALUE

			DEBUG ("\nTransferring and generating stack liveness for assignment statement");
			process_assignment_statement (*value, current_context, current_block, index);
		}
		else
		{
			#if DEBUG_CONTAINER
			program.print_variable_data (index);
			#endif
			DEBUG ("\nMarking variable as stack live");
			process_use_statement (*value, current_context, current_block, index);
		}
	}

	if (block_type & CALL_BLOCK)
		return is_in_initialized;

	// Reuse: Delete a graph if it repeats at the successor program point.
	variables * value_in = current_context->get_in_value (current_block);
	variables * value_out = current_context->get_out_value (current_block);
	if (value_out->is_value_same (*value_in))
	{
		current_context->set_in_value (current_block, value_out);
	}

	return is_in_initialized;
}

void liveness_analysis_simple::
over_approximate_call_statement (variables & value, context<variables, PT_VALUE_TYPE> & src_context, basic_block call_site)
{
	DEBUG ("\nover_approximate_call_statement");

	// FIXME: Check if function call is the only statement of the block;
	// there are no assignment statements created by gcc for parameter
	// passing.
	DEBUG ("\ngsi_start_bb");
	gimple_stmt_iterator gsi = gsi_start_bb (call_site);
	gimple statement = gsi_stmt (gsi);
#if DEBUG_CONTAINER
	DEBUG ("\ngsi_stmt");
	print_gimple_stmt (dump_file, statement, 0, 0);
#endif

	// If there is even a single pointer parameter, overapproximate Lin.
	bool is_pointer_parameter = false;
	for (int i = 0; i < gimple_call_num_args (statement); i++)
	{
		tree arg = gimple_call_arg (statement, i);
		if (program.field_must_have_pointers (arg))
		{
			is_pointer_parameter = true;
			break;
		}
	}
	// If there is no pointer parameter, return to continue processing use
	// statements (for generating function pointers and parameters in Lin).
	if (!is_pointer_parameter)
		return;

	// Add all local variables to Lin if there exists even a single
	// function parameter.
	DEBUG ("\ncall_block: inserting all locals to (in) VALUE");
	struct cgraph_node * src_function = src_context.get_function ();
	// All non-temporary local pointers are made live
	set<unsigned int> local_non_temp_pointers = program.get_local_non_temp_pointers (src_function);
	value.insert_live_vars (local_non_temp_pointers);
#if DEBUG_CONTAINER
	value.print_value (NULL);
#endif
}

bool liveness_analysis_simple::
process_use_statement (variables & value, context<variables, PT_VALUE_TYPE> * current_context, basic_block current_block, unsigned int variable_index)
{
	DEBUG ("\nprocess_use_statement");

	csvarinfo_t variable = VEC_index (csvarinfo_t, program.variable_data, variable_index);
	DEBUG ("\nAdding variable id %d, name %s", variable->id, variable->name);

	// Check that variable is none of global, heap, and function parameter
	// in summary based analysis.
	value.insert_selective_live_var (variable->id);
	value.insert_selective_callees_global_use (variable->id);

#if DEBUG_CONTAINER
	DEBUG ("\nValue variables");
	value.print_value (NULL);
#endif
	DEBUG ("\nprocess_use_statement done");
	return true;
}

bool liveness_analysis_simple::
process_assignment_statement (variables & value, context<variables, PT_VALUE_TYPE> * current_context, basic_block current_block, unsigned int assignment_data_index, bool to_kill)
{
	DEBUG ("\nprocess_assignment_statement");

	constraint_t assignment = VEC_index (constraint_t, program.assignment_data, assignment_data_index);
	constraint_expr lhs = assignment->lhs;
	constraint_expr rhs = assignment->rhs;	
	DEBUG ("\nlhs=%d, lhs.offset=%lld, rhs=%d, rhs.offset=%lld", 
		lhs.var, lhs.offset, rhs.var, rhs.offset);

#if DEBUG_CONTAINER
	DEBUG ("\nValue variables");
	value.print_value (NULL);
#endif

	// In liveness analysis, the variables at OUT are either
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
	//      return;
	// Assume all pointer arithmetic happen only on arrays. Ignoring
	// pointer arithmeitc on fields of structures.
	if (lhs.pointer_arithmetic)
		lhs.offset = 0;
	if (rhs.pointer_arithmetic)
		rhs.offset = 0;


	// Call is_live () before lhs is killed from live_vars.
	// A block becomes important only if it generates new points-to
	// info or it is a predecessor of an important block.
	csvarinfo_t rhs_var = VEC_index (csvarinfo_t, program.variable_data, rhs.var);
	if (rhs_var && rhs_var->decl && value.is_live (lhs.var))
		value.gen_important_block ();


	variables gen_live_vars, kill_live_vars;

	// lhs->f=... or *lhs=...
	if (lhs.type == DEREF)
	{
		DEBUG ("\nlhs.type == DEREF");
		gen_live_vars.insert_selective_live_var (lhs.var);

		// lhs->f=rhs or *lhs=rhs
		if (rhs.type == SCALAR)
		{
			DEBUG ("\nrhs.type == SCALAR");
			if (value.is_element (lhs.var, lhs.offset))
				gen_live_vars.insert_selective_live_var (rhs.var);
		}
			
		// lhs->f=rhs->g
		else if (rhs.type == DEREF)
		{
			DEBUG ("\nrhs.type == DEREF");
			// Such a statement exists in mcf benchmark.
			// Function suspend_impl <bb 13> *new_arc_6 = *arc_7;
			if (value.is_element (lhs.var, lhs.offset))
			{
				struct cgraph_node * current_function = current_context->get_function ();	
				// FIXME: From preprocess_and_parse_program(), call a function which
				// would save this information in liveness_analysis_simple.
				// addr_taken_locals do not include temporaries
				gen_live_vars.insert_addr_taken_locals (rhs.var, rhs.offset, current_function);

				// No use explicitly marking reachable lives
				// for inter-proc liveness. We assume reaching
				// and reachable as live in Pta.
				// if (is_value_context)
				// {
				// 	gen_live_vars.insert_addr_taken_params (current_function);
				//	gen_live_vars.insert_addr_taken_globals ();
				// }
			}
		}

		// lhs->f=&rhs or *lhs=&rhs
		else if (rhs.type == ADDRESSOF)
		{
			DEBUG ("\nrhs.type == ADDRESSOF");
			// e.g. x=&y;t=x->g;use t then y.g,y.f,etc are marked
			// live at IN(3) and they continue to remain live at
			// IN(1).
			// If we were marking only explicitly used vars, i.e.
			// only rhs root nodes, then each live var would have
			// represented a live path rooted at the variable. In
			// that case we would have needed to transfer liveness
			// to rhs, even if it is & on rhs.
		}
	}	

	// lhs=...
	else if (lhs.type == SCALAR)
	{
		DEBUG ("\nlhs.type == SCALAR");
		if (!program.is_array (lhs.var) && !program.is_union (lhs.var))
			kill_live_vars.insert_selective_live_var (lhs.var);

		// lhs=rhs
		if (rhs.type == SCALAR)
		{
			DEBUG ("\nrhs.type == SCALAR");
			if (value.is_element (lhs.var))
				gen_live_vars.insert_selective_live_var (rhs.var);
		}

		// lhs=rhs->f or lhs=*rhs
		else if (rhs.type == DEREF)
		{
			DEBUG ("\nrhs.type == DEREF");
			if (value.is_element (lhs.var))
			{
				struct cgraph_node * current_function = current_context->get_function ();
				// FIXME: From preprocess_and_parse_program(), call a function which
				// would save this information in liveness_analysis_simple.
				// addr_taken_locals do not include temporaries
				gen_live_vars.insert_addr_taken_locals (rhs.var, rhs.offset, current_function);

				// No use explicitly marking reachable lives
				// for inter-proc liveness. We assume reaching
				// and reachable as live in Pta.
				// if (is_value_context)
				// {
				//	gen_live_vars.insert_addr_taken_params (current_function);
				//	gen_live_vars.insert_addr_taken_globals ();
				// }
			}
		}

		// lhs=&rhs
		else if (rhs.type == ADDRESSOF)
		{
			DEBUG ("\nrhs.type == ADDRESSOF");
			// e.g. x=&y;t=x->g;use t then y.g,y.f,etc are marked
			// live at IN(3) and they continue to remain live at
			// IN(1).
			// If we were marking only explicitly used vars, i.e.
			// only rhs root nodes, then each live var would have
			// represented a live path rooted at the variable. In
			// that case we would have needed to transfer liveness
			// to rhs, even if it is & on rhs.
		}

#if DEBUG_CONTAINER
		if (lhs.var == rhs.var && rhs.type == SCALAR)
			DEBUG ("\nlhs.var = rhs.var = %d", lhs.var);
#endif
	}

	else if (lhs.type == ADDRESSOF)
		RESULT ("\nError: Lvalue error.");


#if DEBUG_CONTAINER
	DEBUG ("\nOriginal variables");
	value.print_value (OPEN_FST_FILE);
#endif

	if (to_kill)
	{
#if DEBUG_CONTAINER
		DEBUG ("\nDeleting kill_live_vars");
		kill_live_vars.print_value (NULL);
#endif
		value.delete_live_vars (kill_live_vars);
	}
#if DEBUG_CONTAINER
	DEBUG ("\nAdding gen_live_vars");
	gen_live_vars.print_value (NULL);
#endif
	value.insert_live_vars (gen_live_vars);

	// Over-approximating rec:=ret and param:=arg
	unsigned int block_type = ((block_information *)(current_block->aux))->get_block_type ();
	if (block_type & CALL_BLOCK)
	{
		value.insert_selective_live_var (rhs.var);
	}

	// Side effect analysis
	if (lhs.type == DEREF)
	{
		value.insert_selective_callees_global_use (lhs.var);
	}
	else if (lhs.type == SCALAR)
	{
		value.insert_selective_callees_global_def (lhs.var);
		// Do not consider par:=arg as a def of par. Ignore call block.
		// If received var is par, it is included in
		// process_return_value ().
		if (!(block_type & CALL_BLOCK))
			value.insert_selective_function_param_def (lhs.var);
		if (to_kill)
			value.delete_callees_global_use (lhs.var);
	}

	if (rhs.type == SCALAR || rhs.type == DEREF)
		value.insert_selective_callees_global_use (rhs.var);


#if DEBUG_CONTAINER
	DEBUG ("\nUpdated variables");
	value.print_value (OPEN_FST_FILE);
#endif

	DEBUG ("\nprocess_assignment_statement done");
	return true;
}

/**
 * process_assignment_statement():
 * EXPLICIT_LIVENESS=1 i.e. not marking reachable (implicit) vars. If this is
 * inter-proc, then we need to generate reaching and reachable (implicit) vars
 * before bypassing. In PTA, assume nodes reachable from marked live vars as
 * live.
 */
//
//	// lhs->f=... or *lhs=...
//	if (lhs.type == DEREF)
//	{
//		DEBUG ("\nlhs.type == DEREF");
//		value.insert_selective_live_var (is_value_context, lhs.var);
//
//		value.insert_selective_callees_global_use (lhs.var);
//
//		// lhs->f=rhs or *lhs=rhs
//		if (rhs.type == SCALAR)
//		{
//			DEBUG ("\nrhs.type == SCALAR");
//			// In EXPLICIT_LIVENESS, since paths aliased to lhs may
//			// be implicitly live and not marked at OUT, we mark
//			// rhs live anyway.
//			// if (value.is_element (lhs.var, lhs.offset))
//			value.insert_selective_live_var (is_value_context, rhs.var);
//			value.insert_selective_callees_global_use (rhs.var);
//		}
//			
//		// lhs->f=rhs->g
//		else if (rhs.type == DEREF)
//		{
//			DEBUG ("\nrhs.type == DEREF");
//			// In EXPLICIT_LIVENESS, irrespective of lhs, we mark
//			// rhs root node as live. Then during points-to, all
//			// variables reachable from live rhs node are marked
//			// live.
//			// if (value.is_element (lhs.var, lhs.offset))
//			value.insert_selective_live_var (is_value_context, rhs.var);
//			value.insert_selective_callees_global_use (rhs.var);
//		}
//
//		// lhs->f=&rhs or *lhs=&rhs
//		else if (rhs.type == ADDRESSOF)
//		{
//			DEBUG ("\nrhs.type == ADDRESSOF");
//			// In EXPLICIT_LIVENESS, irrespective of lhs, we mark
//			// rhs root node as live. Since each live variable in
//			// live_vars represents a live path rooted at
//			// the variable, the live path needs to be transferred
//			// to rhs, even if it is & on rhs. 
//			value.insert_selective_live_var (is_value_context, rhs.var);
//			value.insert_selective_callees_global_use (rhs.var);
//		}
//	}	
//
//	// lhs=...
//	else if (lhs.type == SCALAR)
//	{
//		DEBUG ("\nlhs.type == SCALAR");
//		bool is_lhs_live = value.is_element (is_value_context, lhs.var);
//		if (to_kill)
//			value.delete_live_var (lhs.var);
//		
//		value.insert_selective_callees_global_def (lhs.var);
//		if (to_kill)
//			value.delete_callees_global_use (lhs.var);
//
//		// lhs=rhs
//		if (rhs.type == SCALAR)
//		{
//			DEBUG ("\nrhs.type == SCALAR");
//			if (is_lhs_live)
//				value.insert_selective_live_var (is_value_context, rhs.var);
//			value.insert_selective_callees_global_use (rhs.var);
//		}
//
//		// lhs=rhs->f or lhs=*rhs
//		else if (rhs.type == DEREF)
//		{
//			DEBUG ("\nrhs.type == DEREF");
//			// In EXPLICIT_LIVENESS, we mark rhs root node as live.
//			// Then during points-to, all variables reachable from
//			// live rhs node are marked live.
//			if (is_lhs_live)
//				value.insert_selective_live_var (is_value_context, rhs.var);
//			value.insert_selective_callees_global_use (rhs.var);
//		}
//
//		// lhs=&rhs
//		else if (rhs.type == ADDRESSOF)
//		{
//			DEBUG ("\nrhs.type == ADDRESSOF");
//			// e.g. x=&y;t=x->g;use t then y.g,y.f,etc are marked
//			// live at IN(3) and they continue to remain live at
//			// IN(1).
//			// In EXPLICIT_LIVENESS, we mark rhs root node as live.
//			// Since each live variable in live_vars
//			// represents a live path rooted at the variable, the
//			// live path needs to be transferred to rhs, even if it
//			// is & on rhs. 
//			if (is_lhs_live)
//				value.insert_selective_live_var (is_value_context, rhs.var);
//			value.insert_selective_callees_global_use (rhs.var);
//		}
//
//#if DEBUG_CONTAINER
//		if (lhs.var == rhs.var && rhs.type == SCALAR)
//			DEBUG ("\nlhs.var = rhs.var = %d", lhs.var);
//#endif
//	}
//
//	else if (lhs.type == ADDRESSOF)
//		RESULT ("\nError: Lvalue error.");



set<struct cgraph_node *> liveness_analysis_simple::
get_called_functions (context<variables, PT_VALUE_TYPE> & src_context, basic_block call_site, tree function_pointer)
{
	set<struct cgraph_node *> called_functions;
	// Use pointer information for the function pointer computed by gcc.

	program.get_gcc_fn_pointees (function_pointer, called_functions);
	return called_functions;
}

/**
 * Add to assignment_data of the CALL_SITE, mapping of returned value of
 * CALLED_FUNCTION to the received value. Then process them and delete the
 * mappings if the CALL_SITE is a function pointer call.
 */

void liveness_analysis_simple::
process_return_value (context<variables, PT_VALUE_TYPE> * src_context,
	basic_block call_site,
	variables * value,
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

	// We do not add anything to function_param_defs in call block in order
	// to ignore par:=arg defs. Therefore, we need to add rec var if it is
	// a param here.
	csvarinfo_t rec = program.get_received_var (call_site, src_function);
	if (rec)
		value->insert_selective_function_param_def (rec->id);

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
 * Add to assignment_data of the CALL_SITE, mappings of actual parameters to
 * formal parameters of CALLED_FUNCTION. Then process them and delete the
 * mappings if the CALL_SITE is a function pointer call.
 */

void liveness_analysis_simple::
process_function_arguments (context<variables, PT_VALUE_TYPE> * src_context,
	basic_block call_site,
	variables * value,
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

	// All addr-taken locals are added because they may be
	// reachable from args and may have been dereferenced via
	// params in called function.
	list<pair<unsigned int, bool> > parsed_data_indices = 
		((block_information *)(call_site->aux))->get_parsed_data_indices ();
	// If there is even a single pointer parameter, overapproximate Lin.
	if (parsed_data_indices.size ())
	{
		struct cgraph_node * src_function = src_context->get_function ();	
		value->insert_addr_taken_locals (src_function);
	}

	// over_approximate_call_statement (*value, *src_context, call_site);

	// Erase the mappings
	((block_information *)(call_site->aux))->erase_assignment_indices ();
}

void liveness_analysis_simple::
insert_parameters (struct cgraph_node * src_function, variables & params)
{
	program.get_function_parameters (src_function, params.live_vars);
}

void liveness_analysis_simple::
insert_global_pointers (variables & globals)
{
	program.get_global_named_pointers (globals.live_vars);
}


variables * liveness_analysis_simple::
extract_arg_ret_glob_reachable_value (struct cgraph_node * src_function,
	basic_block call_site,
	struct cgraph_node * called_function,
	variables & value_out)
{ 
	// In summary based (intra-proc) liveness, globals are not marked. Only
	// the returned variable belonging to the called function needs to be
	// extracted. 

	// Using boundary_value () for summary based inter-proc analysis of
	// liveness_analysis_simple where important_blocks=true at boundary.
	variables * arg_ret_glob_reachable_value = boundary_value ();

	// Do not send different important_block values to caller. Else,
	// liveness_analysis_simple will no more generate single context per
	// function.
	// value_out.transfer_important_block (*arg_ret_glob_reachable_value);

	// Collect globals and address-taken locals. We need the latter so that
	// locals of caller that points-to analysis passes to callee are not
	// killed in callee. Points-to analysis passes only parameter and
	// global reachable (i.e., addr-taken) vars.
//	value_out.extract_arg_ret_glob_reachable_live_vars (*arg_ret_glob_reachable_value, called_function);

	set<unsigned int> ret_vars = program.get_return_vars (called_function);
	arg_ret_glob_reachable_value->insert_live_vars (ret_vars);
	value_out.delete_live_vars (ret_vars);

	// Bypass all callees_global_defs/uses, callees_lhs_derefs,
	// function_param_defs i.e., none of these (which belong to the caller)
	// should be passed to the callee.  Therefore, nothing to do here.

	return arg_ret_glob_reachable_value;
}

/**
 * This function is not called by check_and_delete_local_variables()
 */

void liveness_analysis_simple::
delete_local_variables (struct cgraph_node * src_function,
	struct cgraph_node * function, variables & value,
	void * info)
{
	// In summary based liveness, globals are anyway not marked.
	// Therefore, we do not want any live_vars from called function. We
	// want all callee_global_defs/uses of callee because they are global.

	// Do not delete locals of src_function.
	if (src_function == function)
		return;

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
	value.delete_live_vars (local_variables);

	// kill all params
	value.erase_function_param_defs ();
}

void liveness_analysis_simple::
store_context_info (context<variables, unlabeled_edges> & current_context)
{
        struct cgraph_node * func = current_context.get_function ();
        basic_block start_bb = current_context.get_start_block ();
        variables * start_value = current_context.get_in_value (start_bb);
	if (!start_value)
		return;

	set<block_index> unimp_blocks;
	if (!start_value->is_important_block ())
		unimp_blocks.insert (start_bb->index);
        basic_block end_bb = current_context.get_end_block ();
        variables * end_value = current_context.get_in_value (end_bb);
	if (end_value && !end_value->is_important_block ())
		unimp_blocks.insert (end_bb->index);
	struct function * function_decl = DECL_STRUCT_FUNCTION (func->decl);
	basic_block block;
	FOR_EACH_BB_FN (block, function_decl)
	{
		block_index bid = block->index;
		variables * value = current_context.get_in_value (block);
		if (value && !value->is_important_block ())
			unimp_blocks.insert (bid);
	}
	function_side_effects.add_unimportant_blocks (func, unimp_blocks);

	set<variable_id> vars = start_value->get_callees_global_defs ();
        function_side_effects.add_callees_global_defs (func, vars);
	vars = start_value->get_callees_global_uses ();
        function_side_effects.add_callees_global_uses (func, vars);
	vars = start_value->get_function_param_defs ();
        function_side_effects.add_function_param_defs (func, vars);

	function_side_effects.set_is_unimp_blocks_ready ();
}

void liveness_analysis_simple::
print_value (variables & vars)
{
	FUNBEGIN ();

	vars.print_value (OPEN_FST_FILE);

	RETURN_VOID ();
}

void liveness_analysis_simple::
print_analysis_statistics (map<function_index, context_enums<variables, PT_VALUE_TYPE> > & function_contexts)
{
	DEBUG ("\nprint_analysis_statistics()");

	variables globals;
	insert_global_pointers (globals);

	// We use FUNCTION_CONTEXTS_MAP instead of PROGRAM_CONTEXTS of
	// inter_procedural_analysis.hh so that the statistics are printed in
	// order of functions. This makes it easier to compare to files of
	// statistics.
	typename map<function_index, context_enums<variables, PT_VALUE_TYPE> >::reverse_iterator rfi;
	for (rfi = function_contexts.rbegin (); rfi != function_contexts.rend (); rfi++)
	{	
		struct cgraph_node * function = program.get_cgraph_node (rfi->first);
		const char * function_name = cgraph_node_name (function);
		DEBUG ("\nfunction=%s", function_name);
		struct function * function_decl = DECL_STRUCT_FUNCTION (function->decl);

		variables parameters;
		insert_parameters (function, parameters);

		context_enums<variables, PT_VALUE_TYPE> contexts = rfi->second;

		basic_block block;
		FOR_EACH_BB_FN (block, function_decl)	
		{
			unsigned int block_id = block->index;
			if (!block->aux)
			{
				DEBUG ("\nBlock %d aux = NULL", block_id);
				continue;
			}
			unsigned int block_type = 
				((block_information *)(block->aux))->get_block_type ();
			if (!(block_type & START_BLOCK) && !(block_type & END_BLOCK))
				continue;
			DEBUG ("\nBlock=%d", block_id);

			variables in_variables, out_variables;

			// Compute meet of all the contexts for this basic block

			typename context_enums<variables, PT_VALUE_TYPE>::iterator ci;
			for (ci = contexts.begin (); ci != contexts.end (); ci++)
			{
				context<variables, PT_VALUE_TYPE> * current_context = 
					ci->second;
				DEBUG ("\nContext=%d", current_context->get_context_id ());

				// In value
				variables * v = current_context->get_in_value (block);
				if (v)
					in_variables.insert_live_vars (*v);

				// Out value
				v = current_context->get_out_value (block);
				if (v)
					out_variables.insert_live_vars (*v);
			}
/*
			if (block_type & START_BLOCK)
			{
				RESULT ("\n\nfunction %s, OUT(%d)---START", function_name, block_id);
				program.print_block_statements (block);
				RESULT ("\nLocals: ");
				print_value (out_variables);
				RESULT ("\nParams: ");
				print_value (parameters);
				RESULT ("\nGlobals: ");
				print_value (globals);
			}
			if (block_type & END_BLOCK)
			{
				RESULT ("\n\nfunction %s, OUT(%d)---END", function_name, block_id);
				RESULT ("\nLocals: ");
				print_value (out_variables);
				RESULT ("\nParams: ");
				print_value (parameters);
				RESULT ("\nGlobals: ");
				print_value (globals);
			}
*/
			if (program.print_source_location (block))
			{
				RESULT ("\nLocals: ");
				print_value (out_variables);
				RESULT ("\nParams: ");
				print_value (parameters);
				RESULT ("\nGlobals: ");
				print_value (globals);
			}
		}
	}
}

/** 
 * The client analysis can modify the control flow graph to use our
 * inter-procedural analysis, which assumes that each function call is the only
 * statement in a basic block. Also, each pointer statement is made the only
 * statement of a basic block for bi-directional inter-procedural analysis.
 */

void liveness_analysis_simple::
preprocess_and_parse_program ()
{
	RESULT ("\nFUNCTIONAL_LIVENESS=1");
	program.initialization ();
	program.preprocess_control_flow_graph ();
	set_blocks_order ();
 
#if DEBUG_CONTAINER
	program.print_parsed_data ();
	// program.print_variable_data ();
	// program.print_assignment_data ();
#endif
}


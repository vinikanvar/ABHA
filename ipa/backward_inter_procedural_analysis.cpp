
/************************
 * @author Vini Kanvar
************************/

#include "backward_inter_procedural_analysis.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

template <class value_type, class dept_value_type>
backward_inter_procedural_analysis<value_type, dept_value_type>::
backward_inter_procedural_analysis (bool is_val_context)
{
	this->is_value_context = is_val_context;
}

/* This function finds a context SAME_CONTEXT in DEST_FUNCTION where
 * (a) value of SAME_CONTEXT at start/end of DEST_FUNCTION is same as VALUE 
 * (b) the SAME_CONTEXT is dependent on DEPT_CONTEXT.
 *
 * @returns SAME_CONTEXT
 */

template <class value_type, class dept_value_type>
context<value_type, dept_value_type> * backward_inter_procedural_analysis<value_type, dept_value_type>::
get_same_dest_context (struct cgraph_node * dest_function, value_type & value, context<dept_value_type, value_type> * dept_context)
{
	struct timeval start;
	start_timer (start);

	// Iterate over all the contexts of FUNCTION_ID to find the same context
	context_enums<value_type, dept_value_type> ce = get_context_enums (dest_function->uid);
	// Iterate in reverse order. The chances of finding the same value in
	// later contexts is higher.
	typename context_enums<value_type, dept_value_type>::reverse_iterator rit;
	for (rit = ce.rbegin (); rit != ce.rend (); rit++)
	{
		context<value_type, dept_value_type> * same_context = rit->second;
		DEBUG ("\nFinding graph in context %d", same_context->get_context_id ());

		// Find context with value same as VALUE
		if (same_context->is_end_value_same (value))
		{
			DEBUG ("\nValue is same as in context %d", same_context->get_context_id ());

			// Find if the dependent context of SAME_CONTEXT is same as DEPT_CONTEXT
			if (!dependent_analysis || same_context->is_dept_context_same (dept_context))
			{
#if DEBUG_CONTAINER
				if (dept_context)
				{
					DEBUG ("\nValue has already been processed in function %d under dependent context %d",
						dest_function->uid, dept_context->get_context_id ());
				}
				else
				{
					DEBUG ("\nValue has already been processed in function %d under dependent context NULL",
						dest_function->uid);
				}
#endif
				stop_timer (start, backward_get_same_dest_context_stats);
				return same_context;
			}
		}
	}
				
	stop_timer (start, backward_get_same_dest_context_stats);
	return NULL;
}
 
template <class value_type, class dept_value_type>
void backward_inter_procedural_analysis<value_type, dept_value_type>::
set_boundary_value (context<value_type, dept_value_type> * new_context, value_type * boundary_value)
{
	struct cgraph_node * cnode = new_context->get_function ();
	basic_block end_block = new_context->get_end_block ();
        DEBUG ("\nSet boundary value to block %d", end_block->index);
	new_context->set_out_value (end_block, boundary_value);
}

/**
 * We wish to find the destination context in DEST_FUNCTION from SRC_CONTEXT
 * through CALL_SITE. The destination context (EXISTING_DEST_CONTEXT) is
 * already existing if 
 * (a) the value of EXISTING_DEST_CONTEXT at start/end of DEST_FUNCTION is the
 *     same as the value of SRC_CONTEXT at CALL_SITE, and
 * (b) the dependent context of EXISTING_DEST_CONTEXT at start/end of
 *     DEST_FUNCTION is the same as the dependent context of SRC_CONTEXT at
 *     CALL_SITE, i.e. given that SRC_CONTEXT is dependent on D1, and D2 is
 *     reachable from D1 through CALL_SITE, EXISTING_DEST_CONTEXT is dependent 
 *     on D2. 
 * For a context to be the same at the CALL_SITE and the start/end of
 * FUNCTION_ID, we need to consider both (a) value and (b) dependent contexts
 * because for example, liveness context L1, which is dependent on alias
 * context A1, is different from liveness context L2, which is dependent on
 * alias context A2; even if the values of L1 and L2 at the end block of the
 * function are the same.
 *
 * This function returns the value computed at IN of the START block of
 * EXISTING_DEST_CONTEXT (if it exists, otherwise it returns NULL). Note that
 * it does not create a copy of the IN value.  Therefore, the client analysis
 * should first create a copy before modifying this returned value.
 */

template <class value_type, class dept_value_type>
value_type * backward_inter_procedural_analysis<value_type, dept_value_type>::
process_destination_context (context<value_type, dept_value_type> & src_context, 
	basic_block call_site, 
	struct cgraph_node * dest_function, 
	value_type * calling_value)
{
	if (!is_value_context)
	{
		return process_destination_context (dest_function, calling_value);
	}

	// AUX_BLOCK is CALL_BLOCK in dfa/liveness_analysis_deterministic/non_deterministic
	basic_block actual_call_block = call_site;
	unsigned int block_type = ((block_information *)(call_site->aux))->get_block_type ();
	if (block_type & AUX_BLOCK)
		actual_call_block = program.get_single_succ_block (call_site);

	// If call_site is an AUX_BLOCK, then we should fetch the dept_context
	// from the actual call block.
	context<dept_value_type, value_type> * dest_dept_context = 
		get_dest_of_dept_context (&src_context, actual_call_block, dest_function);
	if (!dest_dept_context)
		DEBUG ("\ndest_dept_context is NULL");

	// Unlike forward analysis, for backward analysis, the values of the
	// caller are passed to the called function without mapping the
	// parameters to the function arguments.
	// Here IN_VALUE at source is CALLING_VALUE.
	context<value_type, dept_value_type> * existing_dest_context = 
		get_same_dest_context (dest_function, *calling_value, dest_dept_context);

	value_type * function_in_value = NULL;
	if (existing_dest_context)
	{
		DEBUG ("\nFound existing dest context %d", 
			existing_dest_context->get_context_id ());
		function_in_value = process_existing_dest_context (src_context, call_site, 
			dest_function, *existing_dest_context);
		#if GC
		if (calling_value)
			delete calling_value;
		#endif
	}
	else
	{
		DEBUG ("\nExisting dest context not found");
		process_new_dest_context (src_context, call_site, 
			dest_function, *calling_value, dest_dept_context);
	}

	return function_in_value;
}

/**
 * This function returns the value computed at IN of the START block of
 * EXISTING_DEST_CONTEXT. Note that it does not create a copy of the IN value.
 * Therefore, the client analysis should first create a copy before modifying
 * this returned value.
 */

template <class value_type, class dept_value_type>
value_type * backward_inter_procedural_analysis<value_type, dept_value_type>::
process_existing_dest_context (context<value_type, dept_value_type> & src_context, 
	basic_block call_site, 
	struct cgraph_node * dest_function, 
	context<value_type, dept_value_type> & existing_dest_context)
{
	if (!is_value_context)
	{
		RESULT ("\nError: Function=%d is summary based", dest_function->uid);
		return NULL;
	}

#if UNSOUND_RETURN == 0
	// Update worklist to reprocess the call-site blocks of
	// contexts which will become a part of recursion with
	// SRC_CONTEXT.
	update_context_worklist (src_context, existing_dest_context, dest_function);
#endif

	// Push existing_dest_context on top of worklist to process any
	// unprocessed blocks.
	add_context_to_worklist (&existing_dest_context);

	// Erase SRC_CONTEXT from the source of any previously reachable context.
	context<value_type, dept_value_type> * prev_dest_context = 
		src_context.get_destination_context (call_site, dest_function);
	DEBUG ("\nsrc_context %d", src_context.get_context_id ());

	// Update source-destination contexts in context graph
	if (prev_dest_context)
	{
		DEBUG ("\nprev_dest_context %d", prev_dest_context->get_context_id ());
		prev_dest_context->erase_source_context (&src_context, call_site->index);
		// Remove PREV_DEST_CONTEXT if it has no source contexts. 
		// if (!prev_dest_context->get_source_contexts ().size ())
		//	remove_context_from_worklist (prev_dest_context);
		// However, since our CONTEXT_WORKLIST is a stack, we
		// cannot remove a context from in between.  Still
		// while processing the CONTEXT_WORKLIST, we process a
		// context only if it has a source context.
	}
	src_context.add_destination_context (call_site, &existing_dest_context);
	existing_dest_context.add_source_context (&src_context, call_site);

	// Get the value at the START block of EXISTING_DEST_CONTEXT.
	basic_block start_block = existing_dest_context.get_start_block ();
	if (!start_block)
		RESULT ("\nError: start_block is null");
	value_type * function_in_value = existing_dest_context.get_in_value (start_block);
#if DEBUG_CONTAINER
	DEBUG ("\nfunction's evaluation");
	// FIXME: error in test4a.c, test4.c, test5.c, test54.c, test29.c, ...
	// if (!function_in_value)
	//	RESULT ("\nError: function_in_value is NULL");
	// function_in_value->print_value (NULL);
#endif

	// We do not want to modify IN_VALUE of call-site here since this
	// should be in the hands of the client analysis. In other words, it
	// would be a bad programming practice to modify the IN_VALUE of the
	// source context in this external function
	// PROCESS_DESTINATION_CONTEXT(). So we simply return function's in
	// value.

	RESULT ("\nReuse context %d of function %s", 
		existing_dest_context.get_context_id (), cgraph_node_name (dest_function));
	return function_in_value;
}

template <class value_type, class dept_value_type>
void backward_inter_procedural_analysis<value_type, dept_value_type>::
process_new_dest_context (context<value_type, dept_value_type> & src_context, 
	basic_block call_site, 
	struct cgraph_node * dest_function, 
	value_type & calling_value, 
	context<dept_value_type, value_type> * dest_dept_context)
{
	if (!is_value_context)
	{
		RESULT ("\nError: Function=%d is summary based", dest_function->uid);
		return;
	}

	// The current block CALL_SITE has not been completely
	// processed since the called function is still to be
	// processed. Therefore, we add the current block of the
	// current context again for its reanalysis i.e. after the
	// called function has been processed.

	src_context.add_block_to_worklist (call_site);

	// If a context is reachable from SRC_CONTEXT through CALL_SITE
	// to function DEST_FUNCTION, and the reachable/destination
	// context has only SRC_CONTEXT as its source context, then
	// updating its value will have no side-effect on any other context.

	// Observation: But what if a context of some other analysis is
	// dependent on this reusable destination context? Then this
	// context is no more reusable. Answer: That dependent context
	// will continue to remain dependent.

	context<value_type, dept_value_type> * prev_dest_context;
	prev_dest_context = src_context.get_reusable_dest_context (call_site, dest_function);

	if (prev_dest_context)
	{
#if INTERMEDIATE_RESULT
		RESULT ("\nFound reusable destination context %d", prev_dest_context->get_context_id ());
#endif
		basic_block end = prev_dest_context->get_end_block ();
		// No need to create a copy of CALLING_VALUE. It is not being used anywhere else.
		prev_dest_context->set_out_value (end, &calling_value);
		prev_dest_context->add_block_to_worklist (end);
                // Add end block. We do not need to add start block --- if
                // there is any change, then start block will get added; and only
                // in that case will the calling context be added to context
                // worklist.
		add_context_to_worklist (prev_dest_context);
	}
	else
	{
		DEBUG ("\nNeed to create a new context");
		// Erase SRC_CONTEXT as the source of any previously reachable context.
		prev_dest_context = src_context.get_destination_context (call_site, dest_function);
		if (prev_dest_context)
		{
			prev_dest_context->erase_source_context (&src_context, call_site->index);
			// Remove PREV_DEST_CONTEXT if it has no source
			// contexts. 
			//if (!prev_dest_context->get_source_contexts ().size ())
			//	remove_context_from_worklist (prev_dest_context);
			// However, since our CONTEXT_WORKLIST is a stack, we
			// cannot remove a context from in between.  Still
			// while processing the CONTEXT_WORKLIST, we process a
			// context only if it has a source context.
		}

		// No need to create a copy of CALLING_VALUE. It is not being
		// used anywhere else.
		context<value_type, dept_value_type> * new_context = add_new_context 
			(dest_function, &calling_value, &src_context, call_site, dest_dept_context);	
		src_context.add_destination_context (call_site, new_context);
		// No need to initialize IN of call-site with
		// INITIAL_VALUE. The IN of call-site is already
		// initialized with the arg_glob-disconnected ndoes.
	}

#if DEBUG_CONTAINER
	print_context_worklist ();
	print_program_contexts ();
#endif
}

template <class value_type, class dept_value_type>
value_type * backward_inter_procedural_analysis<value_type, dept_value_type>::
process_destination_context (struct cgraph_node * dest_function, 
	value_type * calling_value)
{
	if (is_value_context)
	{
		RESULT ("\nError: function=%d is not summary context", dest_function->uid);
		return NULL;
	}

	context<value_type, dept_value_type> * existing_dest_context = get_function_context (dest_function);

	if (existing_dest_context)
	{
		// Get the value at the START block of EXISTING_DEST_CONTEXT.

		DEBUG ("\nFound existing dest context %d", existing_dest_context->get_context_id ());
		basic_block start_block = existing_dest_context->get_start_block ();
		if (!start_block)
			RESULT ("\nError: start_block is null");
		value_type * function_in_value = existing_dest_context->get_in_value (start_block);

		RESULT ("\nReuse context %d of function %s", 
			existing_dest_context->get_context_id (), cgraph_node_name (dest_function));

		#if GC
		if (calling_value)
			delete calling_value;
		#endif

		return function_in_value;
	}
		
	DEBUG ("\nExisting dest context not found");
	// This CALL_SITE will have an IN value independent of the
	// computation of the called function. Therefore, no need to
	// add this block to worklist.

	// Summary based interprocedural analysis has only one context
	// per function. Therefore, no need to find any previously
	// existing reusable context in the called function.

	// No need to create a copy of CALLING_VALUE. It is not being used
	// anywhere else.
	// No need to connect new context with SRC_CONTEXT.
	context<value_type, dept_value_type> * new_context = add_new_context 
		(dest_function, calling_value, NULL, NULL, NULL);	

	value_type * function_in_value = NULL;
	return function_in_value;
}

template <class value_type, class dept_value_type>
void backward_inter_procedural_analysis<value_type, dept_value_type>::
add_adjacent_blocks_to_worklist (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif

	unsigned int block_type = ((block_information *)(current_block->aux))->get_block_type ();
	struct cgraph_node * function = current_context->get_function ();
	const char * function_name = cgraph_node_name (function);
	DEBUG ("\nAdding adjancent blocks of function %s, block %d, type %d", 
		function_name, current_block->index, block_type);

	if (block_type & NORETURN_BLOCK)
	{
		DEBUG ("\nAdj blocks of NONRETURN_BLOCK are not added");
		return;
	}

	if (!(block_type & START_BLOCK))
	{
		DEBUG ("\n!START_BLOCK");
		edge e;
		edge_iterator ei;
		FOR_EACH_EDGE (e, ei, current_block->preds) 
		{
			basic_block pred_block = e->src;
			current_context->add_block_to_worklist (pred_block);
			DEBUG ("\nCurrent block %d, predecessor block %d added to worklist", 
				current_block->index, pred_block->index);
#if BIDIRECTIONAL_ANALYSIS
			add_dependent_context_to_worklist (current_context, pred_block);
#endif
		}
		DEBUG ("\nadding adj blocks done");
	}
	// In summary based interprocedural analysis, we do not
	// propagate value computed by the function to its caller(s).
	else if (is_value_context)
	{
		DEBUG ("\nAdding adjacent blocks (source function) of the start block of function %s", 
			function_name);
		set<pair<context_index, block_index> > source_contexts;
		source_contexts = current_context->get_source_contexts ();
		typename set<pair<context_index, block_index> >::iterator it;

		for (it = source_contexts.begin (); it != source_contexts.end (); it++)
		{
			context<value_type, dept_value_type> * source_context = get_context (it->first);
			struct cgraph_node * src_function = source_context->get_function ();
			basic_block call_site = get_block_of_function (src_function, it->second);
			DEBUG ("\nFound a source context");

			if (source_context)
			{
				DEBUG ("\nAdding source contexts: context %d, function %d, call site %d", 
					source_context->get_context_id (), src_function->uid, call_site->index);
				source_context->add_block_to_worklist (call_site);

				// Add the source_context to the worklist only
				// if it was not already present
				if (!is_context_in_worklist (source_context))
					add_context_to_worklist (source_context);

#if 0
				add_context_to_worklist (source_context);
				// We push current_context, so that its
				// processing is completed before
				// source_context.
				// FIXME: Check if benchmarks are faster without this.
				add_context_to_worklist (current_context);
#endif

#if BIDIRECTIONAL_ANALYSIS
				add_dependent_context_to_worklist (source_context, call_site);
#endif
			}
			// If this context does not have any source
			else 
			{
				struct cgraph_node * cnode = current_context->get_function ();
				// If the current context is not in function main
				if (strcmp (cgraph_node_name (cnode), "int main()") != 0)
					RESULT ("\nError: Caller's context not saved.");
			}
		}
	}
}

template <class value_type, class dept_value_type>
bool backward_inter_procedural_analysis<value_type, dept_value_type>::
analyze_block (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	DEBUG ("\nPrinting parsed data of block %d", current_block->index);

#if INTERMEDIATE_RESULT
        context<dept_value_type, value_type> * dept_context = get_dependent_context (current_context);
        DEBUG ("\ncalled get_dependent_context()");
        dept_value_type * dept_in_value = NULL;
        dept_value_type * dept_out_value = NULL;
        if (dept_context)
        {
                dept_in_value = dept_context->get_in_value (current_block);
                dept_out_value = dept_context->get_out_value (current_block);
        }
#endif

	// Compute OUT of block

//	value_type * out_value = current_context->get_out_value (current_block);
//	if (!out_value)
//		current_context->set_out_value (current_block, initial_value ());
	compute_out (current_context, current_block);
	value_type * out_value = current_context->get_out_value (current_block);
	// If this block has no successors
	if (!out_value)
	{
		current_context->set_out_value (current_block, initial_value ());
		out_value = current_context->get_out_value (current_block);
	}
#if INTERMEDIATE_RESULT
	struct cgraph_node * cnode = current_context->get_function ();
	const char * function_name = cgraph_node_name (cnode);

	unsigned int dcid = 0;
	if (dept_context)
		dcid = dept_context->get_context_id ();

	unsigned int fn_con_size = get_context_enums_size (cnode->uid);
        RESULT ("\nFunction=%s has %d # contexts", function_name, fn_con_size);
        if (fn_con_size > 50)
                RESULT ("\nALARM: Function=%s has %d # contexts", function_name, fn_con_size);

	RESULT ("\n\nbackward context %d, function %s, OUT(%d), (dept-context %d)",
		current_context->get_context_id (), function_name, current_block->index, dcid);
	program.print_block_statements (current_block);
#endif

	if (!out_value)
		RESULT ("\nError: OUT value of block %d remains un-initialized", current_block->index);

#if DEBUG_CONTAINER
	current_context->print_context ();
	print_context_worklist ();
#endif

#if INTERMEDIATE_RESULT
	if (out_value)
	        print_value (*out_value);

//        if (dept_out_value)
//                dept_out_value->print_value (NULL);
#endif

	// Compute IN of block

	// Save the value of IN before modifying it
	DEBUG ("\ncopy_old_in_value");
	value_type * copy_old_in_value = current_context->get_in_value (current_block);
	if (copy_old_in_value)
	{
		copy_old_in_value->increment_reference_count ();
#if DEBUG_CONTAINER
		DEBUG ("\ncopy_old_in_value: ");
		copy_old_in_value->print_value (NULL);
#endif
	}

	compute_in (current_context, current_block);
	value_type * in_value = current_context->get_in_value (current_block);

#if DEBUG_CONTAINER
	if (copy_old_in_value)
	{
		DEBUG ("\ncopy_old_in_value, after compute_in(): ");
		copy_old_in_value->print_value (NULL);
	}
#endif

#if INTERMEDIATE_RESULT
	if (((block_information *)(current_block->aux))->get_block_type () & START_BLOCK)
	{
		RESULT ("\n\n\nbackward context %d, function %s, IN(%d)---START, (dept-context %d)",
			current_context->get_context_id (), function_name, current_block->index, dcid);
	}
	else
	{
		RESULT ("\n\n\nbackward context %d, function %s, IN(%d), (dept-context %d)",
			current_context->get_context_id (), function_name, current_block->index, dcid);
	}
#endif

#if DEBUG_CONTAINER
	current_context->print_context ();
	print_context_worklist ();
#endif

#if INTERMEDIATE_RESULT
	if (in_value)
		print_value (*in_value);

//        if (dept_in_value)
//                dept_in_value->print_value (NULL);
	RESULT ("\n\n");
#endif

#if DEBUG_CONTAINER
	DEBUG ("\nold_in_value:");
	if (copy_old_in_value)
		copy_old_in_value->print_value (NULL);
#endif

	DEBUG ("\ncopy_old_in_value = NULL? = %d", copy_old_in_value == NULL);
	DEBUG ("\nin_value = NULL? = %d", in_value == NULL);

	bool is_value_same;
	if (copy_old_in_value && in_value)
	{
		DEBUG ("\nvalues non-null");
		is_value_same = copy_old_in_value->is_value_same (*in_value);
	}
	else 
	{
		// If computed value (e.g. called function) is NULL, we assume
		// that the value has not changed, i.e. we do not add adjacent
		// blocks.
		DEBUG ("\nold value is null");
		is_value_same = (copy_old_in_value == in_value);
	}

	DEBUG ("\nis_value_same=%d", is_value_same);
#if GC
	DEBUG ("\nGC value_type of old value at in(%d)", current_block->index);
	if (copy_old_in_value)
		copy_old_in_value->decrement_reference_count ();
	copy_old_in_value = NULL;
#endif

	DEBUG ("\nValue is same %d", is_value_same);

	return is_value_same;
}

/**
 * If there is only one successor edge to this block, then point the OUT value
 * to the IN of that successor edge.
 */

template <class value_type, class dept_value_type>
bool backward_inter_procedural_analysis<value_type, dept_value_type>::
compute_out_single_succ (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	int succ_count = 1;
	edge e;
	edge_iterator ei;
	basic_block succ_block = NULL;
	FOR_EACH_EDGE (e, ei, current_block->succs)
	{
		if (succ_count > 1)
		{
			DEBUG ("\nBlock %d has more than one successor", current_block->index);
			return false;
		}
		succ_count++;

		succ_block = e->dest;
	}
	if (!succ_block)
	{
		// This happens in test-case/test4i.c
		DEBUG ("\nThis block is %d, End block is %d", 
			current_block->index, current_context->get_end_block ()->index);
		DEBUG ("\nThis block %d does not have any successor block",
			current_block->index);
		return true;
	}

	DEBUG ("\nRetrieving IN value of successor %d of block %d",
		succ_block->index, current_block->index);
	value_type * succ_value = current_context->get_in_value (succ_block);
#if DEBUG_CONTAINER
	DEBUG ("\nRetrieved value: ");
	if (succ_value)
		succ_value->print_value (NULL);
#endif
	DEBUG ("\nInserting IN value of successor block %d to OUT value of block %d",
		succ_block->index, current_block->index);
	if (succ_value)
	{
		current_context->set_out_value (current_block, succ_value);
		DEBUG ("\nOut value of block %d is same as in value of block %d",
			current_block->index, succ_block->index);
	}
	else
	{
		DEBUG ("\nIN value of successor block %d is NULL", succ_block->index);
                // If GC_ON_THE_FLY, then this is not an error in which case,
                // add succ_block to worklist. 
#if GC_ON_THE_FLY
		// A block unreachable due to presence of NORETURN_BLOCK
		// (exit(0)), may have remained unprocessed; in which case we
		// do not want to add it to worklist.
                current_context->add_block_to_worklist (succ_block);
//#else
		// This is not an error: See test-cases/test44.c end-block's
		// successor is a node, which is unprocessed
//		DEBUG ("\nWhy is the single successor block %d of block %d still unprocessed?", 
//			succ_block->index, current_block->index);
#endif
	}
	return true;
}

template <class value_type, class dept_value_type>
void backward_inter_procedural_analysis<value_type, dept_value_type>::
compute_out_multiple_succ (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	// Compute OUT value afresh. Do not reuse any earlier computed OUT value, which 
	// may contain for example, x points to JUNK; this might not be true in the 
	// current iteration.
	value_type * out_value = initial_value ();
	current_context->set_out_value (current_block, out_value);

	edge e;
	edge_iterator ei;
	basic_block succ_block = NULL;
	FOR_EACH_EDGE (e, ei, current_block->succs)
	{
		succ_block = e->dest;
		DEBUG ("\nRetrieving IN value of successor %d of block %d",
			succ_block->index, current_block->index);
		value_type * succ_value = current_context->get_in_value (succ_block);
		DEBUG ("\nInserting IN value of successor block %d to OUT value of block %d",
			succ_block->index, current_block->index);
		if (!succ_value)
			DEBUG ("\nIN value of successor block %d is NULL", succ_block->index);

		// Creating copy of SUCC graph and merging with OUT value
		if (succ_value)
		{
			DEBUG ("\nCreating copy of successor graph and merging with OUT value");
			DEBUG ("\nreceived addr of variable_data=%x", program.variable_data); 
			bool is_loop_merge = ((block_information *)(current_block->aux))->get_loop_join ();
			out_value->copy_value (*succ_value, is_loop_merge);
		}
		else
                {
                        // This is not an error. If GC_ON_THE_FLY, then add
                        // succ_block to worklist. 
//#if GC_ON_THE_FLY
                        current_context->add_block_to_worklist (succ_block);
//#endif
                }


#if DEBUG_CONTAINER
		DEBUG ("\nOUT + SUCC graph");
		if (out_value)
			print_value (*out_value);
#endif
	}

	// SUCC_COPY may contain nodes that are not used by OUT_VALUE.
	// Therefore, mark the nodes that are unreachable from OUT_VALUE
	// and delete the unreachable nodes.
	out_value->clean ();
}

template <class value_type, class dept_value_type>
void backward_inter_procedural_analysis<value_type, dept_value_type>::
compute_out (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();

	struct cgraph_node * cnode = current_context->get_function ();
	const char * function_name = cgraph_node_name (cnode);
	DEBUG ("\nComputing OUT of block %d of function %s", current_block->index, function_name);
#endif 
	
	// bool is_value_same = false;

	if (((block_information *)(current_block->aux))->get_block_type () & END_BLOCK)
	{
		DEBUG ("\nThis is the end block. We do not calculate the OUT value of an end block");
		return;
	}
	DEBUG ("\nEnd block is %d", current_context->get_end_block ()->index); 

	// If there is only one successor of CURRENT_BLOCK, then point the
	// OUT value to the IN of that successor edge.
	bool success = compute_out_single_succ (current_context, current_block);

	// If there are multiple successors of CURRENT_BLOCK, then create a
	// new OUT value.
	if (!success)
		compute_out_multiple_succ (current_context, current_block);
	else
		DEBUG ("\nBlock %d has a single successor", current_block->index);
}

template <class value_type, class dept_value_type>
void backward_inter_procedural_analysis<value_type, dept_value_type>::
compute_in (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif 

	unsigned int block_type = ((block_information *)(current_block->aux))->get_block_type ();
	DEBUG ("\nBlock %d, block type %d", current_block->index, block_type);

	// Print statements of the block
	gimple_stmt_iterator gsi;
	DEBUG ("\n");
#if DEBUG_CONTAINER
	for (gsi = gsi_start_bb (current_block); !gsi_end_p (gsi); gsi_next (&gsi))
		print_gimple_stmt (dump_file, gsi_stmt (gsi), 0,0);
#endif

	if (block_type & CALL_BLOCK)
	{
		// Put a check to make sure that this statement is the only 
		// statement in the block
		gimple_stmt_iterator gsi = gsi_start_bb (current_block);
#if DEBUG_CONTAINER
		DEBUG ("\nCall statement: ");
		if (!(block_type & AUX_BLOCK))
			print_gimple_stmt (dump_file, gsi_stmt (gsi), 0, 0);
#endif

		// The mapping of arguments to function parameters is stored
		// as constraints of the block. These have been processed above
		// in this function (COMPUTE_IN) and stored at IN_VALUE of
		// this block.

		// This function propagates only arg_glob-connected nodes at
		// the OUT of call-site to the function. The IN of the
		// call-site is initialized with arg_glob-disconnected nodes
		// of the OUT of call-site. Then the function-transformed
		// arg_glob-connected nodes are merged with the value at the
		// IN of the call-site.

		process_call_statement (current_context, current_block);
	}
	// Parsed information is already processed in PROCESS_CALL_STATEMENT
	// before deleting local/parameters.
	else
		// Print and process parsed information of the block
		process_parsed_data (current_context, current_block, NULL);

#if DEBUG_CONTAINER
	// Pointer to IN_VALUE might have been reset in PROCESS_PARSED_DATA().
	// Therefore, reinitialize it.
	value_type * in_value = current_context->get_in_value (current_block);

	DEBUG ("\nIn_value");
	if (in_value)
		in_value->print_value (NULL);
#endif

	// No need to call CLEAN () here. Both the cases above ---
	// PROCESS_PARSED_DATA () and PROCESS_CALL_STATEMENT () call CLEAN ()
	// in the end.
}

template <class value_type, class dept_value_type>
void backward_inter_procedural_analysis<value_type, dept_value_type>::
copy_out_to_in (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	DEBUG ("\ncopy_out_to_in (block=%d)", current_block->index);

	value_type * out_value = current_context->get_out_value (current_block);
	// Create a new OUT_VALUE irrespective of whether an old OUT_VALUE was
	// present. The old OUT_VALUE might be required for comparison between
	// iterations of analysis. Therefore copy_in_to_out() has been called.
	// IS_LOOP_MERGE = FALSE
	value_type * in_value = out_value->copy_value (false);
	current_context->set_in_value (current_block, in_value);

	if (!out_value)
		DEBUG ("\nout_value is NULL");
	if (!in_value)
		DEBUG ("\nin_value is NULL");

#if DEBUG_CONTAINER
	DEBUG ("\nUpdated IN graph");
	if (in_value)
		print_value (*in_value);
#endif
}

template <class value_type, class dept_value_type>
void backward_inter_procedural_analysis<value_type, dept_value_type>::
set_block_order (basic_block block, int rev_post_order)
{
	int NUM_START_END_BLOCKS = 2;
	int number_of_blocks = n_basic_blocks - NUM_FIXED_BLOCKS + NUM_START_END_BLOCKS;
	((block_information *)(block->aux))->set_block_order (number_of_blocks - rev_post_order - 1);
	DEBUG ("(bb=%d,order=%d),", block->index, number_of_blocks - rev_post_order - 1);
}

//template class backward_inter_procedural_analysis<access_paths, non_deterministic_basic_graph>; 
//template class backward_inter_procedural_analysis<variables, non_deterministic_simple_graph>; 
template class backward_inter_procedural_analysis<variables, pt_node_set>; 
template class backward_inter_procedural_analysis<variables, unlabeled_edges>; 
template class backward_inter_procedural_analysis<deterministic_graph, unlabeled_edges>; 
template class backward_inter_procedural_analysis<non_deterministic_graph, unlabeled_edges>; 

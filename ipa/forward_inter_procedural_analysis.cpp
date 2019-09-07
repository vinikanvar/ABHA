
/************************
 * @author Vini Kanvar
************************/

#include "forward_inter_procedural_analysis.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)


template <class value_type, class dept_value_type>
forward_inter_procedural_analysis<value_type, dept_value_type>::
forward_inter_procedural_analysis (bool is_val_context)
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
context<value_type, dept_value_type> * forward_inter_procedural_analysis<value_type, dept_value_type>::
get_same_dest_context (struct cgraph_node * dest_function, value_type & value, context<dept_value_type, value_type> * dept_context)
{
	FUNBEGIN ();

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
		if (same_context->is_start_value_same (value))
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
				RETURN (same_context);
				// return same_context;
			}
		}
	}
	
	RETURN (NULL);
	// return NULL;
}

template <class value_type, class dept_value_type>
void forward_inter_procedural_analysis<value_type, dept_value_type>::
set_boundary_value (context<value_type, dept_value_type> * new_context, value_type * boundary_value)
{
	struct cgraph_node * cnode = new_context->get_function ();
	basic_block start_block = new_context->get_start_block ();
	DEBUG ("\nSet boundary value to block %d", start_block->index);
	new_context->set_in_value (start_block, boundary_value);
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
 * This function returns the value computed at IN of the END block of
 * EXISTING_DEST_CONTEXT. Note that it does not create a copy of the IN value.
 * Therefore, the client analysis should first create a copy before modifying
 * this returned value.
 */

template <class value_type, class dept_value_type>
value_type * forward_inter_procedural_analysis<value_type, dept_value_type>::
process_destination_context (context<value_type, dept_value_type> & src_context, 
	basic_block call_site, 
	struct cgraph_node * dest_function, 
	value_type * calling_value)
{
	context<dept_value_type, value_type> * dest_dept_context = 
		get_dest_of_dept_context (&src_context, call_site, dest_function);

	if (dest_dept_context)
	{
		DEBUG ("\ndest_dept_context=%d", dest_dept_context->get_context_id ());
	}
	else
	{
		DEBUG ("\ndest_dept_context=NULL");
	}

	// The OUT_VALUE stores all the intermediate evaluations of statements
	// in a block. Therefore, the OUT_VALUE of the block is updated with
	// function parameters mapped to the function arguments.
	// Here OUT_VALUE at source is CALLING_VALUE.
	context<value_type, dept_value_type> * existing_dest_context = 
		get_same_dest_context (dest_function, *calling_value, dest_dept_context);

	value_type * function_out_value = NULL;

	if (existing_dest_context)
	{
		function_out_value = process_existing_dest_context 
			(src_context, call_site, dest_function, *existing_dest_context);
#if GC
		if (calling_value)
			delete calling_value;
#endif
	}
	else
	{
		process_new_dest_context 
			(src_context, call_site, dest_function, *calling_value, dest_dept_context);
	}

	// Do not delete local variables (including returned variable) here
	// because we have still not mapped the returned value to the receiving
	// value.

#if DEBUG_CONTAINER
	DEBUG ("\nValue before deleting local variables:");
	value_type * out_value = src_context.get_out_value (call_site);
	if (out_value)
		out_value->print_value (NULL);
	DEBUG ("\nfuncion_out_value in ipa=");
	if (function_out_value)
		function_out_value->print_value (NULL);
#endif

	return function_out_value;
}

/**
 * This function returns the value computed at IN of the END block of
 * EXISTING_DEST_CONTEXT. Note that it does not create a copy of the IN value.
 * Therefore, the client analysis should first create a copy before modifying
 * this returned value.
 */

template <class value_type, class dept_value_type>
value_type * forward_inter_procedural_analysis<value_type, dept_value_type>::
process_existing_dest_context (context<value_type, dept_value_type> & src_context, 
	basic_block call_site, 
	struct cgraph_node * dest_function, 
	context<value_type, dept_value_type> & existing_dest_context)
{
	DEBUG ("\nFound existing dest context %d", existing_dest_context.get_context_id ());

	// No need to add src_context to worklist. This could lead to infinite
	// loop if dest_context calls back src_context because dest_context
	// also adds itself to worklist -- test6.c. src_context call-site will
	// be added if END_BLOCK of callee function changes.

	// Update worklist to reprocess the call-site blocks of
	// contexts which will become a part of recursion with
	// SRC_CONTEXT.
	// update_context_worklist (src_context, existing_dest_context, dest_function);

	// Push existing_dest_context on top of worklist to process any
	// unprocessed blocks.
	// add_context_to_worklist (&existing_dest_context);

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

	// Set the out of CALL_SITE of SRC_CONTEXT to the value of the
	// END block of EXISTING_DEST_CONTEXT.
	basic_block end_block = existing_dest_context.get_end_block ();
	if (!end_block)
		RESULT ("\nError: end_block is null");
	// Get IN value of the END block of the function since the returned
	// variable is dead at OUT and is missing in the OUT information; we
	// need the returned variable in the source context.
	value_type * function_out_value = existing_dest_context.get_in_value (end_block);
	if (!function_out_value)
		DEBUG ("\nfunction_out_value is null");
#if DEBUG_CONTAINER
	DEBUG ("\nfunction's evaluation");
	// FIXME: test-cases/test6.c gives error if these are uncommented!
//	VEC (csvarinfo_t, heap) * variable_data_debug = get_variable_data ();
//	function_out_value->print_value (NULL, NULL);
#endif

	// We do not want to modify OUT_VALUE of call-site here, i.e. before
	// mapping receiving variable to the returned variable of this
	// CALLED_FUNCTION; otherwise during the setting of receiving to
	// returned variables, the previously computed function pointee of
	// receiving variable (from another called function) will get killed
	// and overwritten by the returned variable of this CALLED_FUNCTION.
	
	// Also it would be a bad programming practice to modify the OUT_VALUE
	// of the source context in this external function
	// PROCESS_DESTINATION_CONTEXT(). So we simply return the function's
	// out value.

#if INTERMEDIATE_RESULT
	RESULT ("\nReuse context %d of function %s", 
		existing_dest_context.get_context_id (), cgraph_node_name (dest_function));
#endif
	return function_out_value;
}

template <class value_type, class dept_value_type>
void forward_inter_procedural_analysis<value_type, dept_value_type>::
process_new_dest_context (context<value_type, dept_value_type> & src_context, 
	basic_block call_site, 
	struct cgraph_node * dest_function, 
	value_type & calling_value, 
	context<dept_value_type, value_type> * dest_dept_context)
{
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

	context<value_type, dept_value_type> * prev_dest_context = NULL;
	prev_dest_context = src_context.get_reusable_dest_context (call_site, dest_function);

	if (prev_dest_context)
	{
#if INTERMEDIATE_RESULT
		RESULT ("\nFound reusable destination context %d", prev_dest_context->get_context_id ());
#endif
		basic_block start = prev_dest_context->get_start_block ();
		// No need to prepare a copy of CALLING_VALUE. It is not used anywhere else.
		prev_dest_context->set_in_value (start, &calling_value);
		prev_dest_context->add_block_to_worklist (start);
		// Add start block. We do not need to add end block --- if
		// there is any change, then end block will get added; and only
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

		// No need to prepare a copy of CALLING_VALUE. It is not used anywhere else.
		context<value_type, dept_value_type> * new_context = add_new_context 
			(dest_function, &calling_value, &src_context, call_site, dest_dept_context);	
		src_context.add_destination_context (call_site, new_context);
		// No need to initialize OUT of call-site with
		// INITIAL_VALUE. The OUT of call-site is already
		// initialized with the arg_glob-disconnected ndoes.
	}

#if DEBUG_CONTAINER
	print_context_worklist ();
	print_program_contexts ();
#endif
}

template <class value_type, class dept_value_type>
void forward_inter_procedural_analysis<value_type, dept_value_type>::
add_adjacent_blocks_to_worklist (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	FUNBEGIN ();

#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif

	unsigned int block_type = ((block_information *)(current_block->aux))->get_block_type ();
	struct cgraph_node * function = current_context->get_function ();
	const char * function_name = cgraph_node_name (function);
	DEBUG ("\nAdding adjancent blocks of function %s, block %d, type %d", 
		function_name, current_block->index, block_type);
	
	if (block_type & NORETURN_BLOCK)
		RETURN_VOID ();

	if (block_type & END_BLOCK)
	{
		DEBUG ("\nAdding adjacent blocks (source function) of the end block of function %s", 
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
				add_context_to_worklist (source_context);
				// We push current_context, so that its
				// processing is completed before
				// source_context. FIXME: Check if benchmarks
				// are faster without this.
				add_context_to_worklist (current_context);
#endif

#if BIDIRECTIONAL_ANALYSIS
				// FIXME: Add the source_context to the
				// worklist only if it was not already present
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
	else
	{
		edge e;
		edge_iterator ei;
		FOR_EACH_EDGE (e, ei, current_block->succs) 
		{
			basic_block succ_block = e->dest;
			current_context->add_block_to_worklist (succ_block);
			DEBUG ("\nCurrent block %d, successor block %d added to worklist", 
				current_block->index, succ_block->index);
#if BIDIRECTIONAL_ANALYSIS
			add_dependent_context_to_worklist (current_context, succ_block);
#endif
		}
	}

	RETURN_VOID ();
}

template <class value_type, class dept_value_type>
bool forward_inter_procedural_analysis<value_type, dept_value_type>::
analyze_block (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	FUNBEGIN ();

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

	// Compute IN of block

//	value_type * in_value = current_context->get_in_value (current_block);
//	if (!in_value)
//		current_context->set_in_value (current_block, initial_value ());
	compute_in (current_context, current_block);
	value_type * in_value = current_context->get_in_value (current_block);
	// If this block has no predecessors
	if (!in_value)
	{
		current_context->set_in_value (current_block, initial_value ());
		in_value = current_context->get_in_value (current_block);
	}

	struct cgraph_node * cnode = current_context->get_function ();
	const char * function_name = cgraph_node_name (cnode);
#if INTERMEDIATE_RESULT
	unsigned int dcid = 0;
	if (dept_context)
		dcid = dept_context->get_context_id ();

	RESULT ("\n\nforward context %d, function %s, IN(%d), (dept-context=%d)", 
		current_context->get_context_id (), function_name, current_block->index, dcid);
	program.print_block_statements (current_block);

#ifdef DOT_FILE
	FILE * file = fopen (DOT_FILE, "a"); 
	fprintf (file, "\n"); 
	fprintf (file, "\ndigraph pt_fi_graph {");
	fprintf (file, "\"context %d, function %s, IN(%d)\"", 
		current_context->get_context_id (), function_name, current_block->index);
	fprintf (file, "[shape=polygon,sides=4,color=red,style=filled];}");
	fclose (file); 
#endif
#endif

	if (!in_value)
		RESULT ("\nError: IN value of block %d remains un-initialized", current_block->index);

#if DEBUG_CONTAINER
	current_context->print_context ();
	DEBUG ("\nDependent context: ");
	if (dept_context)
		dept_context->print_context ();
	print_context_worklist ();
#endif

#if INTERMEDIATE_RESULT
	if (in_value)
		print_value (*in_value); 

	RESULT ("\ndependent context value=");
	if (dept_in_value)
		dept_in_value->print_value (NULL);
#endif

	// Compute OUT of block

	// Save the value at OUT before modifying it
	value_type * copy_old_out_value = current_context->get_out_value (current_block);
	if (copy_old_out_value)
	{
		copy_old_out_value->increment_reference_count ();
#if DEBUG_CONTAINER
		DEBUG ("\ncopy_old_out_value: ");
		copy_old_out_value->print_value (NULL);
#endif
	}

	// CALL block will set out to initial_value. END and other blocks will
	// call copy_in_to_out() in process_parsed_data ().
	compute_out (current_context, current_block);

//#if GC_ON_THE_FLY
	// IN of END_BLOCK and START_BLOCK are used by callee
//	unsigned int block_type = ((block_information *)(current_block->aux))->get_block_type ();
//	if (!(block_type & END_BLOCK) && !(block_type & START_BLOCK))
//	{
//		DEBUG ("\nNULLing IN of block=%d", current_block->index);
//		current_context->set_in_value (current_block, NULL);
//	}
//#endif

	value_type * out_value = current_context->get_out_value (current_block);

#if DEBUG_CONTAINER
	if (copy_old_out_value)
	{
		DEBUG ("\ncopy_old_out_value after call to compute_out(): ");
		copy_old_out_value->print_value (NULL);
	}
#endif

#if INTERMEDIATE_RESULT
	if (((block_information *)(current_block->aux))->get_block_type () & END_BLOCK)
	{
		RESULT ("\n\n\nforward context %d, function %s, OUT(%d)---END, (dept-context=%d)", 
			current_context->get_context_id (), function_name, current_block->index, dcid);
	}
	else
	{
		RESULT ("\n\n\nforward context %d, function %s, OUT(%d), (dept-context=%d)", 
			current_context->get_context_id (), function_name, current_block->index, dcid);
	}

#ifdef DOT_FILE
	file = fopen (DOT_FILE, "a"); 
	fprintf (file, "\n"); 
	fprintf (file, "\ndigraph pt_fi_graph {");
	fprintf (file, "\"context %d, function %s, OUT(%d)\"", 
		current_context->get_context_id (), function_name, current_block->index);
	fprintf (file, "[shape=polygon,sides=4,color=red,style=filled];}");
	fclose (file); 
#endif
#endif

#if DEBUG_CONTAINER
	current_context->print_context ();
	DEBUG ("\nDependent context: ");
	if (dept_context)
		dept_context->print_context ();
	print_context_worklist ();
#endif

#if INTERMEDIATE_RESULT
	if (out_value)
		print_value (*out_value);

	RESULT ("\ndependent context value=");
	if (dept_out_value)
		dept_out_value->print_value (NULL);
	RESULT ("\n\n");
#endif

#if DEBUG_CONTAINER
	DEBUG ("\nold_out_value:");
	if (copy_old_out_value)
		copy_old_out_value->print_value (NULL);
#endif

	DEBUG ("\ncopy_old_out_value = NULL? = %d", copy_old_out_value == NULL);
	DEBUG ("\nout_value = NULL? = %d", out_value == NULL);

	bool is_value_same;
	if (copy_old_out_value && out_value)
	{
		DEBUG ("\nvalues non-null");
		is_value_same = copy_old_out_value->is_value_same (*out_value);
	}
	else 
	{
		// If computed value (e.g. called function) is NULL, we assume
		// that the value has not changed, i.e. we do not add adjacent
		// blocks.
		DEBUG ("\nold value is null");
		is_value_same = (copy_old_out_value == out_value);
	}

	DEBUG ("\nis_value_same=%d", is_value_same);
#if GC
	DEBUG ("\nGC value_type of old value at out(%d)", current_block->index);
	if (copy_old_out_value)
		copy_old_out_value->decrement_reference_count ();
	copy_old_out_value = NULL;
#endif

	DEBUG ("\nValue is same %d in OUT(%d)", is_value_same, current_block->index);

	RETURN (is_value_same);
	// return is_value_same;
}

/**
 * If there is only one predecessor edge to this block, then point the IN value
 * to the OUT of that predecessor edge.
 */

template <class value_type, class dept_value_type>
bool forward_inter_procedural_analysis<value_type, dept_value_type>::
compute_in_single_pred (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	FUNBEGIN ();

	int pred_count = 1;
	edge e;
	edge_iterator ei;
	basic_block pred_block = NULL;
	FOR_EACH_EDGE (e, ei, current_block->preds)
	{
		if (pred_count > 1)
		{
			DEBUG ("\nBlock %d has more than one predecessor", current_block->index);
			RETURN (false);
			// return false;
		}
		pred_count++;

		pred_block = e->src;
	}
	// END_BLOCK will not have predecessor if all predecessors have exit(0);
	if (!pred_block)
		RETURN (true);

	DEBUG ("\nRetrieving OUT value of predecessor %d of block %d", 
		pred_block->index, current_block->index);
	value_type * pred_value = current_context->get_out_value (pred_block);
	DEBUG ("\nInserting OUT value of predecessor block %d to IN value of block %d",
		pred_block->index, current_block->index);
	if (pred_value)
	{
		current_context->set_in_value (current_block, pred_value);
		DEBUG ("\nIn value of block %d is same as out value of block %d", 
			current_block->index, pred_block->index);
	}
	else
	{
		DEBUG ("\nOUT value of predecessor block %d is NULL", pred_block->index);

		// If GC_ON_THE_FLY, then this is not an error in which case,
		// add pred_block to worklist. 
#if GC_ON_THE_FLY
		// A block unreachable due to presence of NORETURN_BLOCK
		// (exit(0)), may have remained unprocessed; in which case we
		// do not want to add it to worklist.
		current_context->add_block_to_worklist (pred_block);
//#else
//		RESULT ("\nError: Why is the single predecessor block %d of block %d still unprocessed?", 
//			pred_block->index, current_block->index);
#endif
	}

	RETURN (true);
	// return true;
}

template <class value_type, class dept_value_type>
void forward_inter_procedural_analysis<value_type, dept_value_type>::
compute_in_multiple_pred (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	FUNBEGIN ();
 
	// Compute IN value afresh. Do not reuse any earlier computed IN value, which 
	// may contain for example, x points to JUNK; this might not be true in the 
	// current iteration.

	// Note: We must take a merge of all the graphs, say g1 and g2, from
	// predecessors. We should not compare g1 and g2 to retain only one of
	// g1 and g2 if they are regex-equivalent. This could lead to
	// non-monotonic and unsafe results. For example,
	// g1={(x,*,n1)(y,*,n1)(p,n1)(x,*,n3)(z,*,n3)(z,*,n4)(n1,f,n2),(n3,f,n2)(q,n2)}.
	// g2={(x,*,n1)(y,*,n1)(p,n1)(x,*,n3)(z,*,n3)(z,*,n4)(n1,f,n2)(n4,f,n2)(q,n2)}.
	// Here g1 and g2 are regex-equivalent. However, the results will be
	// wrong and non-monotonic for the following example.
	// if... 1) generates fig1
	// else  2) generates fig2
	// 3) x->f = null
	// --If at in(3), we retain only fig1, then at out(3) we will say there
	// is no f out of z and no f reaches q.
	// --If at in(3), we retain only fig2, then at out(3) we will say that
	// there is a f out of z and f reaches q. -- correct
	// --If at in(3), we merge fig1 and fig2 at out(3) we will say that
	// there is a f out of z and f reaches q. -- correct
	// I think we should merge and then check if the two graphs are same or
	// not.  Otherwise it could give us unsound and non-monotonic results.
	// Non-monotonic because we will choose g1 first time (delete f edge at
	// out(3)) and then choose g2 next time (retain f edge at out(3)).

	value_type * in_value = initial_value ();
	current_context->set_in_value (current_block, in_value);

	edge e;
	edge_iterator ei;
	basic_block pred_block = NULL;
	FOR_EACH_EDGE (e, ei, current_block->preds)
	{
		pred_block = e->src;
		DEBUG ("\nRetrieving OUT value of predecessor %d of block %d", 
			pred_block->index, current_block->index);
		value_type * pred_value = current_context->get_out_value (pred_block);
		DEBUG ("\nInserting OUT value of predecessor block %d to IN value of block %d",
			pred_block->index, current_block->index);
		if (!pred_value)
			DEBUG ("\nOUT value of predecessor block %d is NULL", pred_block->index);

		// Creating copy of PRED graph and merging with IN value
		if (pred_value)
		{
			DEBUG ("\nCreating copy of predecessor graph and merging with IN value");
			bool is_loop_merge = ((block_information *)(current_block->aux))->get_loop_join ();
			if (is_loop_merge)
				DEBUG ("\nblock %d is loop join", current_block->index);
			in_value->copy_value (*pred_value, is_loop_merge);
		}
		else
		{
			// This is not an error. If GC_ON_THE_FLY, then add
			// pred_block to worklist. 
//#if GC_ON_THE_FLY
			current_context->add_block_to_worklist (pred_block);
//#endif

		}

#if DEBUG_CONTAINER
		if (pred_value)
		{
			DEBUG ("\nPRED graph");
			print_value (*pred_value);
			DEBUG ("\nIN + PRED graph");
			if (in_value)
				print_value (*in_value);
		}
#endif
	}

	// PRED_COPY may contain nodes that are not used by IN_VALUE.
	// Therefore, mark the nodes that are unreachable from IN_VALUE
	// and delete the unreachable nodes.
	in_value->clean ();

	RETURN_VOID ();
}

template <class value_type, class dept_value_type>
void forward_inter_procedural_analysis<value_type, dept_value_type>::
compute_in (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	FUNBEGIN ();

#if DEBUG_CONTAINER
	FUNCTION_NAME ();

	struct cgraph_node * cnode = current_context->get_function ();
	const char * function_name = cgraph_node_name (cnode);
	DEBUG ("\nComputing IN of block %d of function %s", current_block->index, function_name);
#endif 
	
	// bool is_value_same = false;

	if (((block_information *)(current_block->aux))->get_block_type () & START_BLOCK)
	{
		DEBUG ("\nThis is the start block. We do not calculate the IN value of a start block");
		RETURN_VOID ();
		//return;
	}

	// If there is only one predecessor of CURRENT_BLOCK, then point the
	// IN value to the OUT of that predecessor edge.
	bool success = compute_in_single_pred (current_context, current_block);

	// If there are multiple predecessors of CURRENT_BLOCK, then create a
	// new IN value.
	if (!success)
		compute_in_multiple_pred (current_context, current_block);
	else
		DEBUG ("\nBlock %d has a single predecessor", current_block->index);

	// points_to_analysis_fi needs to store a map from its in-value to
	// <context,block> at which it is valid.
#if FI_REANALYSIS
	process_in_value (current_context, current_block);
#endif

	RETURN_VOID ();
}

template <class value_type, class dept_value_type>
void forward_inter_procedural_analysis<value_type, dept_value_type>::
compute_out (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	FUNBEGIN ();

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
		print_gimple_stmt (dump_file, gsi_stmt (gsi), 0, 0);
#endif

#if DEBUG_CONTAINER
	value_type * out_value = current_context->get_out_value (current_block);
	DEBUG ("\nOut_value");
	if (out_value)
		out_value->print_value (NULL);
#endif

	if (block_type & CALL_BLOCK)
	{
		// FIXME: Put a check to make sure that this statement is the
		// only statement in the block
#if DEBUG_CONTAINER
		DEBUG ("\nCall statement: ");
		if (!(block_type & AUX_BLOCK))
		{
			gimple_stmt_iterator gsi = gsi_start_bb (current_block);
			print_gimple_stmt (dump_file, gsi_stmt (gsi), 0, 0);
		}
#endif

		// The mapping of arguments to function parameters is already
		// stored as constraints of the block if the function call is
		// direct; however, the mapping is generated on-the-fly if the
		// function call is through function pointer. These will be
		// mappings will be processed in PROCESS_CALL_STATEMENT().

		// This function propagates only arg_glob-connected nodes at
		// the IN of call-site to the function. The OUT of the
		// call-site is initialized with arg_glob-disconnected nodes of
		// the IN of call-site. Then the function-transformed
		// arg_glob-connected nodes are merged with the value at the
		// OUT of the call-site. Subsequently, the local variables of
		// the called function are deleted from the value at OUT of the
		// call-site.

		DEBUG ("\ncalling process_call_stmt()");
		process_call_statement (current_context, current_block);
	}
	else
		// Process parsed information of the block
		process_parsed_data (current_context, current_block, NULL);

	// No need to call CLEAN () here. Both the cases above ---
	// PROCESS_PARSED_DATA () and PROCESS_CALL_STATEMENT () call CLEAN ()
	// in the end.

	RETURN_VOID ();
}

template <class value_type, class dept_value_type>
void forward_inter_procedural_analysis<value_type, dept_value_type>::
copy_in_to_out (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	DEBUG ("\ncopy_in_to_out (block=%d)", current_block->index);

	value_type * in_value = current_context->get_in_value (current_block);
	// IS_LOOP_MERGE = FALSE
	DEBUG ("\nin_value->copy_value() to out_value in ipa");
	// Create a new OUT_VALUE irrespective of whether an old OUT_VALUE was
	// present. The old OUT_VALUE might be required for comparison between
	// iterations of analysis. Therefore copy_in_to_out() has been called.
	value_type * out_value = in_value->copy_value (false);
	current_context->set_out_value (current_block, out_value);

	if (!out_value)
		DEBUG ("\nout_value is NULL");
	if (!in_value)
		DEBUG ("\nin_value is NULL");

#if DEBUG_CONTAINER
	DEBUG ("\nUpdated OUT value");
	print_value (*out_value);
#endif
}

template <class value_type, class dept_value_type>
dept_value_type * forward_inter_procedural_analysis<value_type, dept_value_type>::
get_dependent_context_in_value (struct cgraph_node * function)
{
        context<dept_value_type, value_type> * dept_context =
                get_function_dependent_context (function);

        basic_block start_block = program.get_start_block_of_function (function);
        dept_value_type * callee_value = dept_context->get_in_value (start_block);
        if (!callee_value)
                RESULT ("\nError: No callee_value");

        return callee_value;
}

template <class value_type, class dept_value_type>
void forward_inter_procedural_analysis<value_type, dept_value_type>::
set_block_order (basic_block block, int rev_post_order)
{
	((block_information *)(block->aux))->set_block_order (rev_post_order);
	DEBUG ("(bb=%d,order=%d),", block->index, rev_post_order);
}

//template class forward_inter_procedural_analysis<non_deterministic_graph, deterministic_graph>; 
//template class forward_inter_procedural_analysis<non_deterministic_basic_graph, access_paths>; 
///template class forward_inter_procedural_analysis<non_deterministic_simple_graph, variables>; 
template class forward_inter_procedural_analysis<pt_node_set, variables>; 
template class forward_inter_procedural_analysis<unlabeled_edges, variables>; 
template class forward_inter_procedural_analysis<unlabeled_edges, deterministic_graph>; 
template class forward_inter_procedural_analysis<unlabeled_edges, non_deterministic_graph>; 

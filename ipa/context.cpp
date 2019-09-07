
/************************
 * @author Vini Kanvar
************************/

#include "context.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

template <class value_type, class dept_value_type>
unsigned int context<value_type, dept_value_type>::
number_of_contexts = 1;

template <class value_type, class dept_value_type>
context<value_type, dept_value_type>::
context (struct cgraph_node * fn, basic_block start_bb, basic_block end_bb, context<value_type, dept_value_type> * source_context, basic_block call_site, context<dept_value_type, value_type> * dept_context)
{
	NEW_ADDR ("\nnew context %x", this);
	context_id = number_of_contexts;
	number_of_contexts++;
	function = fn;
	start_block = start_bb;
	end_block = end_bb;
	build_block_worklist ();
	// SOURCE_CONTEXT and CALL_SITE are NULL for context in main() function
	// or if !IS_VALUE_CONTEXT
	if (source_context && call_site)
	{
		function_index fid = source_context->get_function ()->uid;
		source_contexts.insert (make_pair (source_context->context_id, call_site->index));
	}
	dependent_context = dept_context;
	aux_info = NULL;

#if DEBUG_CONTAINER
	print_context ();
	DEBUG ("\ndependent_context:");
	if (dependent_context)
		dependent_context->print_context ();
#endif
}

template <class value_type, class dept_value_type>
context<value_type, dept_value_type>::
~context ()
{
	DEBUG ("\nGC of context=%d", context_id);
	GC_ADDR ("\ngc context %x", this);

#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif

	typename map<unsigned int, value_type *>::iterator vi;
	for (vi = blocks_in_value.begin (); vi != blocks_in_value.end (); vi++)
	{
		if (vi->second)
		{
			DEBUG ("\nDeleting value at IN of block %d, context %d, function %d", vi->first, context_id, function->uid);
#if GC
			DEBUG ("\nGC value");
			// delete vi->second;
			vi->second->decrement_reference_count ();
#endif
		}
		else
			DEBUG ("\nValue is NULL");

	} 

	for (vi = blocks_out_value.begin (); vi != blocks_out_value.end (); vi++)
	{
		if (vi->second)
		{
			DEBUG ("\nDeleting value at OUT of block %d", vi->first);
#if GC
			DEBUG ("\nGC value");
			// delete vi->second;
			vi->second->decrement_reference_count ();
#endif
		}
		else
			DEBUG ("\nValue is NULL");
	}

	// aux is dependent on client. It is deleted in ipa/inter_procedural_analysis.
//	if (aux_info)
//	{
//#if GC
//		delete_aux_info (aux_info);
//		aux_info = NULL;
//#endif
//	}

	source_contexts.clear ();
	destination_contexts.clear ();
	blocks_in_value.clear ();
	blocks_out_value.clear ();
}

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
build_block_worklist ()
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif 

	int NUM_START_END_BLOCKS = 2;
	DEBUG ("\nbuild_block_worklist ()");
	struct function * function_decl = DECL_STRUCT_FUNCTION (function->decl);
	int total_blocks = n_basic_blocks_for_function (function_decl) 
			- NUM_FIXED_BLOCKS + 1 + NUM_START_END_BLOCKS;
	DEBUG ("\ntotal_blocks=%d", total_blocks);
	block_worklist.resize (total_blocks);
	block_worklist.shrink_to_fit ();
	DEBUG ("\nstart-block=%d, end-block=%d", start_block->index, end_block->index);

	// Push into the worklist the basic block with the least order-id. Do
	// not push other blocks --- they will get pushed when the IN/OUT of
	// the blocks already in worklist changes. It will change for sure in
	// the first time due to initial_value().

	if (!start_block || !end_block)
	{
		RESULT ("\nError: start_block and end_block have not been set");
		return;
	}
	if (!start_block->aux || !end_block->aux)
	{
		RESULT ("\nError: aux not initialized");
		RESULT ("\nFunction=%s, start_aux=%d, end_aux=%d", 
			cgraph_node_name (function), start_block->aux != NULL, end_block->aux != NULL);
		return;
	}

	// Only start_block (end_block) needs to be added for forward
	// (backward) analysis.  Due to exit(0), if a block is not reachable
	// from other blocks, those blocks should not be processed. We add
	// end_block (start_block) so that destination context is created.

	// unsigned int start_block_order = ((block_information *)(start_block->aux))->get_block_order ();
	// block_worklist.at (start_block_order) = start_block;
	// DEBUG ("\nstart block added");
	// unsigned int end_block_order = ((block_information *)(end_block->aux))->get_block_order ();
	// block_worklist.at (end_block_order) = end_block;
	// DEBUG ("\nend block added");

#if (SKIP_NORETURN_PATHS == 0)
	basic_block block;
	FOR_EACH_BB_FN (block, function_decl)	
	{
		unsigned int order = ((block_information *)(block->aux))->get_block_order ();
		block_worklist.at (order) = block;
	}
	DEBUG ("\nAll blocks added");
#endif

	unsigned int start_block_order = ((block_information *)(start_block->aux))->get_block_order ();
	unsigned int end_block_order = ((block_information *)(end_block->aux))->get_block_order ();
	// Forward analysis
	if (!start_block_order)	
	{
		block_worklist.at (0) = start_block;
		DEBUG ("\nstart block added");
	}
	// Backward analysis
	else if (!end_block_order)	
	{
		block_worklist.at (0) = end_block;
		DEBUG ("\nend block added");

		// The following is WRONG.

		// If our END_BLOCK is block id = 1, then it ends at all
		// control flow paths. Control flow paths are unreachable from
		// block id 1 if either there is infinite loop which does not
		// reach exit block (test29.c) or there are only exit blocks
		// and no return blocks (test56.c). In both cases, we would
		// like to say that there is backward analysis (e.g. liveness)
		// along these control flow paths.

		// block_worklist.at (0) = end_block;
		// DEBUG ("\nend block added");

		// If there is only one block containing 'return' or 'exit', it
		// can cover all control flow paths (in reverse direction)
		// starting from it. However, if there are multiple blocks
		// containing 'exit' or 'return' (e.g. test31b.c), not all
		// control flow paths get covered starting from one exit block.
		// Since backward analysis is not too costly and since adding
		// only one exit block to the worklist will not cover all
		// control flow paths, we simply add all blocks to the
		// worklist. 

		// We add all blocks only until function_side_effects is not
		// ready in backward analysis. Once function_side_effects is
		// ready, forward (allocation_site_based) analysis will push
		// only start_block; every adjacent block will get pushed if it
		// is important. Subsequent backward analysis
		// (liveness_analysis_deterministic/non_deterministic) will
		// push only end_block; every adjacent block will get pushed if
		// it is important and has a dependent forward context.

		if (!function_side_effects.get_is_unimp_blocks_ready ())
		{
			basic_block block;
			FOR_EACH_BB_FN (block, function_decl)	
			{
				unsigned int order = ((block_information *)
					(block->aux))->get_block_order ();
				block_worklist.at (order) = block;
			}
			block_worklist.at (start_block_order) = start_block;
			DEBUG ("\nAll blocks added");
		}
	}
	// else
	// {
	// 	RESULT ("\nError: order-id = 0 is not alloted to start/end block in function %s", 
	// 		cgraph_node_name (function));
	// 	return;
	// }
	DEBUG ("\nbuilding block worklist done");

	// basic_block block;
	// FOR_EACH_BB_FN (block, function_decl)	
	// {
	// 	unsigned int order = ((block_information *)(block->aux))->get_block_order ();
	//	block_worklist.at(order) = block;
	//	unsigned int block_type = ((block_information *)(block->aux))->get_block_type ();
	// }
}

/**
 * @returns true if block has been newly added.
 */

template <class value_type, class dept_value_type>
bool context<value_type, dept_value_type>::
add_block_to_worklist (basic_block block)
{
	DEBUG ("\nAdding block %d to context %d", block->index, context_id);

#if DEBUG_CONTAINER
	vector<basic_block>::iterator bi;
	DEBUG ("\nBlock worklist. size=%d: ", block_worklist.size ());
	for (bi = block_worklist.begin (); bi != block_worklist.end (); bi++)	
		if (*bi)
			DEBUG ("%d,", (*bi)->index); 
#endif
	unsigned int order = ((block_information *)(block->aux))->get_block_order ();
	DEBUG ("\nblock %d has order %d", block->index, order);

	if (block_worklist.at(order))
		return false;

	if (!function_side_effects.is_block_unimportant (function, block->index))
	{
		block_worklist.at(order) = block;
		DEBUG ("\nAdded block %d to context %d", block->index, context_id);
	}
	else
		DEBUG ("\nNot added block %d to context %d", block->index, context_id);
	return true;
}

/* THIS context is reachable from SOURCE_CONTEXT through CALL_SITE. 
 */

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
add_source_context (context<value_type, dept_value_type> * source_context, basic_block call_site)
{
	struct cgraph_node * source_function = source_context->get_function (); 

	// Add the new source edge from SOURCE_CONTEXT for THIS context.
	DEBUG ("\nAdding new source edge from src context %d to context %d", source_context->context_id, context_id);
	source_contexts.insert (make_pair (source_context->context_id, call_site->index));
}

/* THIS context reaches DESTINATION_CONTEXT (of DESTINATION_FUNCTION) through
 * CALL_SITE. 
 */

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
add_destination_context (basic_block call_site, context<value_type, dept_value_type> * destination_context) 
{
	function_index dest_fid = destination_context->get_function ()->uid;

#if DEBUG_CONTAINER
	context<value_type, dept_value_type> * prev_dest_context = get_destination_context (call_site, destination_context->get_function ());
	if (prev_dest_context)
	{
		DEBUG ("\nOverwriting previous dest edge from context %d to context %d", context_id, prev_dest_context->context_id);
	}
	else
	{
		DEBUG ("\nNo previous dest edge from context %d exists", context_id);
	}
#endif

	// Replacing previously existing edge from DESTINATION_CONTEXTS of 
	// THIS context with an edge to DESTINATION_CONTEXT.
	DEBUG ("\nAdding new dest edge from context %d to dest context %d", context_id, destination_context->context_id);
	pair<block_index, function_index> dest_edge = make_pair (call_site->index, dest_fid);
	destination_contexts[dest_edge] = destination_context;
}

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
erase_source_context (context<value_type, dept_value_type> * source_context, block_index bid)
{
	pair<context_index, block_index> p = make_pair (source_context->context_id, bid);
	if (source_contexts.erase (p))
	{
		DEBUG ("\nErased.");
	}
	else
	{
		DEBUG ("\nNot found.");
	}
}

template <class value_type, class dept_value_type>
map<block_index, value_type *> context<value_type, dept_value_type>::
get_blocks_in_value ()
{
	return blocks_in_value;
}

template <class value_type, class dept_value_type>
map<block_index, value_type *> context<value_type, dept_value_type>::
get_blocks_out_value ()
{
	return blocks_out_value;
}

template <class value_type, class dept_value_type>
set<pair<context_index, block_index> > context<value_type, dept_value_type>::
get_source_contexts ()
{
	return source_contexts;
}

template <class value_type, class dept_value_type>
map<pair<block_index, function_index>, context<value_type, dept_value_type> *> context<value_type, dept_value_type>::
get_destination_contexts ()
{
	return destination_contexts;
}

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
set_source_contexts (context_index src_cid, block_index src_bid)
{
	source_contexts.insert (make_pair (src_cid, src_bid));
}

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
set_destination_contexts (pair<block_index, function_index> & p,
	context<value_type, dept_value_type> & dest_context)
{
	destination_contexts[p] = &dest_context;
}

template <class value_type, class dept_value_type>
context<value_type, dept_value_type> * context<value_type, dept_value_type>::
get_destination_context (basic_block call_site, struct cgraph_node * cnode)
{
	if (!call_site)	
	{
		DEBUG ("\nCall site is NULL");
		return NULL;
	}

	pair<block_index, function_index> outgoing_edge = make_pair (call_site->index, cnode->uid);

	// If there is no call through CALL_SITE to function CNODE
	if (destination_contexts.find (outgoing_edge) == destination_contexts.end ())
		return NULL;

	DEBUG ("\nFound destination context");
	return destination_contexts[outgoing_edge];
}

/* A destination context is "reusable" by THIS context, i.e.  if THIS context
 * modifies/updates the values of the destination context, there are no
 * side-effects. This is because there is no other context, which uses this
 * destination context of THIS context.
 */

template <class value_type, class dept_value_type>
context<value_type, dept_value_type> * context<value_type, dept_value_type>::
get_reusable_dest_context (basic_block call_site, struct cgraph_node * dest_function)
{
#if REUSE_PROCEDURE_CONTEXT == 0
	return NULL;
#endif
  
	context<value_type, dept_value_type> * dest_context = get_destination_context (call_site, dest_function);

	// There is no reachable destination from THIS context through CALL_SITE
	if (!dest_context)
	{
		DEBUG ("\nNo previously reachable context from context %d through call site %d",
			context_id, call_site->index);
		return NULL;
	}

	// Study the SOURCE_CONTEXTS of DEST_CONTEXT, to find if any other 
	// context is also using DEST_CONTEXT
	set<pair<context_index, block_index> > srcs_of_dest = dest_context->get_source_contexts ();
	if (srcs_of_dest.size () == 1)
	{
		// This is only double checking that the only existing source
		// of DEST_CONTEXT is indeed from THIS context through CALL_SITE.
		pair<context_index, block_index> source_edge = make_pair (context_id, call_site->index);
		if (srcs_of_dest.find (source_edge) == srcs_of_dest.end ())
		{
			RESULT ("\nError: Context %d can reach %d through destination, but not the reverse way through sources",
				context_id, dest_context->context_id);
			return NULL;
		}
		DEBUG ("\nThere is only one source context of context %d which is context %d through call-site %d",
				dest_context->context_id, context_id, call_site->index);
		return dest_context;
	}

	// The reachable context DEST_CONTEXT cannot be reused, since it is 
	// being reachable from some other context too.
	return NULL;
}

template <class value_type, class dept_value_type>
context<dept_value_type, value_type> * context<value_type, dept_value_type>::
get_dependent_context ()
{
#if DEBUG_CONTAINER
	DEBUG ("\nget_dependent_context()");
	if (dependent_context)
		dependent_context->print_context ();
	DEBUG ("\nreturning dependent_context");
#endif
	return dependent_context;
}

/**
 * Gets all the contexts which are (directly or indirectly) calling the
 * CALLED_CONTEXT along any of the paths from THIS context to the
 * CALLED_CONTEXT.
 *
 * @returns true if THIS context is a (direct or indirect) caller of the
 * CALLED_CONTEXT.
 */
 
template <class value_type, class dept_value_type>
bool context<value_type, dept_value_type>::
is_caller_context (context_index called_context, set<pair<context_index, block_index> > & caller_contexts, set<context_index> & visited_contexts)
{
	if (context_id == called_context)
		return true;

	if (visited_contexts.find (context_id) != visited_contexts.end ())
	{
		// If THIS context is already identified as a caller context of
		// the CALLED_CONTEXT, return true; else return false.
		set<pair<context_index, block_index> >::iterator cci;
		for (cci = caller_contexts.begin (); cci != caller_contexts.end (); cci++)
		{
			pair<context_index, block_index> caller = *cci;
			if (context_id == caller.first)
				return true;
		}
		return false;
	}
	
	visited_contexts.insert (context_id);

	bool found_context = false;
	typename map<pair<block_index, function_index>, context<value_type, dept_value_type> *>::iterator dest_ci;
	for (dest_ci = destination_contexts.begin (); dest_ci != destination_contexts.end (); dest_ci++)
	{
		pair<block_index, function_index> call = dest_ci->first;
		context<value_type, dept_value_type> * dest_context = dest_ci->second;
		context_index dest_context_id = dest_context->context_id;
		if (dest_context->is_caller_context (called_context, caller_contexts, visited_contexts))
		{
			caller_contexts.insert (make_pair (context_id, call.first));
			found_context = true;
		}
	}

	return found_context;
}

/** This function returns true if either the context is a context of the main
 * function or there exists a source context for this context.
 */

template <class value_type, class dept_value_type>
bool context<value_type, dept_value_type>::
is_source_context_empty (function_index main_id)
{
	if (main_id == function->uid)
		return true;

	if (source_contexts.size ())
		return true;

	return false;
}

template <class value_type, class dept_value_type>
basic_block context<value_type, dept_value_type>::
get_first_block_from_worklist ()
{
	DEBUG ("\nget_first_block_from_worklist ()");
	vector<basic_block>::iterator bi;

#if 0
	bool is_context_unprocessed = !is_context_partially_processed ();
#endif
	for (bi = block_worklist.begin (); bi != block_worklist.end (); bi++)
	{
		basic_block first_block = *bi;
		if (!first_block)
			continue;

#if 0
		// Intraprocedurally eager.
		// If START block (in backward analysis) or END block (in
		// forward analysis) of THIS context is unprocessed, then pick
		// an intraprocedural block (non-call block) first (as per
		// Bageshri's interprocedural worklist management). Otherwise,
		// process blocks in reverse-post order only  (so that a
		// function pointer call is processed before its succeeding
		// blocks).
		if (is_context_unprocessed)
		{
			// If there is no intra block in the worklist, then return *BI
			basic_block bb = get_first_intra_block_from_worklist ();
			if (bb)
				return bb;
			return first_block;
		}
#endif
		return first_block;
	}
	return NULL;
}

template <class value_type, class dept_value_type>
basic_block context<value_type, dept_value_type>::
get_first_intra_block_from_worklist ()
{
	DEBUG ("\nget_first_intra_block_from_worklist ()");

	vector<basic_block>::iterator bi;
	for (bi = block_worklist.begin (); bi != block_worklist.end (); bi++)
	{
		basic_block bb = *bi;
		if (!bb)
			continue;
		if (!(((block_information *)(bb->aux))->get_block_type () & CALL_BLOCK))
			return bb;
	}
	return NULL;
}

template <class value_type, class dept_value_type>
bool context<value_type, dept_value_type>::
is_block_worklist_empty ()
{
	basic_block bb = get_first_block_from_worklist ();
	DEBUG ("\nBlock worklist of context %d is empty=%d", context_id, bb==NULL);
	return bb == NULL;
}

template <class value_type, class dept_value_type>
bool context<value_type, dept_value_type>::
is_context_partially_processed ()
{
	unsigned int start_block_order = ((block_information *)(start_block->aux))->get_block_order ();
	unsigned int end_block_order = ((block_information *)(end_block->aux))->get_block_order ();
	// If this is a forward interprocedural analysis
	if (!start_block_order)	
	{
		block_index bid = end_block->index;
		return blocks_in_value[bid] != NULL;
	}
	// If this is a backward interprocedural analysis
	else if (!end_block_order)	
	{
		block_index bid = start_block->index;
		return blocks_out_value[bid] != NULL;
	}
	else
		RESULT ("\nError: order-id = 0 is not alloted to start/end block of function %s", 
			cgraph_node_name (function));

	return false;
}

template <class value_type, class dept_value_type>
bool context<value_type, dept_value_type>::
is_block_in_worklist (basic_block block)
{
	unsigned int order = ((block_information *)(block->aux))->get_block_order ();
	return block_worklist.at(order) != NULL;
}


template <class value_type, class dept_value_type>
basic_block context<value_type, dept_value_type>::
get_block_from_worklist ()
{
	FUNBEGIN ();

	vector<basic_block>::iterator bi;

#if DEBUG_CONTAINER
	DEBUG ("\nBlock worklist. size=%d: ", block_worklist.size ());
	for (bi = block_worklist.begin (); bi != block_worklist.end (); bi++)
		if (*bi)
			DEBUG ("%d, ", (*bi)->index);
#endif 

	basic_block block = get_first_block_from_worklist ();
	DEBUG ("\nRetrieved block %d from worklist", block->index);
	unsigned int order = ((block_information *)(block->aux))->get_block_order ();
	block_worklist[order] = NULL;
	DEBUG ("\nErased block %d from worklist", block->index);

	#if CHECK_CONTAINER
	// If the basic block from the worklist has not yet been processed
	if (blocks_in_value.find (block->index) == blocks_in_value.end ())
		RESULT ("\nError: Block %d is in the worklist but its IN value has not been initialized", 
			block->index);
	if (blocks_out_value.find (block->index) == blocks_out_value.end ())
		RESULT ("\nError: Block %d is in the worklist but its OUT value has not been initialized", 
			block->index);
	#endif

#if DEBUG_CONTAINER
	DEBUG ("\nUpdated block worklist. size=%d: ", block_worklist.size ());
	for (bi = block_worklist.begin (); bi != block_worklist.end (); bi++)
		if (*bi)
			DEBUG ("%d, ", (*bi)->index);
#endif 

	RETURN (block);
	// return block;
}

template <class value_type, class dept_value_type>
unsigned int context<value_type, dept_value_type>::
get_context_id ()
{
	return context_id;
}

template <class value_type, class dept_value_type>
value_type * context<value_type, dept_value_type>::
get_in_value (basic_block block)
{
	typename map<block_index, value_type *>::iterator it = blocks_in_value.find (block->index);
	if (it == blocks_in_value.end ())
	{
		DEBUG ("\nIN value of block %d remains un-initialized", block->index);
		return NULL;
	}

	DEBUG ("\nReturning IN value of block %d from map", block->index);
	return (*it).second;
}

template <class value_type, class dept_value_type>
value_type * context<value_type, dept_value_type>::
get_out_value (basic_block block)
{
	typename map<block_index, value_type *>::iterator it = blocks_out_value.find (block->index);
	if (it == blocks_out_value.end ())
	{
		DEBUG ("\nOUT value of block %d remains un-initialized", block->index);
		return NULL;
	}

	DEBUG ("\nReturning OUT value of block %d from map", block->index);
	return (*it).second;
}

/* This function does not delete the previous values. It is the responsibility
 * of the caller to delete it.
 */

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
set_in_value (basic_block block, value_type * value)
{
	value_type * old_value = get_in_value (block);
	if (old_value)
		old_value->decrement_reference_count ();
	
	blocks_in_value[block->index] = value;
	if (value)
		value->increment_reference_count ();
}

/* This function does not delete the previous values. It is the responsibility
 * of the caller to delete it.
 */

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
set_out_value (basic_block block, value_type * value)
{
	value_type * old_value = get_out_value (block);
	if (old_value)
		old_value->decrement_reference_count ();

	blocks_out_value[block->index] = value;
	if (value)
		value->increment_reference_count ();
}

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
copy_in_value (block_index bid, value_type * value)
{
	value_type * new_v = NULL;

	// Copy value of THIS context to unique_context if it exists
	if (value && blocks_in_value.find (bid) != blocks_in_value.end ())
	{
		new_v = blocks_in_value[bid];
 		if (new_v)
		{
			new_v->copy_value (*value, false);
			return;
		}
	}

	// Create a new value if either bid does not exist or OUT value is NULL.
	if (value)
		new_v = value->copy_value (false);
	basic_block bb = get_basic_block (function, bid);
	set_in_value (bb, new_v);
}

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
copy_out_value (block_index bid, value_type * value)
{
	value_type * new_v = NULL;

	// Copy value of THIS context to unique_context if it exists
	if (value && blocks_out_value.find (bid) != blocks_out_value.end ())
	{
		new_v = blocks_out_value[bid];
 		if (new_v)
		{
			new_v->copy_value (*value, false);
			return;
		}
	}

	// Create a new value if either bid does not exist or OUT value is NULL.
	if (value)
		new_v = value->copy_value (false);
	basic_block bb = get_basic_block (function, bid);
	set_out_value (bb, new_v);
}

template <class value_type, class dept_value_type>
bool context<value_type, dept_value_type>::
is_start_value_same (value_type & value)
{
	#if CHECK_CONTAINER
	// If data flow value of start block is not present
	if (blocks_in_value.find (start_block->index) == blocks_in_value.end ())
	{
		RESULT ("\nError: IN value of start block does not exist");
		return false;
	}
	#endif

	value_type * start_value = blocks_in_value[start_block->index];
#if DEBUG_CONTAINER
	DEBUG ("\nstart value");
	if (start_value)
		start_value->print_value (NULL);
#endif

	if (start_value->is_value_same (value))
		return true;
	return false;
}

template <class value_type, class dept_value_type>
bool context<value_type, dept_value_type>::
is_end_value_same (value_type & value)
{
	#if CHECK_CONTAINER
	// If data flow value of end block is not present
	if (blocks_out_value.find (end_block->index) == blocks_out_value.end ())
	{
		RESULT ("\nError: OUT value of start block does not exist");
		return false;
	}
	#endif

	value_type * end_value = blocks_out_value[end_block->index];
	if (end_value->is_value_same (value))
		return true;
	return false;
}

/* Return true if the dependent context of THIS is the same
 * as the DEPT_CONTEXT
 */

template <class value_type, class dept_value_type>
bool context<value_type, dept_value_type>::
is_dept_context_same (context<dept_value_type, value_type> * dept_context)
{
	if (dept_context && dependent_context)
	{
        	if (dept_context->get_context_id () == dependent_context->get_context_id ())
		{
			DEBUG ("\nDependent context %d of context %d is context %d", 
				dependent_context->get_context_id (), context_id, dept_context->get_context_id ());
			return true;
		}
		else
			DEBUG ("\nDependent context %d of context %d is NOT context %d", 
				dependent_context->get_context_id (), context_id, dept_context->get_context_id ());
	}
	else if (!dept_context && !dependent_context)
	{
		DEBUG ("\nDependent context of context %d is NULL", context_id);
	        return true;
	}

	return false;
}

template <class value_type, class dept_value_type>
basic_block context<value_type, dept_value_type>::
get_start_block ()
{
	return start_block;
}

template <class value_type, class dept_value_type>
basic_block context<value_type, dept_value_type>::
get_end_block ()
{
	return end_block;
}

template <class value_type, class dept_value_type>
struct cgraph_node * context<value_type, dept_value_type>::
get_function ()
{
	return function;
}

/**
 * Copy contents of THIS context to the unique context of the corresponding
 * function.
 */

template <class value_type, class dept_value_type>
template <class dest_value_type, class dest_dept_value_type>
void context<value_type, dept_value_type>::
copy_context (context_enums<value_type, dept_value_type> & orig_program_contexts,
	map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts)
{
	function_index fid = function->uid;
	context<dest_value_type, dest_dept_value_type> * uc = unique_function_contexts[fid];

	copy_source_contexts (*uc, orig_program_contexts, unique_function_contexts);
	copy_destination_contexts (*uc, orig_program_contexts, unique_function_contexts);

	// We may not have wanted to copy the dependent context
	// if (dependent_context != uc->dependent_context)
	//	RESULT ("\nError: Cannot copy contexts of different dependent contexts");

	copy_blocks_in_value (*uc);
	copy_blocks_out_value (*uc);
}

/** 
 * Copy source_contexts of THIS context to uc_source_contexts.
 */

template <class value_type, class dept_value_type>
template <class dest_value_type, class dest_dept_value_type>
void context<value_type, dept_value_type>::
copy_source_contexts (context<dest_value_type, dest_dept_value_type> & uc,
	context_enums<value_type, dept_value_type> & orig_program_contexts,
	map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts)
{
	DEBUG ("\ncopy_source_contexts ()");
	set<pair<context_index, block_index> >::iterator sci;
	for (sci = source_contexts.begin (); sci != source_contexts.end (); sci++)
	{
		pair<context_index, block_index> p = *sci;
		context_index src_cid = p.first;
		block_index src_bid = p.second;

		context<dest_value_type, dest_dept_value_type> * unique_src_context = 
			get_unique_context (src_cid, orig_program_contexts, unique_function_contexts); 
		context_index unique_src_cid = unique_src_context->get_context_id ();

		uc.set_source_contexts (unique_src_cid, src_bid);
		DEBUG ("\n<cid=%d,bb=%d>", unique_src_cid, src_bid);
	}
}

template <class value_type, class dept_value_type>
template <class dest_value_type, class dest_dept_value_type>
void context<value_type, dept_value_type>::
copy_destination_contexts (context<dest_value_type, dest_dept_value_type> & uc,
	context_enums<value_type, dept_value_type> & orig_program_contexts,
	map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts)
{
	DEBUG ("\ncopy_destination_contexts ()");
	typename map<pair<block_index, function_index>, context<value_type, dept_value_type> *>::iterator fdci;
	for (fdci = destination_contexts.begin (); fdci != destination_contexts.end (); fdci++)
	{
		pair<block_index, function_index> p = fdci->first;
		context<value_type, dept_value_type> * dest_context = fdci->second;
		context_index dest_cid = dest_context->get_context_id ();

		context<dest_value_type, dest_dept_value_type> * unique_dest_context = 
			get_unique_context (dest_cid, orig_program_contexts, unique_function_contexts);

		uc.set_destination_contexts (p, *unique_dest_context);
		DEBUG ("\n<bb=%d,fid=%d>=cid=%d", p.first, p.second, unique_dest_context->get_context_id ());
	} 
}

/**
 * Copy blocks_in_value of THIS to uc_blocks_in_value.
 */

template <class value_type, class dept_value_type>
template <class dest_value_type, class dest_dept_value_type>
void context<value_type, dept_value_type>::
copy_blocks_in_value (context<dest_value_type, dest_dept_value_type> & unique_context)
{
	DEBUG ("\ncopy_blocks_in_value()");

	typename map<block_index, dest_value_type *>::iterator bvi;
	for (bvi = blocks_in_value.begin (); bvi != blocks_in_value.end (); bvi++)
	{
		block_index bid = bvi->first;
		dest_value_type * v = bvi->second;
		DEBUG ("\nbid=%d", bid);
		unique_context.copy_in_value (bid, v);
	}
}

template <class value_type, class dept_value_type>
template <class dest_value_type, class dest_dept_value_type>
void context<value_type, dept_value_type>::
copy_blocks_out_value (context<dest_value_type, dest_dept_value_type> & unique_context)
{
	DEBUG ("\ncopy_blocks_out_value()");

	typename map<block_index, dest_value_type *>::iterator bvi;
	for (bvi = blocks_out_value.begin (); bvi != blocks_out_value.end (); bvi++)
	{
		block_index bid = bvi->first;
		dest_value_type * v = bvi->second;

		DEBUG ("\nbid=%d", bid);
		unique_context.copy_out_value (bid, v);
	}
}

template <class value_type, class dept_value_type>
template <class dest_value_type, class dest_dept_value_type>
context<dest_value_type, dest_dept_value_type> * context<value_type, dept_value_type>::
get_unique_context (context_index orig_cid,
	context_enums<value_type, dept_value_type> & orig_program_contexts,
	map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts)
{
	DEBUG ("\nget_unique_context()");

	context<value_type, dept_value_type> * orig_context = orig_program_contexts[orig_cid];
	if (!orig_context)
	{
		RESULT ("\nError: context %d not found", orig_cid);
		return NULL;
	}
	struct cgraph_node * orig_function = orig_context->function;
	function_index orig_fid = orig_function->uid;
	context<dest_value_type, dest_dept_value_type> * unique_context = 
		unique_function_contexts[orig_fid];
	return unique_context;
}

template <class value_type, class dept_value_type>
basic_block context<value_type, dept_value_type>::
get_basic_block (struct cgraph_node * cnode, block_index bid)
{
	struct function * function_decl = DECL_STRUCT_FUNCTION (cnode->decl);
	basic_block bb = BASIC_BLOCK_FOR_FUNCTION (function_decl, bid);
	return bb;
}

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
print_block_stmts (basic_block block)
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif
	if (!block || !block->aux)
	{
		RESULT ("\nError: empty block");
		return;
	}
	unsigned int block_type = ((block_information *)(block->aux))->get_block_type ();
	DEBUG ("\nBlock %d (block type %d), ", block->index, block_type);
}

template <class value_type, class dept_value_type>
int context<value_type, dept_value_type>::
get_max_call_chain_len (map<context_index, int> & call_chain_len, int inf)
{
	if (call_chain_len[context_id] >= inf)
		return inf;

	int max_len = 0;
	set<pair<context_index, block_index> >::iterator srci;
	for (srci = source_contexts.begin (); srci != source_contexts.end (); srci++)
	{
		context_index cid = srci->first;
		int src_len = call_chain_len[cid] + 1;
		if (max_len < src_len)
			max_len = src_len;
	}
	return max_len;
}

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
get_destination_contexts (set<context<value_type, dept_value_type> *> & dest_contexts)
{
	typename map<pair<block_index, function_index>, context<value_type, dept_value_type> *>::iterator di;
	for (di = destination_contexts.begin (); di != destination_contexts.end (); di++)
	{
		context<value_type, dept_value_type> * d = di->second;
		dest_contexts.insert (d);
	}	
}

template <class value_type, class dept_value_type>
void * context<value_type, dept_value_type>::
get_aux_info ()
{
	return aux_info;
}

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
set_aux_info (void * info)
{
	aux_info = info;
}

template <class value_type, class dept_value_type>
void * context<value_type, dept_value_type>::
get_dest_aux_info (basic_block call_site, 
	struct cgraph_node * dest_function)
{
	context<value_type, dept_value_type> * dest_context = 
		get_destination_context (call_site, dest_function);
	if (!dest_context)
	{
		RESULT ("\nError: context of dest_function=%s from call_site=%d not found",
			cgraph_node_name (dest_function), call_site->index);
		return NULL;
	}
	DEBUG ("\nFound dest_context=%d", dest_context->context_id);
	void * info = dest_context->get_aux_info ();
	if (!info)
		RESULT ("\nError: aux_info of dest_context=%d is NULL", dest_context->context_id);

	return info;
}

/**
 * This function accumulates all the direct and indirect callers of each
 * context until fixed point. If a caller is called by itself, then it is a
 * recursive function.
 */

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
find_recursive_functions (map<context_index, set<context_index> > & callers,	
	set<function_index> & recursive_fns)
{
	typename map<pair<block_index, function_index>, context<value_type, dept_value_type> *>::iterator fdci;
	for (fdci = destination_contexts.begin (); fdci != destination_contexts.end (); fdci++)
	{
		context<value_type, dept_value_type> * dest_context = fdci->second;
		DEBUG ("\ncurr context=%d,fn=%d. Dest context=%d,fn=%d",
			context_id, function->uid, dest_context->context_id, dest_context->function->uid);

		bool is_same = dest_context->add_callers (context_id, callers, recursive_fns);
		if (!is_same)
			dest_context->find_recursive_functions (callers, recursive_fns);
	} 
}

template <class value_type, class dept_value_type>
bool context<value_type, dept_value_type>::
add_callers (context_index new_caller,
	map<context_index, set<context_index> > & callers,
	set<function_index> & recursive_fns)
{
	set<context_index> old_callers = callers[context_id];

	callers[context_id].insert (new_caller);
	set<context_index> callers_of_caller = callers[new_caller];
	callers[context_id].insert (callers_of_caller.begin (), callers_of_caller.end ());

	set<context_index> new_callers = callers[context_id];

	if (new_callers.find (context_id) != new_callers.end ())
		recursive_fns.insert (function->uid);
	
	if (old_callers.size () != new_callers.size ())
		return false;
	return (old_callers == new_callers);
}

template <class value_type, class dept_value_type>
void context<value_type, dept_value_type>::
print_context ()
{
	RESULT ("\nFunction: %s", cgraph_node_name (function));
	RESULT ("\nBlock worklist of context %d. size=%d: ", context_id, block_worklist.size ());
	vector<basic_block>::iterator bi;
	for (bi = block_worklist.begin (); bi != block_worklist.end (); bi++)
	{
		if (!*bi) continue;
		basic_block block = *bi;
		DEBUG ("%d,", block->index);
		//print_block_stmts (*bi);
	}

	#if 0
	typename map<block_index, value_type *>::iterator biv;
	for (biv = blocks_in_value.begin (); biv != blocks_in_value.end (); biv++)
	{
		block_index b = biv->first;
		value_type * iv = biv->second;
		RESULT ("\nBlock in=%d", b);
		if (iv)
			iv->print_value (NULL);
		else
			RESULT ("\nNULL");
	}
	typename map<block_index, value_type *>::iterator bov;
	for (bov = blocks_out_value.begin (); bov != blocks_out_value.end (); bov++)
	{
		block_index b = bov->first;
		value_type * ov = bov->second;
		RESULT ("\nBlock out=%d", b);
		if (ov)
			ov->print_value (NULL);
		else
			RESULT ("\nNULL");
	}
	#endif
	RESULT ("\nprinted context");
}

//template class context<access_paths, non_deterministic_basic_graph>; 
//template class context<variables, non_deterministic_simple_graph>; 
//template class context<non_deterministic_graph, deterministic_graph>; 
//template class context<non_deterministic_basic_graph, access_paths>; 
//template class context<non_deterministic_simple_graph, variables>; 
//template class context<deterministic_graph, non_deterministic_graph>; 
template class context<pt_node_set, variables>; 
template class context<unlabeled_edges, variables>; 
template class context<variables, pt_node_set>; 
template class context<variables, unlabeled_edges>; 
template class context<deterministic_graph, unlabeled_edges>; 
template class context<non_deterministic_graph, unlabeled_edges>; 
template class context<unlabeled_edges, deterministic_graph>; 
template class context<unlabeled_edges, non_deterministic_graph>; 

template void context<unlabeled_edges, variables>::
copy_source_contexts (context<unlabeled_edges, deterministic_graph> & uc,
	context_enums<unlabeled_edges, variables> & orig_program_contexts,
	map<function_index, context<unlabeled_edges, deterministic_graph> *> & unique_function_contexts);

template void context<unlabeled_edges, variables>::
copy_source_contexts (context<unlabeled_edges, non_deterministic_graph> & uc,
	context_enums<unlabeled_edges, variables> & orig_program_contexts,
	map<function_index, context<unlabeled_edges, non_deterministic_graph> *> & unique_function_contexts);

template void context<unlabeled_edges, variables>::
copy_destination_contexts (context<unlabeled_edges, deterministic_graph> & uc,
	context_enums<unlabeled_edges, variables> & orig_program_contexts,
	map<function_index, context<unlabeled_edges, deterministic_graph> *> & unique_function_contexts);
template void context<unlabeled_edges, variables>::
copy_destination_contexts (context<unlabeled_edges, non_deterministic_graph> & uc,
	context_enums<unlabeled_edges, variables> & orig_program_contexts,
	map<function_index, context<unlabeled_edges, non_deterministic_graph> *> & unique_function_contexts);

template void context<unlabeled_edges, variables>::
copy_blocks_in_value (context<unlabeled_edges, deterministic_graph> & unique_context);
template void context<unlabeled_edges, variables>::
copy_blocks_in_value (context<unlabeled_edges, non_deterministic_graph> & unique_context);

template void context<unlabeled_edges, variables>::
copy_blocks_out_value (context<unlabeled_edges, deterministic_graph> & unique_context);
template void context<unlabeled_edges, variables>::
copy_blocks_out_value (context<unlabeled_edges, non_deterministic_graph> & unique_context);

template context<unlabeled_edges, deterministic_graph> * context<unlabeled_edges, variables>::
get_unique_context (context_index orig_cid,
	context_enums<unlabeled_edges, variables> & orig_program_contexts,
	map<function_index, context<unlabeled_edges, deterministic_graph> *> & unique_function_contexts);
template context<unlabeled_edges, non_deterministic_graph> * context<unlabeled_edges, variables>::
get_unique_context (context_index orig_cid,
	context_enums<unlabeled_edges, variables> & orig_program_contexts,
	map<function_index, context<unlabeled_edges, non_deterministic_graph> *> & unique_function_contexts);

template void context<unlabeled_edges, variables>::
copy_context (context_enums<unlabeled_edges, variables> & orig_program_contexts,
	map<function_index, context<unlabeled_edges, deterministic_graph> *> & unique_function_contexts);
template void context<deterministic_graph, unlabeled_edges>::
copy_context (context_enums<deterministic_graph, unlabeled_edges> & orig_program_contexts,
	map<function_index, context<deterministic_graph, unlabeled_edges> *> & unique_function_contexts);
template void context<unlabeled_edges, variables>::
copy_context (context_enums<unlabeled_edges, variables> & orig_program_contexts,
	map<function_index, context<unlabeled_edges, non_deterministic_graph> *> & unique_function_contexts);
template void context<non_deterministic_graph, unlabeled_edges>::
copy_context (context_enums<non_deterministic_graph, unlabeled_edges> & orig_program_contexts,
	map<function_index, context<non_deterministic_graph, unlabeled_edges> *> & unique_function_contexts);


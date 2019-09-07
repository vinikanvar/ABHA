
/************************
 * @author Vini Kanvar
************************/

#include "inter_procedural_analysis.hh"

#if UNSOUND_FUNC_PTR
#define FUNCTION_POINTER 0
#else
#define FUNCTION_POINTER 1
#endif

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

template <class value_type, class dept_value_type>
inter_procedural_analysis<value_type, dept_value_type>::
inter_procedural_analysis ()
{
	dependent_analysis = NULL;
}

template <class value_type, class dept_value_type>
inter_procedural_analysis<value_type, dept_value_type>::
~inter_procedural_analysis ()
{
	DEBUG ("\nGC of IPA");

#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif
	delete_contexts ();
	program_contexts.clear ();
	function_contexts_map.clear ();
	context<value_type, dept_value_type>::number_of_contexts = 1;
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
delete_contexts ()
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif

	typename map<unsigned int, context_enums<value_type, dept_value_type> >::iterator ci;
	for (ci = function_contexts_map.begin (); ci != function_contexts_map.end (); ci++)
	{
		context_enums<value_type, dept_value_type> ce = ci->second;
		typename context_enums<value_type, dept_value_type>::iterator vi;
		for (vi = ce.begin (); vi != ce.end (); vi++)
		{
			context<value_type, dept_value_type> * c = vi->second;
#if GC
			DEBUG ("\nGC context %d, %x", vi->first, c);
			delete c;
#endif
		}
	}
}

/**
 * virtual function delete_aux_info() cannot be called from
 * ~inter_procedural_analysis() as destructor of derived client analysis has
 * already been called. Therefore, this is called from destructor of the
 * derived client analysis.
 */

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
delete_context_aux_info ()
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif

	DEBUG ("\ndelete_context_aux_info function_contexts size=%d", function_contexts_map.size ());
	typename map<unsigned int, context_enums<value_type, dept_value_type> >::iterator ci;
	for (ci = function_contexts_map.begin (); ci != function_contexts_map.end (); ci++)
	{
		DEBUG ("\ndelete function %d", ci->first);
		context_enums<value_type, dept_value_type> ce = ci->second;
		typename context_enums<value_type, dept_value_type>::iterator vi;
		for (vi = ce.begin (); vi != ce.end (); vi++)
		{
			context<value_type, dept_value_type> * c = vi->second;
			DEBUG ("\ndelete context=%d", c->get_context_id ());
			delete_aux_info (c->get_aux_info ());
		}
	}
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
initialize_block_worklist (context<value_type, dept_value_type> * current_context)
{
	struct timeval start;
	start_timer(start);

	struct cgraph_node * cnode = current_context->get_function ();
#if DEBUG_CONTAINER
	const char * function_name = cgraph_node_name (cnode);
	DEBUG ("\nInitializing worklist of function %s", function_name);
#endif
	struct function * function_decl = DECL_STRUCT_FUNCTION (cnode->decl);
	basic_block block;
	FOR_EACH_BB_FN (block, function_decl)
	{
		DEBUG ("\nInitializing IN and OUT of block %d", block->index);
		// Unless a block is analyzed in analyze_block (), we set NULL value.
		current_context->set_in_value (block, NULL);
		current_context->set_out_value (block, NULL);
		// current_context->set_in_value (block, initial_value ());
		// current_context->set_out_value (block, initial_value ());
	}
        basic_block startbb = current_context->get_start_block ();
        basic_block endbb = current_context->get_end_block ();
	current_context->set_in_value (startbb, NULL);
	current_context->set_out_value (startbb, NULL);
	current_context->set_in_value (endbb, NULL);
	current_context->set_out_value (endbb, NULL);

	stop_timer (start, initialize_block_worklist_stats);
}

template <class value_type, class dept_value_type>
context<value_type, dept_value_type> * inter_procedural_analysis<value_type, dept_value_type>::
get_context_from_worklist ()
{
	FUNBEGIN ();
	
	DEBUG ("\nget_context_from_worklist ()");

	if (context_worklist.empty ())
		RETURN (NULL);
		// return NULL;

	//typename set<context<value_type, dept_value_type> *>::iterator it = context_worklist.begin();
	context<value_type, dept_value_type> * curr_context = context_worklist.top();

	if (!curr_context)
		RESULT ("\nError: CONTEXT_WORKLIST is empty");

	// Return the context only if it is either a context of the main
	// function or it is being used, i.e. it has a source context and its
	// BLOCK_WORKLIST is not empty.
	// or if it is a functional based inter procedural context
	if ((curr_context->is_source_context_empty (program.main_cnode->uid) || !is_value_context)
		&& !curr_context->is_block_worklist_empty ())
	{
#if DEBUG_CONTAINER
		DEBUG ("\nTop context %d", curr_context->get_context_id ());
#endif
		RETURN (curr_context);
		// return curr_context;
	}

	DEBUG ("\nPopping context %d", curr_context->get_context_id ());

	// Remove the context from the worklist if it is not supposed to be
	// processed (since there is no source context for it) or its
	// BLOCK_WORKLIST is empty.
	context_worklist.pop ();

//#if GC_ON_THE_FLY
	// Free all block values of curr_context if no context is reachable from it
	free_context_analysis_values (*curr_context);
//#endif

	// Do not delete the context if there is no source context, since it
	// may in the future find a source; it is at that time that this
	// context can be used. On the other hand, it might be useful to delete
	// the context in order to save space.
	// delete current_context;

	// Get the next valid top context
	RETURN (get_context_from_worklist ());
	// return get_context_from_worklist ();
}

template <class value_type, class dept_value_type>
bool inter_procedural_analysis<value_type, dept_value_type>::
is_reachable_context_unprocessed (context<value_type, dept_value_type> & curr_context,
	set<context_index> & reachable_contexts)
{
	context_index context_id = curr_context.get_context_id ();
	if (reachable_contexts.find (context_id) != reachable_contexts.end ())
		return false;

	if (is_context_in_worklist (&curr_context))
		return true;

	reachable_contexts.insert (context_id);

	typename map<pair<block_index, function_index>, context<value_type, dept_value_type> *>::iterator ci;
	map<pair<block_index, function_index>, context<value_type, dept_value_type> *> dest_contexts = 
		curr_context.get_destination_contexts ();
	for (ci = dest_contexts.begin (); ci != dest_contexts.end (); ci++)
	{
		context<value_type, dept_value_type> * dest = ci->second;
		DEBUG ("\ndest context=%d", dest->get_context_id ());
		if (is_reachable_context_unprocessed (*dest, reachable_contexts))
			return true;
	}

	return false;
}

template <class value_type, class dept_value_type>
unsigned int inter_procedural_analysis<value_type, dept_value_type>::
get_context_enums_size (unsigned int function_uid)
{
	return function_contexts_map[function_uid].size ();
}

template <class value_type, class dept_value_type>
context_enums<value_type, dept_value_type> inter_procedural_analysis<value_type, dept_value_type>::
get_context_enums (unsigned int function_uid)
{
	return function_contexts_map[function_uid];
}

/** Find the destination context in dependent analysis i.e. context reached from
 *  dependent context of SRC_CONTEXT through call site CALL_SITE. 
 */

template <class value_type, class dept_value_type>
context<dept_value_type, value_type> * inter_procedural_analysis<value_type, dept_value_type>::
get_dest_of_dept_context (context<value_type, dept_value_type> * src_context, basic_block call_site, struct cgraph_node * dest_function)
{
	DEBUG ("\nget_dest_of_dept_context (src=%d, call_site=%d, dest_function=%s)",
		src_context->get_context_id (), call_site->index, cgraph_node_name (dest_function));
	if (!dependent_analysis)
	{
		DEBUG ("\nThere is no dependent context");
		return NULL;
	}

	context<dept_value_type, value_type> * src_dept_context = src_context->get_dependent_context ();
	if (!src_dept_context)
	{
		DEBUG ("\nsrc_dept_context is NULL");
		return NULL;
	}
	DEBUG ("\nsrc_dept_context=%d", src_dept_context->get_context_id ());

	context<dept_value_type, value_type> * dest_dept_context = 
			src_dept_context->get_destination_context (call_site, dest_function);
	if (!dest_dept_context)
	{
		DEBUG ("\nDependent analysis does not handle function call in block %d", call_site->index);
		return NULL;
	}
	DEBUG ("\nDest of dept context %d of context %d is %d", 
		src_dept_context->get_context_id (), src_context->get_context_id (), dest_dept_context->get_context_id ());
	return dest_dept_context;
}

template <class value_type, class dept_value_type>
bool inter_procedural_analysis<value_type, dept_value_type>::
get_is_value_context ()
{
	return is_value_context;
}

template <class value_type, class dept_value_type>
context<dept_value_type, value_type> * inter_procedural_analysis<value_type, dept_value_type>::
get_dependent_context (context<value_type, dept_value_type> * curr_context)
{
	if (!dependent_analysis)
		return NULL;

	if (dependent_analysis->get_is_value_context ())
		return curr_context->get_dependent_context ();

	struct cgraph_node * function = curr_context->get_function ();
	return dependent_analysis->get_function_context (function);
}

template <class value_type, class dept_value_type>
context<value_type, dept_value_type> * inter_procedural_analysis<value_type, dept_value_type>::
get_function_context (struct cgraph_node * function)
{
	// This function is called when there is one context per function

	context_enums<value_type, dept_value_type> ce = get_context_enums (function->uid);
	if (ce.size () > 1)
	{
		RESULT ("\nError: function=%d has more than one summary", function->uid);
		return NULL;
	}
	if (ce.size () == 1)
		return (ce.begin ())->second;

	return NULL;
}

template <class value_type, class dept_value_type>
context<dept_value_type, value_type> * inter_procedural_analysis<value_type, dept_value_type>::
get_function_dependent_context (struct cgraph_node * function)
{
        inter_procedural_analysis<dept_value_type, value_type> * dept_analysis =
                get_dependent_analysis ();

        if (!dept_analysis)
        {
                RESULT ("\nError: No dependent analysis");
                return NULL;
        }

#if MOVP == 0
	if (dept_analysis->is_value_context)
	{
		RESULT ("\nError: Function=%d is not functional context", function->uid);
		return NULL;
	}
#endif

        context<dept_value_type, value_type> * dept_context =
                dept_analysis->get_function_context (function);

        if (!dept_context)
        {
                RESULT ("\nError: No dependent context");
                return NULL;
        }

	return dept_context;
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
set_function_contexts_map (function_index fid,
	context_index cid, 
	context<value_type, dept_value_type> & c)
{
	function_contexts_map[fid][cid] = &c;
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
set_program_context (context_index cid, 
	context<value_type, dept_value_type> & c)
{
	program_contexts[cid] = &c;
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
set_dependent_analysis (inter_procedural_analysis<dept_value_type, value_type> * dept_analysis)
{
	dependent_analysis = dept_analysis;
}

template <class value_type, class dept_value_type>
inter_procedural_analysis<dept_value_type, value_type> * inter_procedural_analysis<value_type, dept_value_type>::
get_dependent_analysis ()
{
	return dependent_analysis;
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
get_source_contexts (context<value_type, dept_value_type> & con,
	set<context<value_type, dept_value_type> *> & source_contexts)
{
	set<pair<context_index, block_index> > src_cids = con.get_source_contexts ();
	set<pair<context_index, block_index> >::iterator sci;
	for (sci = src_cids.begin (); sci != src_cids.end (); sci++)
	{
		context_index scid = sci->first;
		context<value_type, dept_value_type> * sc = get_context (scid);
		source_contexts.insert (sc);
	}
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
get_destination_contexts (context<value_type, dept_value_type> & con,
	map<pair<block_index, function_index>, context<value_type, dept_value_type> *> & destination_contexts)
{
	destination_contexts = con.get_destination_contexts ();
}

template <class value_type, class dept_value_type>
bool inter_procedural_analysis<value_type, dept_value_type>::
is_context_in_worklist (context<value_type, dept_value_type> * new_context)
{
	context_index cid = new_context->get_context_id ();

	stack<context<value_type, dept_value_type> *> temp;
	for (temp = context_worklist; !temp.empty (); temp.pop ())
	{
		context<value_type, dept_value_type> * wc = temp.top ();
		context_index wcid = wc->get_context_id ();
		if (wcid == cid)
			return true;
	}
	return false;
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
add_context_to_worklist (context<value_type, dept_value_type> * new_context)
{
	if (!new_context)
		RESULT ("\nError: Trying to insert a NULL context");

	DEBUG ("\nAdded Context %d of function %d to the worklist", 
		new_context->get_context_id (), new_context->get_function ()->uid);

	context_worklist.push (new_context);	
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
add_dependent_context_to_worklist (context<value_type, dept_value_type> * current_context, basic_block current_block)
{
	DEBUG ("\nadd_dependent_context_to_worklist()");

	if (!dependent_analysis)
	{
		DEBUG ("\ndependent_analysis is NULL");
		return;
	}

	context<dept_value_type, value_type> * dept_context = current_context->get_dependent_context ();

	if (!dept_context)
	{
		DEBUG ("\ndept_context is NULL");
		return;
	}

	dept_context->add_block_to_worklist (current_block);

	// Dependent context might not have been in the worklist.
	dependent_analysis->add_context_to_worklist (dept_context);
}

/**
 * This function adds contexts whose call-site blocks need reprocessing. This
 * function is called when SRC_CONTEXT makes a call to an
 * EXISTING_DEST_CONTEXT; however the context-transition graph has not been
 * updated yet. Due to this call, some contexts become a part of recursion with
 * SRC_CONTEXT; in which case the call-site blocks of such contexts are added
 * to the worklist for reprocessing so that local variables are no more deleted
 * at the out of call-site block (in case of forward analysis) and at the in of
 * call-site block (in case of backward analysis). 
 */

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
update_context_worklist (context<value_type, dept_value_type> & src_context, context<value_type, dept_value_type> & existing_dest_context, struct cgraph_node * dest_function)
{
	context_index src_context_id = src_context.get_context_id ();
	context_index existing_dest_context_id = existing_dest_context.get_context_id ();

	// Get CALLER_CONTEXTS which will become a part of recursion with the
	// SRC_CONTEXT, i.e. the contexts which are callers of the SRC_CONTEXT
	// starting from EXISTING_DEST_CONTEXT. 
	set<pair<context_index, block_index> > caller_contexts;
	set<context_index> visited_contexts;

	// We do not add CALL_SITE of SRC_CONTEXT to the worklist --- it will
	// need reprocessing later if the END block of EXISTING_DEST_CONTEXT
	// changes; in which case CALL_SITE of SRC_CONTEXT will be
	// automatically added to the worklist.	
	visited_contexts.insert (src_context_id);
	existing_dest_context.is_caller_context (src_context_id, caller_contexts, visited_contexts);
#if DEBUG_CONTAINER
	set<pair<context_index, block_index> >::iterator ci;
	DEBUG ("\nContexts in recursion with src_context %d starting from existing_dest_context %d: ",
		src_context_id, existing_dest_context.get_context_id ());
	for (ci = caller_contexts.begin (); ci != caller_contexts.end (); ci++)
	{
		pair<context_index, block_index> caller = *ci;
		DEBUG ("(%d,%d),", caller.first, caller.second);
	}
#endif

	// Prepare a list of contexts whose call-site blocks need to be
	// reprocessed so that local variables are not deleted this time. To
	// elaborate, a context needs to be reprocessed if it is in the
	// CALLER_CONTEXTS list (i.e. it will become a part of recursion with
	// SRC_CONTEXT) and it was earlier not in recursion with DEST_FUNCTION.
	set<pair<context_index, block_index> > reprocess_contexts;
	set<pair<context_index, block_index> >::iterator cci;
	for (cci = caller_contexts.begin (); cci != caller_contexts.end (); cci++)
	{
		pair<context_index, block_index> caller = *cci;
		context<value_type, dept_value_type> * caller_context = get_context (caller.first);
		visited_contexts.clear ();
		if (!is_recursively_called (dest_function, *caller_context, visited_contexts))
			reprocess_contexts.insert (caller);
	}
#if DEBUG_CONTAINER
	DEBUG ("\nContexts which need reprocessing: ");
	for (ci = reprocess_contexts.begin (); ci != reprocess_contexts.end (); ci++)
	{
		pair<context_index, block_index> caller = *ci;
		DEBUG ("(%d,%d),", caller.first, caller.second);
	}
#endif

	// Add call-sites blocks to the worklist for reprocessing.
	set<pair<context_index, block_index> >::iterator rci;
	for (rci = reprocess_contexts.begin (); rci != reprocess_contexts.end (); rci++)
	{
		pair<context_index, block_index> caller = *rci;
		context_index caller_context_id = caller.first;
		block_index call_site_id = caller.second;
		context<value_type, dept_value_type> * reprocess_context = get_context (caller_context_id);
		struct cgraph_node * caller_function = reprocess_context->get_function ();
		basic_block call_site = get_block_of_function (caller_function, call_site_id);
		if (!call_site)
		{
			RESULT ("\nError: call_site %d block is null", call_site_id);
			continue;
		}
		reprocess_context->add_block_to_worklist (call_site);
		add_context_to_worklist (reprocess_context);
		DEBUG ("\nAdded call-site block %d of reprocess_context %d", 
			call_site_id, caller_context_id);
	}

#if DEBUG_CONTAINER
	DEBUG ("\nprint_context_worklist()");
	print_context_worklist ();
#endif
}

/**
 * This function deletes both the local and formal parameters of the
 * CALLED_FUNCTION, since neither of them will be used by the calling function.
 * However, if the CALLED_FUNCTION has a context in the history calls of
 * SRC_CONTEXT, then we should not delete any variables. This is because we
 * cannot differentiate between the nodes created by CALLED_FUNCTION called
 * from the SRC_CONTEXT and those created by the history context of the
 * CALLED_FUNCTION.
 * FIXME: Do no delete address escaped variables; delete the rest.
 */

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
check_and_delete_local_variables (context<value_type, dept_value_type> & src_context, 
	struct cgraph_node * called_function, 
	value_type & value,
	void * info)
{
	FUNBEGIN ();

	set<context_index> visited_contexts;
	bool called = is_recursively_called (called_function, src_context, visited_contexts);
#if DEBUG_CONTAINER
	set<context_index>::iterator vci;
	DEBUG ("\nVisited contexts:");
	for (vci = visited_contexts.begin (); vci != visited_contexts.end (); vci++)
		DEBUG ("%d,", *vci);
	DEBUG ("\nContext %d is recursively called=%d", 
		src_context.get_context_id (), called);
#endif

	if (!called)
	{
		DEBUG ("\nDeleting local variables of context %d", 
			src_context.get_context_id ());
		delete_local_variables (src_context.get_function (), called_function, value, info);
	}
	// FIXME: Delete temporary variables -- they are never address escaped
	else
		DEBUG ("\nNOT deleting local variables of context %d", 
			src_context.get_context_id ());

#if DEBUG_CONTAINER
	DEBUG ("\nout_value without any local variables");
	value.print_value (NULL);
#endif

	RETURN_VOID ();
}

/**
 * This function deletes both the local and formal parameters of the
 * CALLED_FUNCTION, since neither of them will be used by the calling function.
 * However, if the CALLED_FUNCTION has a context in the history calls of any
 * context of SRC_FUNCTION, then we should not delete any variables. This is
 * because we cannot differentiate between the nodes created by CALLED_FUNCTION
 * called from the SRC_CONTEXT and those created by the history context of the
 * CALLED_FUNCTION.
 * FIXME: Do no delete address escaped variables; delete the rest.
 */

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
check_and_delete_local_variables (struct cgraph_node * src_function, 
	struct cgraph_node * called_function, 
	value_type & value,
	void * info)
{
	FUNBEGIN ();

	bool called = false;

	// Get all SRC_CONTEXT of SRC_FUNCTION.
	context_enums<value_type, dept_value_type> src_contexts = 
		function_contexts_map[src_function->uid];

	// Check if any of the SRC_CONTEXTs is recursively called by CALLED_FUNCTION
	typename context_enums<value_type, dept_value_type>::iterator ci;
	for (ci = src_contexts.begin (); ci != src_contexts.end (); ci++)
	{
		context<value_type, dept_value_type> * src_context = ci->second;
		set<context_index> visited_contexts;
		called = is_recursively_called (called_function, *src_context, visited_contexts);
#if DEBUG_CONTAINER
		set<context_index>::iterator vci;
		DEBUG ("\nVisited contexts:");
		for (vci = visited_contexts.begin (); vci != visited_contexts.end (); vci++)
			DEBUG ("%d,", *vci);
		DEBUG ("\nContext %d is recursively called=%d", 
			src_context->get_context_id (), called);
#endif
		if (called)
			break;
	}

	if (!called)
	{
		DEBUG ("\nDeleting local variables of function %d", 
			src_function->uid);
		delete_local_variables (src_function, called_function, value, info);
	}
	else
		DEBUG ("\nNOT deleting local variables of function %d", 
			src_function->uid);

#if DEBUG_CONTAINER
	DEBUG ("\nout_value without any local variables");
	value.print_value (NULL);
#endif

	RETURN_VOID ();
}

template <class value_type, class dept_value_type>
context<value_type, dept_value_type> * inter_procedural_analysis<value_type, dept_value_type>::
add_new_context (struct cgraph_node * cnode, value_type * boundary_value, context<value_type, dept_value_type> * source_context, basic_block call_site, context<dept_value_type, value_type> * dependent_context)
{
	DEBUG ("\nadd_new_context");

	basic_block start_block = program.get_start_block_of_function (cnode);
	basic_block end_block = program.get_end_block_of_function (cnode);
	if (!start_block)
		RESULT ("\nError: start block could not be retrieved");
	if (!end_block)
		RESULT ("\nError: end block could not be retrieved");

	context<value_type, dept_value_type> * new_context = new context<value_type, dept_value_type> 
		(cnode, start_block, end_block, source_context, call_site, dependent_context);
#if DEBUG_CONTAINER
	const char * function_name = cgraph_node_name (cnode);
	DEBUG ("\nCreated new context %d for function %s", new_context->get_context_id (), function_name);
#endif

	// analyze_block () sets initial values of IN and OUT of all blocks,
	// the boundary value of the start block in a forward flow analysis and
	// end block in a backward flow analysis.
	// Here we set IN and OUT values of blocks to NULL.
	initialize_block_worklist (new_context);

	context_enums<value_type, dept_value_type> ce;
	if (function_contexts_map.find (cnode->uid) != function_contexts_map.end ())
	{
		DEBUG ("\nA set of contexts of function %d exists", cnode->uid);
		ce =  function_contexts_map[cnode->uid];
	}
	else
		DEBUG ("\nNo context for function %d exists", cnode->uid);

	ce[new_context->get_context_id ()] = new_context;
	function_contexts_map[cnode->uid] = ce;

#if DEBUG_CONTAINER
	typename context_enums<value_type, dept_value_type>::iterator it;
	DEBUG ("\nContexts in function %d are: ", cnode->uid);
	for (it = ce.begin (); it != ce.end (); it++)
		DEBUG ("%d, ", it->first);
#endif 

	program_contexts[new_context->get_context_id ()] = new_context;
	DEBUG ("\nAdded new context %d to function_contexts_map", 
		new_context->get_context_id ());
	set_boundary_value (new_context, boundary_value);

	// Add the new context to the worklist
	add_context_to_worklist (new_context);
	DEBUG ("\nAdded Context %d of function %s to the worklist", 
		new_context->get_context_id (), function_name);

	return new_context;
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
analyze_program ()
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif

	if (is_value_context)
	{
		DEBUG ("\nis_value_context");
		if (!program.main_cnode)
		{
			RESULT ("\nError: main not found");
			return;
		}
		DEBUG ("\nprogram.main_cnode = %s", cgraph_node_name (program.main_cnode));
		create_start_context (program.main_cnode, boundary_value ());
	}
	else
	{
		DEBUG ("\nis_value_context = 0");
		create_all_contexts ();
	}
	analyze_context_worklist ();

#if DEBUG_CONTAINER
	program.print_variable_data ();
#endif
	DEBUG ("\nanalyze_program done");
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
create_start_context (struct cgraph_node * start_function, value_type * start_value)
{
	FUNBEGIN ();

	DEBUG ("\ncreate_global_context ()");

	if (!start_function)
	{
		DEBUG ("\nStart function is NULL");
		return;
	}

	context<dept_value_type, value_type> * dependent_context;

	// Retrieve the dependent context of context in FUNCTION 
	if (dependent_analysis && dependent_analysis->get_is_value_context ())
	{
                context_enums<dept_value_type, value_type> ce = 
			dependent_analysis->get_context_enums (start_function->uid);
		// START_FUNCTION has only one context
	        typename context_enums<dept_value_type, value_type>::iterator ci = ce.begin ();
		if (ci != ce.end ())
		{
                	dependent_context = ci->second;
			DEBUG ("\nDependent context of global() is %d", 
				dependent_context->get_context_id ());
		}
		else
		{
			DEBUG ("\nDependent context of start_function is NULL");
			dependent_context = NULL;
		}
	}
	else
		dependent_context = NULL;

	add_new_context (start_function, start_value, NULL, NULL, dependent_context);

	RETURN_VOID ();
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
create_all_contexts ()
{
	DEBUG ("\ncreate_all_contexts ()");

	if (is_value_context)
	{
		RESULT ("\nError: This is not summary based inter proc analysis");
		return;
	}

	set<struct cgraph_node *> functions;
	struct cgraph_node * cnode;
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next)
	{
		if (DECL_STRUCT_FUNCTION (cnode->decl))
			add_new_context (cnode, boundary_value (), NULL, NULL, NULL);
	}
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
analyze_context_worklist ()
{
	FUNBEGIN ();

	DEBUG ("\nanalyze_context_worklist ()");

	context<value_type, dept_value_type> * current_context;
	while (current_context = get_context_from_worklist ())
	{
#if DEBUG_CONTAINER
		DEBUG ("\nContext %d retrieved from context-worklist", current_context->get_context_id ());
		struct cgraph_node * cnode = current_context->get_function ();
		const char * function_name = cgraph_node_name (cnode);
		DEBUG ("\nFunction %s\n", function_name);

	        struct function * function_decl = DECL_STRUCT_FUNCTION (cnode->decl);
	        basic_block block;
	        FOR_EACH_BB_FN (block, function_decl)
		{
			value_type * in_value = current_context->get_in_value (block);
			value_type * out_value = current_context->get_out_value (block);
			DEBUG ("\nBlock %d okay!", block->index);
		}
#endif

		DEBUG ("\nAre there any blocks?");
		basic_block current_block = current_context->get_block_from_worklist ();

#if DEBUG_CONTAINER
		if (!current_block)
			RESULT ("\nError: get_context_from_worklist () ensures that the block worklist is not empty");
	        DEBUG ("\nFunction %s, block %d retrieved from block-worklist", function_name, current_block->index);
		if (!current_block->aux)
			RESULT ("\nError: aux field of block %d has not been initialized", current_block->index);
		DEBUG ("\nAnalyzing block %d", current_block->index);
#endif

		bool is_value_same = analyze_block (current_context, current_block);
		// FIXME
		// If the current block is still in the BLOCK_WORKLIST, it
		// means that the current block is a function call and the
		// called context still needs to be processed; therefore, the
		// current block has been added for reprocessing. In this
		// case, we do not add the adjacent blocks right now.
		// if (!is_processed (current_block))
		if (!is_value_same)
			add_adjacent_blocks_to_worklist (current_context, current_block);
			// FIXME: If we implement interleaved forward and
			// backward interprocedural analysis, it might be time
			// saving to not start the worklist from scratch in
			// every round, but use the previous round's worklist.
			// So when we perform forward analysis and IN of a
			// block changes, we should add this block to the
			// worklist of backward analysis. Similarly, when we
			// perform backward analysis and OUT of a block
			// changes, we should add this block to the worklist of
			// forward analysis.
		else
		{
			DEBUG ("\nValue at out of block is same as previous iteration");
			DEBUG ("\nTherefore, adjacent block is not added to worklist");
		}

#if DEBUG_CONTAINER
		DEBUG ("\nPrinting current worklist before picking the next context from the worklist");
		print_context_worklist ();
#endif
	}

	RETURN_VOID ();
}

/** Returns the function targets of a call_site under a given context.
 *  Context is needed for on-the-fly call graph construction.
 */

template <class value_type, class dept_value_type>
set<struct cgraph_node *> inter_procedural_analysis<value_type, dept_value_type>::
get_called_functions (context<value_type, dept_value_type> & src_context, basic_block call_site)
{
	if (!is_value_context)
	{
		set<struct cgraph_node *> empty_called_functions;
		return empty_called_functions;
	}

	// Returns the called function's decl tree. If it is a direct function 
	// call, the TREE_CODE of the returned decl will be FUNCTION_DECL. If 
	// it is a call via function pointer, it will be VAR_DECL. 

	// FIXME: Check if function call is the only statement of the block;
	// there are not assignment statements created by gcc for parameter
	// passing.
	DEBUG ("\ngsi_start_bb");
	gimple_stmt_iterator gsi = gsi_start_bb (call_site);
	gimple statement = gsi_stmt (gsi);
#if DEBUG_CONTAINER
	DEBUG ("\ngsi_stmt");
	print_gimple_stmt (dump_file, statement, 0, 0);
#endif

	// If we can resolve it here, its a simple function call. 
	tree decl = gimple_call_fndecl (statement);

	// The call is through function pointer. 
	if (!decl)
	{
		if (!(decl = gimple_call_fn (statement)))
		{
			RESULT ("\nError: Could not fetch decl of function pointer from statement");
			set<struct cgraph_node *> empty_set;
			return empty_set;
		}
#if DEBUG_CONTAINER
		DEBUG ("\nFunction pointer:\n");
		print_node (dump_file, "", decl, 0);
		DEBUG ("\n");
		print_node_brief (dump_file, "", decl, 0);
#endif

#if FUNCTION_POINTER
		// Find pointees of the function pointer from the data flow
		// value
		return get_called_functions (src_context, call_site, decl);

#else
		set<struct cgraph_node *> empty_set;
		return empty_set;
#endif
	}

	if (!decl)
		DEBUG ("\nFunction pointer not yet resolved");

	struct cgraph_node * dest_function = cgraph_get_node (decl);

#if DEBUG_CONTAINER
	DEBUG ("\nFunction tree:");
	print_node_brief (dump_file, "", decl, 0);
	const char * dest_function_name = IDENTIFIER_POINTER (DECL_NAME (decl));
	DEBUG ("\nFunction %s", dest_function_name);
#endif

	set<struct cgraph_node *> dest_functions;
	dest_functions.insert (dest_function);
	return dest_functions;
}

template <class value_type, class dept_value_type>
basic_block inter_procedural_analysis<value_type, dept_value_type>::
get_block_of_function (struct cgraph_node * cnode, block_index bid)
{
	struct function * fn = DECL_STRUCT_FUNCTION (cnode->decl);
	basic_block bb = BASIC_BLOCK_FOR_FUNCTION (fn, bid);
	if (bb->index != bid)
		RESULT ("\nError: get_block_of_function () returns wrong basic block");
	DEBUG ("\nget_block_of_function: bb = %d = %d", bid, bb->index);
	return bb;
}

template <class value_type, class dept_value_type>
context<value_type, dept_value_type> * inter_procedural_analysis<value_type, dept_value_type>::
get_context (context_index cid)
{
	#if CHECK_CONTAINER
	if (program_contexts.find (cid) == program_contexts.end ())
	{
		RESULT ("\nError: Context is not saved in map of program contexts");
		return NULL;
	}
	#endif
	return program_contexts[cid];
}

template <class value_type, class dept_value_type>
bool inter_procedural_analysis<value_type, dept_value_type>::
is_recursively_called (struct cgraph_node * function, 
	context<value_type, dept_value_type> & current_context, 
	set<context_index> & visited_contexts)
{
#if UNSOUND_RETURN
	return false;
#endif

	if (current_context.get_function () == function)
	{
		DEBUG ("\nContext %d is of the same function", current_context.get_context_id ());
		return true;
	}

	context_index context_id = current_context.get_context_id ();
	if (visited_contexts.find (context_id) != visited_contexts.end ())
		return false;
	visited_contexts.insert (context_id);

	set<pair<context_index, block_index> >::iterator ci;
	set<pair<context_index, block_index> > source_contexts = current_context.get_source_contexts ();
	for (ci = source_contexts.begin (); ci != source_contexts.end (); ci++)
	{
		context_index src_index = ci->first;
		context<value_type, dept_value_type> * src = get_context (src_index);
		if (is_recursively_called (function, *src, visited_contexts))
			return true;
	}

	return false;
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
set_blocks_order ()
{
	int NUM_START_END_BLOCKS = 2;
	for (struct cgraph_node * cnode = cgraph_nodes; cnode; cnode = cnode->next)
	{
		// Nodes without a body, and clone nodes are not interesting. 
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;
		set_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

#if DEBUG_CONTAINER
		const char * dest_function_name = IDENTIFIER_POINTER (DECL_NAME (cnode->decl));
		DEBUG ("\nFunction %s", dest_function_name);
#endif

		int number_of_blocks = n_basic_blocks - NUM_FIXED_BLOCKS + NUM_START_END_BLOCKS;
		DEBUG ("\nnumber_of_blocks=%d", number_of_blocks);
		DEBUG ("\nrev_post_order: ");
		// rev_post_order is a map from order-id to block-id
		int * rev_post_order = XNEWVEC (int, number_of_blocks);
		pre_and_rev_post_order_compute (NULL, rev_post_order, false);

#if DEBUG_CONTAINER
		DEBUG ("\nOriginal rev-post-order: ");
		for (int i = 0; i < number_of_blocks - NUM_START_END_BLOCKS; i++)
			DEBUG ("(bb=%d,order=%d), ", rev_post_order[i], i);
#endif

		// Assign START_BLOCK the lowest order-id which is higher than order-id of call blocks
		int bb = cfun->cfg->x_entry_block_ptr->index;
		// Shift all blocks in REV_POST_ORDER to one higher order-id
		for (int j = number_of_blocks - 1; j > 0; j--)
			rev_post_order[j] = rev_post_order[j - 1];
		rev_post_order[0] = bb;
		DEBUG ("\nstart block %d gets order id %d", bb, 0);
		
		// Assign END_BLOCK order-id = number_of_blocks-1
		bb = cfun->cfg->x_exit_block_ptr->index;
		rev_post_order[number_of_blocks - 1] = bb;
		DEBUG ("\nend block %d gets order id %d", bb, number_of_blocks - 1);

		DEBUG ("\nUpdated rev-post-order: ");	
		for (int i = 0; i < number_of_blocks; i++)
		{
			basic_block block = BASIC_BLOCK (rev_post_order[i]);
			set_block_order (block, i);
		}

		free (rev_post_order);
	}
}

template <class value_type, class dept_value_type>
map<context_index, int> inter_procedural_analysis<value_type, dept_value_type>::
get_call_chain_lengths (int inf)
{
	map<context_index, int> call_chain_len;

	set<context<value_type, dept_value_type> *> contexts;
	typename context_enums<value_type, dept_value_type>::iterator ci;
	for (ci = program_contexts.begin (); ci != program_contexts.end (); ci++)
		contexts.insert (ci->second);

	get_call_chain_lengths (contexts, call_chain_len, inf);
	return call_chain_len;
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
get_call_chain_lengths (set<context<value_type, dept_value_type> *> & contexts,
	map<context_index, int> & call_chain_len,
	int inf)
{
	set<context<value_type, dept_value_type> *> succ_contexts;

	typename set<context<value_type, dept_value_type> *>::iterator ci;
	for (ci = contexts.begin (); ci != contexts.end (); ci++)
	{
		context<value_type, dept_value_type> * c = *ci;
		context_index cid = c->get_context_id ();
		int max_len = c->get_max_call_chain_len (call_chain_len, inf);
		if (call_chain_len[cid] < max_len)
		{
			call_chain_len[cid] = max_len;
			c->get_destination_contexts (succ_contexts);
		}
	}

	if (succ_contexts.size ())
		get_call_chain_lengths (succ_contexts, call_chain_len, inf);
}

/**
 * Check that there should be only one context per function.
 */

template <class value_type, class dept_value_type>
bool inter_procedural_analysis<value_type, dept_value_type>::
is_one_context_per_function ()
{
#if DEBUG_CONTAINER
	print_program_contexts ();
#endif

        typename map<function_index, context_enums<value_type, dept_value_type> >::iterator fci;
	for (fci = function_contexts_map.begin (); fci != function_contexts_map.end (); fci++)
	{
		function_index fid = fci->first;
		context_enums<value_type, dept_value_type> ce = fci->second;
		if (ce.size () > 1)
		{
			RESULT ("\nError: Function %d has %d number of contexts", fid, ce.size ());
			return false;
		}
	}
	return true;
}

/**
 * This is analysis specific function. Should not be defined here.
 */

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
copy_context_value (void * src_con, void * dest_con)
{
	RESULT ("\nError: copy_context_value has not been overridden");
}

template <class value_type, class dept_value_type>
bool inter_procedural_analysis<value_type, dept_value_type>::
caller_to_callee_info (context<value_type, dept_value_type> & con)
{
	RESULT ("\nError: caller_to_callee_info has not been overridden");
}

template <class value_type, class dept_value_type>
bool inter_procedural_analysis<value_type, dept_value_type>::
callee_to_caller_info (context<value_type, dept_value_type> & con)
{
	RESULT ("\nError: callee_to_caller_info has not been overridden");
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
store_context_info (context<value_type, dept_value_type> & con)
{
	RESULT ("\nError: store_context_info has not been overridden");
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
free_context_values ()
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif

	typename map<unsigned int, context_enums<value_type, dept_value_type> >::iterator ci;
	for (ci = function_contexts_map.begin (); ci != function_contexts_map.end (); ci++)
	{
		context_enums<value_type, dept_value_type> ce = ci->second;
		typename context_enums<value_type, dept_value_type>::iterator vi;
		for (vi = ce.begin (); vi != ce.end (); vi++)
		{
			context<value_type, dept_value_type> * c = vi->second;
			free_context_values (*c);
		}
	}
}

/**
 * Free all block values of curr_context if no context is reachable from it
 */

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
free_context_analysis_values (context<value_type, dept_value_type> & curr_context)
{

}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
free_context_values (context<value_type, dept_value_type> & curr_context)
{
        DEBUG ("\nFREE");

        set<context_index> reachable_contexts;
        if (is_reachable_context_unprocessed (curr_context, reachable_contexts))
                return;

        DEBUG ("\nNULLing context %d", curr_context.get_context_id ());
        struct cgraph_node * cnode = curr_context.get_function ();
        struct function * function_decl = DECL_STRUCT_FUNCTION (cnode->decl);
        basic_block block;
	bool is_first_block = true;
        FOR_EACH_BB_FN (block, function_decl)
        {
                unsigned int block_type = ((block_information *)(block->aux))->get_block_type ();
                if (!(block_type & END_BLOCK) && !(block_type & START_BLOCK))
                {
			if (!is_first_block)
	                        curr_context.set_in_value (block, NULL);
                        curr_context.set_out_value (block, NULL);
			DEBUG ("\nIN OUT of block=%d set to NULL", block->index);
			is_first_block = false;
                }
        }
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
delete_aux_info (void * aux_info)
{
	RESULT ("\nError: delete_aux_info has not been overridden");
	// Since this class does not know the type of AUX_INFO, delete cannot
	// be done here. Classes that want to delete AUX_INFO can override this
	// function.
	aux_info = NULL;
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
print_aux_info (void * aux_info)
{
	RESULT ("\nError: print_aux_info has not been overridden");
}

/** 
 * Merge all value contexts of each function. This is MOVP. Till now, this is
 * used by dfa/allocation_site_based_analysis only.
 */

template <class value_type, class dept_value_type>
template <class dest_value_type, class dest_dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
meet_over_valid_paths (inter_procedural_analysis<dest_value_type, dest_dept_value_type> & dest_analysis)
{
	DEBUG ("\nmeet_over_valid_paths()");

#if DEBUG_CONTAINER
	print_program_contexts ();
#endif
        map<function_index, context<dest_value_type, dest_dept_value_type> *> unique_function_contexts;
	create_unique_function_contexts (unique_function_contexts);

	unsigned int func_contexts_count = 0;

        typename map<function_index, context_enums<value_type, dept_value_type> >::iterator fci;
	for (fci = function_contexts_map.begin (); fci != function_contexts_map.end (); fci++)
	{
		function_index fid = fci->first;
		context_enums<value_type, dept_value_type> ce = fci->second;
		func_contexts_count += ce.size ();

		typename context_enums<value_type, dept_value_type>::iterator vi;
		// Copy every context to the unique context of the function
		for (vi = ce.begin (); vi != ce.end (); vi++)
		{
			context<value_type, dept_value_type> * fc = vi->second;
			DEBUG ("\nCopy context=%d to unique context", fc->get_context_id ());
			fc->copy_context (program_contexts, unique_function_contexts);

			struct cgraph_node * func = fc->get_function ();
			function_index fid = func->uid;
			context<dest_value_type, dest_dept_value_type> * uc = 
				unique_function_contexts[fid];
			copy_context_value (fc, uc);
		}
	}

#if STATISTICS_CONTAINER
	STATS ("\nTotal value contexts=%d", func_contexts_count);
	FILE * stat_file = fopen (STAT_FILE, "a");
	fprintf (stat_file, "\nTotal value contexts=%d", func_contexts_count);
	fclose (stat_file);
#endif

#if DEBUG_CONTAINER
	DEBUG ("\nOriginal pta contexts=");
	print_program_contexts ();
#endif

	// Delete all contexts except first of every function
	dest_analysis.save_unique_function_contexts (unique_function_contexts);

#if DEBUG_CONTAINER
	DEBUG ("\nUnique contexts=");
	dest_analysis.print_program_contexts ();
#endif
}

template <>
template <class dest_value_type, class dest_dept_value_type>
void inter_procedural_analysis<variables, unlabeled_edges>::
get_dept_context (context<variables, unlabeled_edges> * src_context,
	context<dest_dept_value_type, dest_value_type> ** dept_context)
{
	dept_context = NULL;
}

template <>
template <class dest_value_type, class dest_dept_value_type>
void inter_procedural_analysis<unlabeled_edges, variables>::
get_dept_context (context<unlabeled_edges, variables> * src_context,
	context<dest_dept_value_type, dest_value_type> ** dept_context)
{
	dept_context = NULL;
}

template <>
template <class dest_value_type, class dest_dept_value_type>
void inter_procedural_analysis<deterministic_graph, unlabeled_edges>::
get_dept_context (context<deterministic_graph, unlabeled_edges> * src_context,
	context<dest_dept_value_type, dest_value_type> ** dept_context)
{
	*dept_context = src_context->get_dependent_context ();
}

template <>
template <class dest_value_type, class dest_dept_value_type>
void inter_procedural_analysis<non_deterministic_graph, unlabeled_edges>::
get_dept_context (context<non_deterministic_graph, unlabeled_edges> * src_context,
	context<dest_dept_value_type, dest_value_type> ** dept_context)
{
	*dept_context = src_context->get_dependent_context ();
}

template <class value_type, class dept_value_type>
template <class dest_value_type, class dest_dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
create_unique_function_contexts (map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts)
{
	DEBUG ("\ncreate_unique_function_contexts ()");
        typename map<function_index, context_enums<value_type, dept_value_type> >::iterator fci;
	for (fci = function_contexts_map.begin (); fci != function_contexts_map.end (); fci++)
	{
		function_index fid = fci->first;
		context_enums<value_type, dept_value_type> ce = fci->second;
		typename context_enums<value_type, dept_value_type>::iterator vi;
		vi = ce.begin ();
		if (vi == ce.end ())
			continue;
		context<value_type, dept_value_type> * first_fc = vi->second;

		struct cgraph_node * cnode = first_fc->get_function ();
		basic_block start_block = first_fc->get_start_block ();
		basic_block end_block = first_fc->get_end_block ();

		context<dest_dept_value_type, dest_value_type> * dept_context = NULL;
		get_dept_context (first_fc, &dept_context);

		context<dest_value_type, dest_dept_value_type> * unique_context = 
			new context<dest_value_type, dest_dept_value_type> 
				(cnode, start_block, end_block, NULL, NULL, dept_context);

		context_index unique_cid = unique_context->get_context_id ();
		unique_function_contexts[fid] = unique_context;
	}
}

template <class value_type, class dept_value_type>
template <class dest_value_type, class dest_dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
save_unique_function_contexts (map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts)
{
	// aux_info is dependent on client analysis and it is deleted when
	// analysis goes out of scope.
	// delete_context_aux_info ();
	delete_contexts ();
	program_contexts.clear ();
	function_contexts_map.clear ();

        typename map<function_index, context<dest_value_type, dest_dept_value_type> *>::iterator ufci;
	for (ufci = unique_function_contexts.begin (); ufci != unique_function_contexts.end (); ufci++)
	{
		function_index fid = ufci->first;
		context<dest_value_type, dest_dept_value_type> * uc = ufci->second;
		context_index ucid = uc->get_context_id ();

		set_function_contexts_map (fid, ucid, *uc);
		set_program_context (ucid, *uc);
	}
}

/**
 * context info of allocation_site_based_analysis<dept_value_type> represents
 * bypassed points-to graph due to this call only. context info of
 * allocation_site_based_analysis <dest_dept_value_type> (that is computed in
 * this function) represents bypassed points-to graph of all the previous
 * calls.
 */

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
accumulate_contexts (bool caller_to_callee)
{
	FUNBEGIN ();

	DEBUG ("\nanalyze_contexts (caller_to_callee=%d)", caller_to_callee);

	if (context_worklist.size ())
	{
		RESULT ("\nError: context worklist should have been empty");
	}
	
	// Add all contexts to worklist
	typename context_enums<value_type, dept_value_type>::iterator ci;
	for (ci = program_contexts.begin (); ci != program_contexts.end (); ci++)
	{
		context<value_type, dept_value_type> * uc = ci->second;
		DEBUG ("\nadd context=%d", uc->get_context_id ());
		add_context_to_worklist (uc);
	}

	// Process worklist
	context<value_type, dept_value_type> * current_context;
	while (current_context = get_context_from_info_worklist ())
	{
		DEBUG ("\nanalyze context=%d", current_context->get_context_id ());
		bool is_info_same = true;
		if (caller_to_callee)
			is_info_same = caller_to_callee_info (*current_context); 
		else
			is_info_same = callee_to_caller_info (*current_context); 
		if (!is_info_same)
			add_dest_contexts_to_worklist (*current_context);
		else
		{
			DEBUG ("\ncontext info same as previous iteration");
			DEBUG ("\nTherefore, dest contexts are not added to worklist");
		}

#if DEBUG_CONTAINER
		DEBUG ("\nPrinting info worklist before picking the next context from the worklist");
		print_context_worklist ();
#endif
	}

	RETURN_VOID ();
}

template <class value_type, class dept_value_type>
context<value_type, dept_value_type> * inter_procedural_analysis<value_type, dept_value_type>::
get_context_from_info_worklist ()
{
	DEBUG ("\nget_context_from_info_worklist ()");

	if (context_worklist.empty ())
		return NULL;

	context<value_type, dept_value_type> * curr_context = context_worklist.top();
	// Remove the context from the worklist
	context_worklist.pop ();

	if (!curr_context)
	{
		RESULT ("\nError: CONTEXT_WORKLIST is empty");
		return NULL;
	}

	return curr_context;
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
add_dest_contexts_to_worklist (context<value_type, dept_value_type> & curr_context)
{
	// Get the destination/called contexts
	map<pair<block_index, function_index>, context<value_type, dept_value_type> *> destination_contexts = 
		curr_context.get_destination_contexts ();
	typename map<pair<block_index, function_index>, context<value_type, dept_value_type> *>::iterator di;
	for (di = destination_contexts.begin (); di != destination_contexts.end (); di++)
	{
		context<value_type, dept_value_type> * dc = di->second;
		add_context_to_worklist (dc);
	}
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
store_contexts_info ()
{
#if DEBUG_CONTAINER
	print_program_contexts ();
#endif

	// Iterate over movp contexts of dfa/allocation_site_based_analysis
        typename map<function_index, context_enums<value_type, dept_value_type> >::iterator fci;
	for (fci = function_contexts_map.begin (); fci != function_contexts_map.end (); fci++)
	{
		function_index fid = fci->first;
		context_enums<value_type, dept_value_type> ce = fci->second;
		typename context_enums<value_type, dept_value_type>::iterator vi;
		for (vi = ce.begin (); vi != ce.end (); vi++)
		{
			context<value_type, dept_value_type> * con = vi->second;
			DEBUG ("\ncontext=%d", con->get_context_id ());
			store_context_info (*con);
		}
	}
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
find_recursive_functions (set<function_index> & recursive_fns)
{
#if DEBUG_CONTAINER
	print_program_contexts ();
#endif

	function_index main_fid = program.main_cnode->uid;
	if (function_contexts_map.find (main_fid) == function_contexts_map.end ())
	{
		RESULT ("\nError: main function not found in contexts_map");
		return;
	}
	context_enums<value_type, dept_value_type> main_contexts = 
		function_contexts_map[main_fid];
	if (!main_contexts.size ())
	{
		RESULT ("\nError: main context not found");
		return;
	}
	context<value_type, dept_value_type> * main_context = main_contexts.begin ()->second;

	map<context_index, set<context_index> > callers;
	main_context->find_recursive_functions (callers, recursive_fns);

#if DEBUG_CONTAINER
	map<context_index, set<context_index> >::iterator mc;
	DEBUG ("\ncontext callers=");
	for (mc = callers.begin (); mc != callers.end (); mc++)
	{
		context_index cid = mc->first;
		DEBUG ("\ncallers of context=%d=", cid);
		set<context_index> caller_cids = mc->second;
		set<context_index>::iterator ci;
		for (ci = caller_cids.begin (); ci != caller_cids.end (); ci++)
			DEBUG ("%d,", *ci);
	}
#endif
#if INFO_CONTAINER
	set<function_index>::iterator fi;
	RESULT ("\nRecursive fns=");
	for (fi = recursive_fns.begin (); fi != recursive_fns.end (); fi++)
	{
		struct cgraph_node * function = program.get_cgraph_node (*fi);
		const char * function_name = cgraph_node_name (function);
		RESULT ("%s(%d),", function_name, *fi);
	}
#endif
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
print_program_contexts ()
{
	typename map<function_index, context_enums<value_type, dept_value_type> >::iterator fi;
	for (fi = function_contexts_map.begin (); fi != function_contexts_map.end (); fi++)
	{
		// Get function index
		function_index index = fi->first;
		struct cgraph_node * function = program.get_cgraph_node (index);
		const char * function_name = cgraph_node_name (function);
		DEBUG ("\nFunction %s(%d)", function_name, index);

		// Get all contexts of the function
		context_enums<value_type, dept_value_type> ce = fi->second;

		typename context_enums<value_type, dept_value_type>::iterator vi;
		for (vi = ce.begin (); vi != ce.end (); vi++)
		{
			// Get a context of the function
			context<value_type, dept_value_type> * function_context = vi->second;
			DEBUG ("\nContext %d", vi->first);
			#if DEBUG_CONTAINER
			function_context->print_context ();
			print_aux_info (function_context->get_aux_info ());
			#endif

			// Get the dependent context of the function context
			context<dept_value_type, value_type> * dependent_context = 
				function_context->get_dependent_context ();
			if (dependent_context)
			{
				DEBUG (", dependent context %d", dependent_context->get_context_id ());
			}
			else
			{
				DEBUG (", dependent context NULL");
			}

			// Get the source/calling contexts
			set<pair<context_index, block_index> > source_contexts;
			source_contexts = function_context->get_source_contexts ();
			typename set<pair<context_index, block_index> >::iterator si;
			for (si = source_contexts.begin (); si != source_contexts.end (); si++)
			{
				context<value_type, dept_value_type> * c = get_context (si->first);
				block_index b = si->second;
				DEBUG (", source (context %d, src-function %d, block %d)", si->first, c->get_function ()->uid, b);
			} 

			// Get the destination/called contexts
			map<pair<block_index, function_index>, context<value_type, dept_value_type> *> destination_contexts = 
				function_context->get_destination_contexts ();
			typename map<pair<block_index, function_index>, context<value_type, dept_value_type> *>::iterator di;
			for (di = destination_contexts.begin (); di != destination_contexts.end (); di++)
			{
				pair<block_index, function_index> p = di->first;
				context<value_type, dept_value_type> * c = di->second;
				DEBUG (", destination (context %d, dest-function %d, block %d)", 
					c->get_context_id (), p.second, p.first);
			} 
		}
	}
	DEBUG ("\nprint_program_contexts done");
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
print_context_worklist ()
{
	DEBUG ("\nWorklist of contexts:");
	//typename set<context<value_type, dept_value_type> *>::iterator it;
	stack<context<value_type, dept_value_type> *> temp;
	//for (it = context_worklist.begin (); it != context_worklist.end (); it++)
	for (temp = context_worklist; !temp.empty (); temp.pop ())
	{
		context<value_type, dept_value_type> * c = temp.top ();
		if (!c)
			RESULT ("\nError: Context NULL is saved on worklist");
		struct cgraph_node * cnode = c->get_function();
		const char * function_name = cgraph_node_name (cnode);
		DEBUG ("%d(%s),", c->get_context_id (), function_name);
	}

	for (temp = context_worklist; !temp.empty (); temp.pop ())
	{
		context<value_type, dept_value_type> * c = temp.top ();
		if (!c)
			RESULT ("\nError: Context NULL is saved on worklist");
		struct cgraph_node * cnode = c->get_function();
		const char * function_name = cgraph_node_name (cnode);
		DEBUG ("\nContext %d at function %s", c->get_context_id (), function_name);
		DEBUG (", source contexts:");
		set<pair<context_index, block_index> > src_contexts = c->get_source_contexts ();
		set<pair<context_index, block_index> >::iterator si;
		for (si = src_contexts.begin (); si != src_contexts.end (); si++)
		{
			pair<context_index, block_index> p = *si;	
			DEBUG ("%d,", p.first);
		}
		c->print_context ();
	}
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
print_bypassing_analysis_statistics (map<function_index, context_enums<value_type, dept_value_type> > & function_contexts_map)
{
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
print_bypassing_statistics ()
{
	print_bypassing_analysis_statistics (function_contexts_map);
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
print_statistics ()
{
	print_analysis_statistics (function_contexts_map);
//	print_bypassing_statistics ();
}

template <class value_type, class dept_value_type>
void inter_procedural_analysis<value_type, dept_value_type>::
print_functions_blocks ()
{
	DEBUG ("print_functions_blocks()");
	set<unsigned int > fuids;
	for (struct cgraph_node * cnode = cgraph_nodes; cnode; cnode = cnode->next)
	{
		// Nodes without a body, and clone nodes are not interesting. 
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;
		set_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

#if DEBUG_CONTAINER
		const char * dest_function_name = IDENTIFIER_POINTER (DECL_NAME (cnode->decl));
		DEBUG ("\nFunction %s", dest_function_name);
#endif
		fuids.insert (cnode->uid);
	}

	set<unsigned int>::iterator fi;
	for (fi = fuids.begin (); fi != fuids.end (); fi++)
	{
		struct cgraph_node * function = program.get_cgraph_node (*fi);
		const char * function_name = cgraph_node_name (function);
		DEBUG ("\nFunction %s(%d)", function_name, *fi);
		struct function * function_decl = DECL_STRUCT_FUNCTION (function->decl);

		basic_block block;
		FOR_EACH_BB_FN (block, function_decl)
		{
			DEBUG ("\n\tblock=%d", block->index);
		}
	}
}

//template class inter_procedural_analysis<access_paths, non_deterministic_basic_graph>; 
//template class inter_procedural_analysis<variables, non_deterministic_simple_graph>; 
//template class inter_procedural_analysis<non_deterministic_graph, deterministic_graph>; 
//template class inter_procedural_analysis<non_deterministic_basic_graph, access_paths>; 
//template class inter_procedural_analysis<non_deterministic_simple_graph, variables>; 
template class inter_procedural_analysis<pt_node_set, variables>; 
template class inter_procedural_analysis<unlabeled_edges, variables>; 
template class inter_procedural_analysis<variables, pt_node_set>; 
template class inter_procedural_analysis<variables, unlabeled_edges>; 
template class inter_procedural_analysis<deterministic_graph, unlabeled_edges>; 
template class inter_procedural_analysis<non_deterministic_graph, unlabeled_edges>; 
template class inter_procedural_analysis<unlabeled_edges, deterministic_graph>; 
template class inter_procedural_analysis<unlabeled_edges, non_deterministic_graph>; 

template void inter_procedural_analysis<unlabeled_edges, variables>::
meet_over_valid_paths (inter_procedural_analysis<unlabeled_edges, deterministic_graph> & );
template void inter_procedural_analysis<deterministic_graph, unlabeled_edges>::
meet_over_valid_paths (inter_procedural_analysis<deterministic_graph, unlabeled_edges> & );
template void inter_procedural_analysis<unlabeled_edges, variables>::
meet_over_valid_paths (inter_procedural_analysis<unlabeled_edges, non_deterministic_graph> & );
template void inter_procedural_analysis<non_deterministic_graph, unlabeled_edges>::
meet_over_valid_paths (inter_procedural_analysis<non_deterministic_graph, unlabeled_edges> & );

template void inter_procedural_analysis<unlabeled_edges, variables>::
create_unique_function_contexts (map<function_index, context<unlabeled_edges, deterministic_graph> *> & unique_function_contexts);
template void inter_procedural_analysis<unlabeled_edges, variables>::
create_unique_function_contexts (map<function_index, context<unlabeled_edges, non_deterministic_graph> *> & unique_function_contexts);

template void inter_procedural_analysis<unlabeled_edges, deterministic_graph>::
save_unique_function_contexts (map<function_index, context<unlabeled_edges, deterministic_graph> *> & unique_function_contexts);
template void inter_procedural_analysis<unlabeled_edges, non_deterministic_graph>::
save_unique_function_contexts (map<function_index, context<unlabeled_edges, non_deterministic_graph> *> & unique_function_contexts);



/************************
 * @author Vini Kanvar
************************/

#include "variables.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

variables::
variables ()
{
	reference_count = 0;
	DEBUG ("\nvariables()");
	NEW_ADDR ("\nnew variables %x", this);
	important_block = false;
}

variables::
~variables ()
{
	DEBUG ("\n~variables(): %u", this);
	DEBUG ("\nGC of live variables");
	GC_ADDR ("\ngc variables %x", this);

	callees_global_defs.clear ();
	callees_global_uses.clear ();
	function_param_defs.clear ();
	live_vars.clear ();
}

void variables::
increment_reference_count ()
{
	reference_count++;
	DEBUG ("\nCount = %d (after incr) of variable set", reference_count);
}

void variables::
decrement_reference_count ()
{
	if (!reference_count)
	{
		RESULT ("\nError: reference count of variable set %x was already 0", this);
		return;
	}
	
	reference_count--;
	DEBUG ("\nCount = %d (after decr) of variable set", reference_count);
	if (!reference_count)
	{
#if GC
		DEBUG ("\nGC variables");
		delete this;
#endif
	}
}

set<variable_id> variables::
get_live_vars ()
{
	return live_vars;
}

set<variable_id> variables::
get_function_param_defs ()
{
	return function_param_defs;
}

set<variable_id> variables::
get_callees_global_defs ()
{
	return callees_global_defs;
}

set<variable_id> variables::
get_callees_global_uses ()
{
	return callees_global_uses;
}

void variables::
clean ()
{
	// No cleaning required for VARIABLES. This function is needed in
	// other data structures based on graphs (like
	// NON_DETERMINISTIC_BASIC_GRAPH).
}

bool variables::
is_empty ()
{
	if (callees_global_defs.size ())
		return false;
	if (callees_global_uses.size ())
		return false;
	if (function_param_defs.size ())
		return false;
	if (live_vars.size ())
		return false;
}

/**
 * Note that for computation of liveness summary, LIVE_VARS contains
 * only local variables and temporary variables. We assume that function
 * parameters, globals, and heaps are live at all program points.
 * 
 * Return true if v is in LIVE_VARS or v is a function parameter or
 * global.
 */

bool variables::
is_element (variable_id v)
{
	// If v is in LIVE_VARS
	if (live_vars.find (v) != live_vars.end ())
	{
#if DEBUG_CONTAINER
		csvarinfo_t vinfo = program.cs_get_varinfo (v);
		DEBUG ("\n%s(%d) is in live_vars", vinfo->name, v);
#endif
		return true;
	}

	csvarinfo_t v_info = program.cs_get_varinfo (v);

	// If v is a global variable or 
	if (v_info->is_global_var)
	{
		DEBUG ("\n%s(%d) is a global variable", v_info->name, v);
		return true;
	}

	// If v is a function parameter
	if (v_info->decl && TREE_CODE (v_info->decl) == PARM_DECL)
	{
		DEBUG ("\n%s(%d) is a function parameter", v_info->name, v);
		return true;
	}

	return false;
}

/**
 * Note that for computation of liveness summary, LIVE_VARS contains
 * only local variables and temporary variables. We assume that function
 * parameters, globals, and heaps are live at all program points.
 * 
 * (1) Using points-to information: Return true if v is a function parameter,
 * or z.offset is an element of LIVE_VARS or globals or heap, where z is
 * a pointee of v.
 * (2) Using type information: Return true if v is a function parameter, or
 * z.offset is an element of local variables in LIVE_VARS or globals or
 * heap, where the type of z matches with the type of *v. (Note that &D.xxxx
 * never appears in any statement; therefore, a temporary can never be a
 * pointee of any variable.)
 * (3) Using no information: Return true since v might be pointing to a global
 * or heap.
 */

bool variables::
is_element (variable_id v, label offset)
{
	DEBUG ("\nis_element(v=%d,offset=%d)", v, offset);

	// Using (3)
	return true;
}

void variables::
insert_addr_taken_globals ()
{
	insert_live_vars (program.addr_taken_globals);
}

void variables::
insert_addr_taken_locals (struct cgraph_node * cnode)
{
	if (program.addr_taken_locals.find (cnode) == program.addr_taken_locals.end ())
		return;

	insert_live_vars (program.addr_taken_locals[cnode]);
}

void variables::
insert_addr_taken_params (struct cgraph_node * cnode)
{
	if (program.addr_taken_params.find (cnode) == program.addr_taken_params.end ())
		return;

	insert_live_vars (program.addr_taken_params[cnode]);
}

void variables::
insert_live_var (variable_id v)
{
	live_vars.insert (v);
}

void variables::
insert_selective_live_var (variable_id v)
{
	// Do not insert variables with id <= 2
	if (!program.is_proper_var (v))
		return;

	csvarinfo_t variable = program.cs_get_varinfo (v);
	if (!variable)
		return;
	if (!variable->decl)
		return;

	// Check that variable is not heap 
	if (variable->is_heap_var)
		return;

	// Do not insert function parameters --- we assume they are live in
	// summary based analysis.
	// if (program.parm_decl (variable->id)
	if (TREE_CODE (variable->decl) == PARM_DECL)
		return;

	// Do not insert global variables --- we assume they are live.
	if (variable && variable->is_global_var)
		return;

	live_vars.insert (v);
	DEBUG ("\nInserted %d", v);
	DEBUG ("\nlive_vars.size() = %u", live_vars.size ());
}

void variables::
insert_selective_function_param_def (variable_id v)
{
	csvarinfo_t variable = program.cs_get_varinfo (v);
	if (program.param_var (variable))
	{
		function_param_defs.insert (v);
		DEBUG ("\nInserted %d", v);
		DEBUG ("\nfunction_param_defs.size() = %u", function_param_defs.size ());
		return;
	}
}

void variables::
insert_selective_callees_global_def (variable_id v)
{
	csvarinfo_t variable = program.cs_get_varinfo (v);
	if (variable && variable->decl && variable->is_global_var && !variable->is_heap_var)
	{
		callees_global_defs.insert (v);
		DEBUG ("\nInserted %d", v);
		DEBUG ("\ncallees_global_defs.size() = %u", callees_global_defs.size ());
		return;
	}
}

void variables::
insert_selective_callees_global_use (variable_id v)
{
	csvarinfo_t variable = program.cs_get_varinfo (v);
	if (variable && variable->decl && variable->is_global_var && !variable->is_heap_var)
	{
		callees_global_uses.insert (v);
		DEBUG ("\nInserted %d", v);
		DEBUG ("\ncallees_global_uses.size() = %u", callees_global_uses.size ());
		return;
	}
}

/**
 * (1) Using points-to information: Insert z.offset, where z is a pointee of v.
 * (2) Using type information: Insert z.offset, where the type of z (a local
 * non-temporary variable) is same as type of *v. (Note that &D.xxxx never
 * appears in any statement; therefore, a temporary can never be a pointee of
 * any variable.)
 * (3) Using no information: Insert all local (non-temporary) variables of this
 * function.
 */

void variables::
insert_addr_taken_locals (variable_id v, label offset, struct cgraph_node * cnode)
{
	if (!program.is_proper_var (v))
		return;

	// The below function does not include temporary variables. If V is a
	// temporary, we need to include that also.
	insert_selective_live_var (v);

	// For (1) and (2), 
	// use misc/parser::cs_first_vi_for_offset(...z,offset). This returns
	// z.offset.

	// Using (3)
	// Iterating over the variables of the entire program and finding local
	// (non-temporary) pointer variables of CURRENT_FUNCTION.
	// addr_taken locals do not include temporaries
	insert_addr_taken_locals (cnode);	
}

bool variables::
is_important_block ()
{
	return important_block;
}

void variables::
gen_important_block ()
{
	important_block = true;
}

void variables::
kill_important_block ()
{
	important_block = false;
}

void variables::
transfer_important_block (variables & dest_value)
{
	dest_value.important_block = important_block; 
}

/**
 * Used by IMPORTANT to check if lhs is live.
 */

bool variables::
is_live (label var)
{
//	if (live_vars.find (var) != live_vars.end ())
//		return true;
	if (callees_global_uses.find (var) != callees_global_uses.end ())
		return true;
	return false;
}

void variables::
insert_live_vars (set<variable_id> & vars)
{
	live_vars.insert (vars.begin (), vars.end ());
}

void variables::
insert_live_vars (variables & gen_vars)
{
	set<variable_id> sov = gen_vars.live_vars;
	live_vars.insert (sov.begin (), sov.end ());

#if DEBUG_CONTAINER
	DEBUG ("\ngen_live_vars: ");
	gen_vars.print_value (NULL);
	DEBUG ("\ninserted variables");
	print_value (NULL);
#endif
}

void variables::
delete_live_var (variable_id v)
{
	live_vars.erase (v);
}

void variables::
erase_function_param_defs ()
{
	function_param_defs.clear ();
}

void variables::
delete_callees_global_def (variable_id v)
{
	callees_global_defs.erase (v);
}

void variables::
delete_callees_global_use (variable_id v)
{
	callees_global_uses.erase (v);
}

void variables::
delete_live_vars (set<variable_id> & del_vars)
{
	set<variable_id>::iterator si;
	for (si = del_vars.begin (); si != del_vars.end (); si++)
		delete_live_var (*si);
}

void variables::
delete_live_vars (variables & del_vars)
{
	set<variable_id> sov = del_vars.live_vars;
	delete_live_vars (sov);
}

void variables::
clear_live_vars ()
{
	live_vars.clear ();
}

void variables:: 
extract_arg_ret_glob_reachable_live_vars (variables & arg_ret_glob_reachable_value,
	struct cgraph_node * called_function)
{
	set<variable_id>::iterator vi;
	for (vi = live_vars.begin (); vi != live_vars.end (); )
	{
		variable_id vid = *vi;
		csvarinfo_t var = VEC_index (csvarinfo_t, program.variable_data, vid);

		// Extract all globals as they may be needed in generating liveness of
		// other variables in callee.
		// Do not delete called function's variable e.g. return variable
		if (var->is_global_var
			|| var->scoping_function == called_function)
		// Do not extract address taken locals and params for greedy
		// liveness of root variables. Statements like x=... in callee
		// do not need caller's locals and statements like x->f=... do
		// not process lhs at all.
		//	 || var->is_addr_taken
		{
			live_vars.erase (vi++);
			arg_ret_glob_reachable_value.insert_live_var (vid);
		}
		else
			vi++;
	}
}

/**
 * This function returns the dead variables from LOCAL_VARIABLES. Here
 * LOCAL_VARIABLES does not contain parameters, globals, and heap.
 */

set<variable_id> variables::
get_dead_variables (set<variable_id> vars)
{
	set<variable_id>::iterator vi;
#if DEBUG_CONTAINER
	DEBUG ("\nLocal variables: ");
	for (vi = vars.begin (); vi != vars.end (); vi++)
		DEBUG ("%d, ", *vi);
	DEBUG ("\nLive variables: ");
	print_value (NULL);
#endif

	// Remove live and non-pointer variables from vars 
	for (vi = vars.begin (); vi != vars.end (); )
	{
		DEBUG ("\nCheck %d", *vi);

		csvarinfo_t variable = VEC_index (csvarinfo_t, program.variable_data, *vi);

		if (!variable)
			vars.erase (vi++);
		else if (!variable->decl)
			vars.erase (vi++);
		else if (!TREE_TYPE (variable->decl))
			vars.erase (vi++);
		else if (TREE_CODE (TREE_TYPE (variable->decl)) == FUNCTION_TYPE)
			vars.erase (vi++);
		else if (TREE_CODE (TREE_TYPE (variable->decl)) == METHOD_TYPE)
			vars.erase (vi++);

		// LIVE_VARS is the set of live variables
		else if (live_vars.find (*vi) != live_vars.end ())
		{
			DEBUG ("\n%d is live", *vi);
			vars.erase (vi++);
		}
		else
		{
			DEBUG ("\n%d is dead", *vi);
			vi++;
		}
	}
#if DEBUG_CONTAINER
	DEBUG ("\nDead local variables: ");
	for (vi = vars.begin (); vi != vars.end (); vi++)
		DEBUG ("%d, ", *vi);
#endif

	return vars;
}

variables * variables:: 
copy_value (bool is_loop_merge)
{
	variables * copy_variables = new variables;
	copy_variables->important_block = important_block;
	copy_variables->live_vars = live_vars;
	copy_variables->callees_global_defs = callees_global_defs;
	copy_variables->callees_global_uses = callees_global_uses;	
	copy_variables->function_param_defs = function_param_defs;
	return copy_variables;
}

void variables:: 
copy_value (variables & vars, bool is_loop_merge)
{
	important_block |= vars.important_block;
	live_vars.insert (vars.live_vars.begin (), vars.live_vars.end ());
	callees_global_defs.insert (vars.callees_global_defs.begin (), vars.callees_global_defs.end ());
	callees_global_uses.insert (vars.callees_global_uses.begin (), vars.callees_global_uses.end ());
	function_param_defs.insert (vars.function_param_defs.begin (), vars.function_param_defs.end ());
}

bool variables:: 
is_value_same (variables & vars)
{
#if DEBUG_CONTAINER
	DEBUG ("\nis_value_same ()");
	DEBUG ("\nValue1: ");
	print_value (NULL);
	DEBUG ("\nValue2: ");
	vars.print_value (NULL);
#endif

	if (this == &vars)
	{
		DEBUG ("\nValues are same");
		return true;
	}

	if (important_block != vars.important_block
		|| live_vars.size () != vars.live_vars.size ()
		|| callees_global_defs.size () != vars.callees_global_defs.size ()
		|| callees_global_uses.size () != vars.callees_global_uses.size ()
		|| function_param_defs.size () != vars.function_param_defs.size ()
		)
	{
		DEBUG ("\ncallees_global or callees_lhs_derefs are different");
		return false;
	}


	if (live_vars != vars.live_vars
		|| callees_global_defs != vars.callees_global_defs
		|| callees_global_uses != vars.callees_global_uses
		|| function_param_defs != vars.function_param_defs
		)
	{
		DEBUG ("\ncallees_global or callees_lhs_derefs are different");
		return false;
	}

	DEBUG ("\nValues are same");
	return true;
}

void variables:: 
print_value (const char * file)
{
	RESULT ("\n");
#if 0
#if DEBUG_CONTAINER
	for (int index = 0; index < VEC_length (csvarinfo_t, program.variable_data); index++)
	{
		csvarinfo_t variable = VEC_index (csvarinfo_t, program.variable_data, index);
		struct cgraph_node * cnode = variable->scoping_function;
		const char * function_name = NULL;
		if (cnode)
			function_name = cgraph_node_name (cnode);
		DEBUG ("\nVariable id %d, name %s, offset %llu, scoping function %s", 
			variable->id, variable->name, variable->offset, function_name);
	}
#endif
#endif

	DEBUG ("\nVariables (%x), ref_count=%d: ", this, reference_count);
	RESULT ("\nIMPORTANT=%d", important_block);
	set<variable_id>::iterator vi;
	RESULT ("\nlive_vars=");
	for (vi = live_vars.begin (); vi != live_vars.end (); vi++)
	{
		variable_id vid = *vi;
		DEBUG ("\nvid=%d", vid);
		csvarinfo_t variable = program.cs_get_varinfo (vid);
		if (!variable)
		{
			RESULT ("\nError: variable %d not found in variable_data", vid);
			continue;
			// return;
		}

		if (!variable->is_global_var)
		{
			struct cgraph_node * cnode = variable->scoping_function;
			// const char * function_name = cgraph_node_name (cnode);
			// RESULT ("%s.%s(%d), ", function_name, variable->name, vid);
			RESULT ("%s(%d), ", variable->name, vid);
		}
		else
			RESULT ("# %s(%d), ", variable->name, vid);
	}
	RESULT ("\ncallees_global_defs=");
	for (vi = callees_global_defs.begin (); vi != callees_global_defs.end (); vi++)
	{
		variable_id vid = *vi;
		DEBUG ("\nvid=%d", vid);
		csvarinfo_t variable = program.cs_get_varinfo (vid);
		if (!variable)
		{
			RESULT ("\nError: variable %d not found in variable_data", vid);
			continue;
			// return;
		}

		RESULT ("# %s(%d), ", variable->name, vid);
	}
	RESULT ("\ncallees_global_uses=");
	for (vi = callees_global_uses.begin (); vi != callees_global_uses.end (); vi++)
	{
		variable_id vid = *vi;
		DEBUG ("\nvid=%d", vid);
		csvarinfo_t variable = program.cs_get_varinfo (vid);
		if (!variable)
		{
			RESULT ("\nError: variable %d not found in variable_data", vid);
			continue;
			// return;
		}

		RESULT ("# %s(%d), ", variable->name, vid);
	}	
#if 0
	RESULT ("\nfunction_param_defs=");
	for (vi = function_param_defs.begin (); vi != function_param_defs.end (); vi++)
	{
		variable_id vid = *vi;
		DEBUG ("\nvid=%d", vid);
		csvarinfo_t variable = program.cs_get_varinfo (vid);
		if (!variable)
		{
			RESULT ("\nError: variable %d not found in variable_data", vid);
			continue;
			// return;
		}

		RESULT ("%s(%d), ", variable->name, vid);
	}
#endif
}



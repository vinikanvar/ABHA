
/************************
 * @author Vini Kanvar
************************/

#include "side_effects.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

side_effects::
side_effects ()
{
	is_unimp_blocks_ready = false;
}

void side_effects::
set_is_unimp_blocks_ready ()
{
	is_unimp_blocks_ready = true;
}

bool side_effects::
get_is_unimp_blocks_ready ()
{
	return is_unimp_blocks_ready;
}

set<variable_id> * side_effects::
get_callees_global_defs (struct cgraph_node * func)
{
	function_id fid = func->uid;
	if (callees_global_defs.find (fid) == callees_global_defs.end ())
	{
		RESULT ("\nError: callees_global_defs for func=%d is NULL", fid);
		return NULL;
	}
	return &callees_global_defs[fid];
}

set<variable_id> * side_effects:: 
get_callees_global_uses (struct cgraph_node * func)
{
	function_id fid = func->uid;
	if (callees_global_uses.find (fid) == callees_global_uses.end ())
	{
		RESULT ("\nError: callees_global_uses for func=%d is NULL", fid);
		return NULL;
	}
	return &callees_global_uses[fid];
}

set<variable_id> * side_effects:: 
get_callees_lhs_derefs (struct cgraph_node * func)
{
	function_id fid = func->uid;
	if (callees_lhs_derefs.find (fid) == callees_lhs_derefs.end ())
	{
		RESULT ("\nError: callees_lhs_derefs for func=%d is NULL", fid);
		return NULL;
	}
	return &callees_lhs_derefs[fid];
}

set<variable_id> * side_effects:: 
get_function_param_defs (struct cgraph_node * func)
{
	function_id fid = func->uid;
	if (function_param_defs.find (fid) == function_param_defs.end ())
	{
		RESULT ("\nError: function_param_defs for func=%d is NULL", fid);
		return NULL;
	}
	return &function_param_defs[fid];
}

/** 
 * This function is called from all analyses by ipa/context.cpp. Until then
 * dfv/side_effects may not have been populated. Therefore, return
 * "unimportant" if not populated.
 */ 

bool side_effects::
is_block_unimportant (struct cgraph_node * func, block_index bid)
{
	function_id fid = func->uid;
	if (unimportant_blocks.find (fid) == unimportant_blocks.end ())
	{
		if (is_unimp_blocks_ready)
			RESULT ("\nError: unimportant_blocks of func=%d not found", fid);
		return false;
	}
	if (unimportant_blocks[fid].find (bid) != unimportant_blocks[fid].end ())
		return true;
	return false;
}

void side_effects::
add_unimportant_blocks (struct cgraph_node * func, set<block_index> & blocks)
{
	function_id fid = func->uid;
	unimportant_blocks[fid].insert (blocks.begin (), blocks.end ());
}

void side_effects:: 
add_callees_lhs_derefs (struct cgraph_node * func, set<variable_id> & vars)
{
	function_id fid = func->uid;
	callees_lhs_derefs[fid].insert (vars.begin (), vars.end ());
}

void side_effects:: 
add_callees_global_defs (struct cgraph_node * func, set<variable_id> & vars)
{
	function_id fid = func->uid;
	callees_global_defs[fid].insert (vars.begin (), vars.end ());
}

void side_effects:: 
add_callees_global_uses (struct cgraph_node * func, set<variable_id> & vars)
{
	function_id fid = func->uid;
	callees_global_uses[fid].insert (vars.begin (), vars.end ());
}

void side_effects:: 
add_function_param_defs (struct cgraph_node * func, set<variable_id> & vars)
{
	function_id fid = func->uid;
	function_param_defs[fid].insert (vars.begin (), vars.end ());
}

void side_effects::
print_side_effects ()
{
	map<function_id, set<variable_id> >::iterator fi;
	DEBUG ("\ncallees_global_defs=");
	for (fi = callees_global_defs.begin (); fi != callees_global_defs.end (); fi++)
	{
		function_id fid = fi->first;
		struct cgraph_node * cnode = program.get_cgraph_node (fid);
		const char * function_name = cgraph_node_name (cnode);
		DEBUG ("\n\tFunction=%s(%d)=", function_name, fid);
		set<variable_id> vars = fi->second;
		set<variable_id>::iterator vi;
		for (vi = vars.begin (); vi != vars.end (); vi++)
		{ 
			csvarinfo_t var = program.cs_get_varinfo (*vi);
			DEBUG ("%s(%d),", var->name, var->id);
		}
	}

	DEBUG ("\ncallees_global_uses=");
	for (fi = callees_global_uses.begin (); fi != callees_global_uses.end (); fi++)
	{
		function_id fid = fi->first;
		struct cgraph_node * cnode = program.get_cgraph_node (fid);
		const char * function_name = cgraph_node_name (cnode);
		DEBUG ("\n\tFunction=%s(%d)=", function_name, fid);
		set<variable_id> vars = fi->second;
		set<variable_id>::iterator vi;
		for (vi = vars.begin (); vi != vars.end (); vi++)
		{ 
			csvarinfo_t var = program.cs_get_varinfo (*vi);
			DEBUG ("%s(%d),", var->name, var->id);
		}
	}

	DEBUG ("\nfunction_param_defs=");
	for (fi = function_param_defs.begin (); fi != function_param_defs.end (); fi++)
	{
		function_id fid = fi->first;
		struct cgraph_node * cnode = program.get_cgraph_node (fid);
		const char * function_name = cgraph_node_name (cnode);
		DEBUG ("\n\tFunction=%s(%d)=", function_name, fid);
		set<variable_id> vars = fi->second;
		set<variable_id>::iterator vi;
		for (vi = vars.begin (); vi != vars.end (); vi++)
		{ 
			csvarinfo_t var = program.cs_get_varinfo (*vi);
			DEBUG ("%s(%d),", var->name, var->id);
		}
	}

	DEBUG ("\ncallees_lhs_derefs=");
	for (fi = callees_lhs_derefs.begin (); fi != callees_lhs_derefs.end (); fi++)
	{
		function_id fid = fi->first;
		struct cgraph_node * cnode = program.get_cgraph_node (fid);
		const char * function_name = cgraph_node_name (cnode);
		DEBUG ("\n\tFunction=%s(%d)=", function_name, fid);
		set<variable_id> vars = fi->second;
		set<variable_id>::iterator vi;
		for (vi = vars.begin (); vi != vars.end (); vi++)
		{ 
			csvarinfo_t var = program.cs_get_varinfo (*vi);
			DEBUG ("%s(%d),", var->name, var->id);
		}
	}
}

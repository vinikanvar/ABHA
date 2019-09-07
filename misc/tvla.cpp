 
/************************
 * @author Vini Kanvar
************************/

#include "tvla.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...) 

#define SETS_TVP(...) { \
	FILE * sets_tvp_file_ptr = fopen (SETS_TVP_FILE, "a"); \
	fprintf (sets_tvp_file_ptr, __VA_ARGS__); \
	fclose (sets_tvp_file_ptr); \
}

#define CFG_TVP(...) { \
	FILE * cfg_tvp_file_ptr = fopen (CFG_TVP_FILE, "a"); \
	fprintf (cfg_tvp_file_ptr, __VA_ARGS__); \
	fclose (cfg_tvp_file_ptr); \
}

#define TVLA_FUNCTIONS 0

void tvla::
print_tvp_dsel (unsigned int offset)
{
	CFG_TVP ("f_%d", offset);

	// stringstream str_offset;
	// str_offset << offset;
	// string str = "f_" + str_offset.str ();
	string str = "f_" + to_string (offset);
	program_dsel.insert (str);
}

void tvla::
print_tvp_list (list<csvarinfo_t> & vars)
{
	list<csvarinfo_t>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); )
	{
		print_tvp_pvar (*vi);

		vi++;
		if (vi != vars.end ())
			CFG_TVP (",");
	}
}

void tvla::
replace_char (string & s)
{
	for (int i = 0; i < s.length (); i++)
		if (s[i] == '+')
			s[i] = '_';
}

void tvla::
print_tvp_set (set<string> & vars)
{
	set<string>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); )
	{
		string s = *vi;
		replace_char (s);
		SETS_TVP ("%s", s.c_str ());

		vi++;
		if (vi != vars.end ())
			SETS_TVP (",");
	}
}

void tvla::
insert_tvp_pvars (list<csvarinfo_t> & src,
	set<string> & dest)
{
	list<csvarinfo_t>::iterator li;
	for (li = src.begin (); li != src.end (); li++)
	{
		csvarinfo_t var = *li;
		insert_tvp_pvar (var, dest);
	}
}

void tvla::
insert_tvp_pvar (csvarinfo_t var,
	set<string> & dest)
{
	string name (var->name);
	string str = name + "." + to_string (var->id);
	dest.insert (str);
}

void tvla::
print_tvp_pvar (csvarinfo_t var)
{
	CFG_TVP ("%s.%d", var->name, var->id);
}

void tvla::
collect_tvp_pvars ()
{
	for (int index = 0; index < VEC_length (csvarinfo_t, program.variable_data); index++)
	{
	        csvarinfo_t variable = VEC_index (csvarinfo_t, program.variable_data, index);
		const char * function_name = NULL;
		if (variable && variable->scoping_function)
			function_name = cgraph_node_name (variable->scoping_function);
		
		insert_tvp_pvar (variable, program_pvar);
	}
}

void tvla::
print_tvp_empty ()
{
	CFG_TVP (" Empty()");
}

void tvla::
print_tvp_malloc (constraint_expr lhs)
{
        csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, program.variable_data, lhs.var);

	CFG_TVP (" Malloc(");
	print_tvp_pvar (lhs_variable);
	CFG_TVP (") ");
}

void tvla::
print_tvp_copy_var (constraint_expr lhs, constraint_expr rhs)
{
        csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, program.variable_data, lhs.var);
        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, program.variable_data, rhs.var);

	CFG_TVP (" Copy_Var(");
	print_tvp_pvar (lhs_variable);
	CFG_TVP (",");
	print_tvp_pvar (rhs_variable);
	CFG_TVP (") ");
}

void tvla::
print_tvp_get_sel (constraint_expr lhs, constraint_expr rhs)
{
        csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, program.variable_data, lhs.var);
        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, program.variable_data, rhs.var);

	CFG_TVP (" Get_Sel(");
	print_tvp_pvar (lhs_variable);
	CFG_TVP (",");
	print_tvp_pvar (rhs_variable);
	CFG_TVP (",");
	print_tvp_dsel (rhs.offset);
	CFG_TVP (") ");
}

void tvla::
print_tvp_set_sel (constraint_expr lhs, constraint_expr rhs)
{
        csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, program.variable_data, lhs.var);
        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, program.variable_data, rhs.var);

	CFG_TVP (" Set_Sel(");
	print_tvp_pvar (lhs_variable);
	CFG_TVP (",");
	print_tvp_dsel (lhs.offset);
	CFG_TVP (",");
	print_tvp_pvar (rhs_variable);
	CFG_TVP (") ");
}

void tvla::
print_tvp_ff (constraint_expr lhs, constraint_expr rhs)
{

	switch (lhs.type)
	{
	case SCALAR:
		switch (rhs.type)
		{
		// lhs=..., ...=rhs or ...=&(rhs->f)
		case SCALAR:
			print_tvp_copy_var (lhs, rhs);
			break;
		// lhs=..., ...=&rhs
		case ADDRESSOF:
			if (program.heap_var (rhs.var))
				print_tvp_malloc (lhs);
			else
				// FIXME: Handle address taken stack locations
				print_tvp_empty ();
			break;
		// lhs=..., ...=rhs->f or ...=*rhs
		case DEREF:
			print_tvp_get_sel (lhs, rhs);
			break;
		default:
			RESULT ("\nError: rhs cannot hold fourth type");
		}
		break;
	case DEREF:
		switch (rhs.type)
		{
		//lhs->f=... or *lhs=..., ...=rhs or ...=&(rhs->f)
		case SCALAR:
			print_tvp_set_sel (lhs, rhs);
			break;
		//lhs->f=... or *lhs=, ...=&rhs
		case ADDRESSOF:
			if (program.heap_var (rhs.var))
				print_tvp_malloc (lhs);
			else
				// FIXME: Handle address taken stack locations
				print_tvp_empty ();
			break;
		//lhs->f=... or *lhs=..., ...=*rhs or ...=rhs->f
		case DEREF:
			break;
		default:
			RESULT ("\nError: rhs cannot hold fourth type");
		}
		break;
	case ADDRESSOF:
		RESULT ("\nError: Lvalue error.");
		break;
	default:
		RESULT ("\nError: lhs cannot hold fourth type");
	} 
}

void tvla::
print_tvp_ff (int index)
{
        constraint_t assignment = VEC_index (constraint_t, program.assignment_data, index);
	DEBUG ("\nassignment index=%d, addr=%x", index, assignment);
        constraint_expr lhs = assignment->lhs;
        constraint_expr rhs = assignment->rhs;
//        csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, program.variable_data, lhs.var);
//        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, program.variable_data, rhs.var);
//        DEBUG ("\nLHS: variable id %d, ptr_arith=%d, offset %llu(",
//                lhs.var, lhs.pointer_arithmetic, lhs.offset);
//	list<unsigned int>::iterator ofi;
//	if (lhs.offset_sequence)
//		for (ofi = lhs.offset_sequence->begin (); ofi != lhs.offset_sequence->end (); ofi++)
//			DEBUG ("%d,", *ofi);
//	DEBUG ("), type %d, name %s, RHS: variable id %d, ptr_arith=%d, offset %llu(",
//		lhs.type, lhs_variable->name, 
//                rhs.var, rhs.pointer_arithmetic, rhs.offset);
//	if (rhs.offset_sequence)
//		for (ofi = rhs.offset_sequence->begin (); ofi != rhs.offset_sequence->end (); ofi++)
//			DEBUG ("%d,", *ofi);
//	DEBUG ("), type %d, name %s",
//                rhs.type, rhs_variable->name);
//	DEBUG (", previous_phi=%d", assignment->previous_phi != NULL);

	print_tvp_ff (lhs, rhs);
}

void tvla::
get_tvp_pairs (basic_block call_site,
	list<csvarinfo_t> & lhs,
	list<csvarinfo_t> & rhs)
{
        list<pair<unsigned int, bool> > parsed_data_indices = 
		((block_information *)(call_site->aux))->get_parsed_data_indices ();

        list<pair<unsigned int, bool> >::iterator it;
        for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
        {
                unsigned int index = (*it).first;
                bool is_assignment = (*it).second;
                DEBUG ("\nParsed data: index %d, bool %d, block %d, ", 
			index, is_assignment, call_site->index);

                if (!is_assignment)
			continue;
		// Assume lhs=rhs type (there is no * or &)

        	constraint_t assignment = VEC_index (constraint_t, program.assignment_data, index);
        	constraint_expr lhs_expr = assignment->lhs;
	        constraint_expr rhs_expr = assignment->rhs;
        	csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, program.variable_data, lhs_expr.var);
	        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, program.variable_data, rhs_expr.var);
		lhs.push_back (lhs_variable);
		rhs.push_back (rhs_variable);
	}

	if (lhs.size () != rhs.size ())
		RESULT ("\nError: lhs and rhs not extracted.");
}

void tvla::
print_tvp_params_args (cgraph_node * calling_function, 
	basic_block call_site, 
	cgraph_node * called_function,
	list<csvarinfo_t> & params,
	list<csvarinfo_t> & args)
{
	// Fetch all assignments
	// Fetch args (rhs) and formals (lhs)
	// \nL_func_%d_bb_%d_start 
	// Call_2args(a1,a2,f1,f2)
	// L_%s.%d_start, cgraph_node_name(called_function), called_function->uid

	((block_information *)(call_site->aux))->erase_assignment_indices ();
	program.map_function_pointer_arguments (calling_function, call_site, called_function);
	get_tvp_pairs (call_site, params, args);
	unsigned int count = args.size ();
	print_tvp_block_start (calling_function, call_site);
	CFG_TVP (" Call_%dargs(", count);
	print_tvp_list (args);
	if (count)
		CFG_TVP (",");
	print_tvp_list (params);
	CFG_TVP (") ");
	CFG_TVP (" L_%s.%d_start", cgraph_node_name (called_function), called_function->uid);
	((block_information *)(call_site->aux))->erase_assignment_indices ();
}

void tvla::
print_tvp_rec (cgraph_node * calling_function, 
	basic_block call_site, 
	cgraph_node * called_function,
	list<csvarinfo_t> & params,
	list<csvarinfo_t> & args,
	list<csvarinfo_t> & rec,
	list<csvarinfo_t> & ret)
{
	// Fetch received variable
	// \nL_func_%d_bb_%d_start 
	// Call_2Return_2args(a1,a2,f1,f2,rec)
	//  L_func_%d_bb_%d_start_b, 

	((block_information *)(call_site->aux))->erase_assignment_indices ();
	basic_block end_block = program.get_end_block_of_function (called_function);
	// Find return blocks before end_block. There could be more than one
	// return blocks (e.g. test-cases/test31b.c).
	edge e;
	edge_iterator ei;
	FOR_EACH_EDGE (e, ei, end_block->preds)
	{
		basic_block return_block = e->src;
		// This function always fetches/creates a new map entry in
		// assignment pool.
		program.map_return_value (call_site, calling_function, return_block, called_function);
	}
	get_tvp_pairs (call_site, rec, ret);
	if (rec.size () > 1)
		RESULT ("\nError: Multiple return statements not handled"); 
	unsigned int count_args = args.size ();
	unsigned int count_rec = rec.size ();
	print_tvp_block_start (calling_function, call_site);

	if (count_rec)
	{
		CFG_TVP (" CalltoReturn_%dargs(", count_args);
	}
	else
	{
		CFG_TVP (" CalltoFuncEnd_%dargs(", count_args);
	}
	print_tvp_list (args);
	if (count_args)
		CFG_TVP (",");
	print_tvp_list (params);
	if (count_rec)
	{
		CFG_TVP (",");
		print_tvp_pvar (rec.front ());
	}
	CFG_TVP (") ");
	CFG_TVP (" L_func_%d_bb_%d_start_b", calling_function->uid, call_site->index);
}

void tvla::
print_tvp_rec_ret (cgraph_node * calling_function, 
	basic_block call_site, 
	cgraph_node * called_function,
	list<csvarinfo_t> & params,
	list<csvarinfo_t> & args,
	list<csvarinfo_t> & rec,
	list<csvarinfo_t> & ret)
{
	// Fetch returned variable
	// L_func_%d_bb_%d_end, called_function->uid, end_block_of_called_function
	// Return_2args(a1,a2,f1,f2,rec,ret)
	//  L_func_%d_bb_%d_start_b, 

	basic_block end_block = program.get_end_block_of_function (called_function);
	if (rec.size () > 1)
		RESULT ("\nError: Multiple return statements not handled"); 
	unsigned int count_args = args.size ();
	unsigned int count_rec = rec.size ();
	CFG_TVP ("\nL_func_%d_bb_%d_end", called_function->uid, end_block->index);
	if (count_rec)
	{
		CFG_TVP (" Return_%dargs(", count_args);
	}
	else
	{
		CFG_TVP (" FuncEnd_%dargs(", count_args);
	}
	print_tvp_list (args);
	if (count_args)
		CFG_TVP (",");
	print_tvp_list (params);
	if (count_args)
		CFG_TVP (",");
	if (count_rec)
	{
		print_tvp_pvar (rec.front ());
		CFG_TVP (",");
		print_tvp_pvar (ret.front ());
	}
	CFG_TVP (") ");
	CFG_TVP (" L_func_%d_bb_%d_start_b", calling_function->uid, call_site->index);

	insert_tvp_pvars (args, program_args);
	insert_tvp_pvars (params, program_params);
	insert_tvp_pvars (rec, program_recs);
}

void tvla::
print_tvp_merge_rec (cgraph_node * calling_function, 
	basic_block call_site, 
	cgraph_node * called_function,
	list<csvarinfo_t> & params,
	list<csvarinfo_t> & args,
	list<csvarinfo_t> & rec,
	list<csvarinfo_t> & ret)
{
	//  L_func_%d_bb_%d_start_b, 
	// Merge_2args(a1,a2,rec)

	basic_block end_block = program.get_end_block_of_function (called_function);
	if (rec.size () > 1)
		RESULT ("\nError: Multiple return statements not handled"); 
	unsigned int count_args = args.size ();
	unsigned int count_rec = rec.size ();
	CFG_TVP ("\nL_func_%d_bb_%d_start_b", calling_function->uid, call_site->index);
	if (count_rec)
	{
		CFG_TVP (" MergeatReturn_%dargs(", count_args);
	}
	else
	{
		CFG_TVP (" MergeatFuncEnd_%dargs(", count_args);
	}
	print_tvp_list (args);
	if (count_rec)
	{
		CFG_TVP (",");
		print_tvp_pvar (rec.front ());
	}
	CFG_TVP (") ");
}

void tvla::
print_tvp_call (cgraph_node * calling_function, basic_block call_site)
{
	// If function pointer, return.
        gimple_stmt_iterator gsi = gsi_start_bb (call_site);
        gimple statement = gsi_stmt (gsi);
        // If we can resolve it here, its a simple function call. 
        tree decl = gimple_call_fndecl (statement);
        // The call is through function pointer. 
        if (!decl)
		return;

	// Get called function
        struct cgraph_node * called_function = cgraph_get_node (decl);

	list<csvarinfo_t> params;
	list<csvarinfo_t> args;
	print_tvp_params_args (calling_function, call_site, called_function,
		params, args);
	
	list<csvarinfo_t> rec;
	list<csvarinfo_t> ret;
	print_tvp_rec (calling_function, call_site, called_function,
		params, args, rec, ret);

	print_tvp_rec_ret (calling_function, call_site, called_function,
		params, args, rec, ret);

	print_tvp_merge_rec (calling_function, call_site, called_function,
		params, args, rec, ret);

	print_tvp_block_end (calling_function, call_site);
}

void tvla::
print_tvp_block_start (cgraph_node * cnode, basic_block current_block)
{
	CFG_TVP ("\nL_func_%d_bb_%d_start", cnode->uid, current_block->index);
}

void tvla::
print_tvp_block_end (cgraph_node * cnode, basic_block current_block)
{
	CFG_TVP (" L_func_%d_bb_%d_end", cnode->uid, current_block->index);

	edge e;
	edge_iterator ei;
	FOR_EACH_EDGE (e, ei, current_block->succs)
	{
		CFG_TVP ("\nL_func_%d_bb_%d_end ", cnode->uid, current_block->index);
		print_tvp_empty ();

		basic_block succ_block = e->dest;
		CFG_TVP (" L_func_%d_bb_%d_start", cnode->uid, succ_block->index);
	}
}

void tvla::
print_tvp_block_ff (cgraph_node * cnode, basic_block current_block)
{
	DEBUG ("\nPrinting parsed data of block %d", current_block->index);

        list<pair<unsigned int, bool> > parsed_data_indices = 
		((block_information *)(current_block->aux))->get_parsed_data_indices ();
		
	print_tvp_block_start (cnode, current_block);
	print_tvp_empty ();

        list<pair<unsigned int, bool> >::iterator it;
        for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
        {
                unsigned int index = (*it).first;
                bool is_assignment = (*it).second;
                DEBUG ("\nParsed data: index %d, bool %d, block %d, ", 
			index, is_assignment, current_block->index);
		CFG_TVP (" L_%d", index);
		CFG_TVP ("\nL_%d ", index);
                if (is_assignment)
			print_tvp_ff (index);
		else
			print_tvp_empty ();
        }

	print_tvp_block_end (cnode, current_block);
}

void tvla::
print_tvp_function_start (cgraph_node * cnode)
{
	CFG_TVP ("\nL_%s.%d_start ", cgraph_node_name (cnode), cnode->uid);

	list<csvarinfo_t> params;
	csvarinfo_t func = program.cs_lookup_vi_for_tree (cnode->decl);
	// Iterate and count number of parameters
	unsigned int param_num;
	tree t;
	for (param_num = 1, t = DECL_ARGUMENTS (cnode->decl); 
		t; 
		param_num++, t = DECL_CHAIN (t))
	{
		csvarinfo_t param = program.cs_first_vi_for_offset (func, param_num);
		params.push_back (param);
	}
	
	unsigned int count = params.size ();
	CFG_TVP (" Init_%dformals(", count);
	print_tvp_list (params);
	CFG_TVP (")");

	basic_block start_block = program.get_start_block_of_function (cnode);
	CFG_TVP (" L_func_%d_bb_%d_start", cnode->uid, start_block->index);
	print_tvp_block_ff (cnode, start_block);
	basic_block end_block = program.get_end_block_of_function (cnode);
	print_tvp_block_ff (cnode, end_block);
}

void tvla::
print_tvp_assignments ()
{
   	struct cgraph_node * cnode = NULL; 
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

                DEBUG ("\nFunction : %s\n", cgraph_node_name (cnode));

#if TVLA_FUNCTIONS
		print_tvp_function_start (cnode);
#endif

		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
			if (!current_block->aux)
				continue;

			unsigned int bt = ((block_information *)(current_block->aux))->get_block_type ();
			if (bt & CALL_BLOCK)
			{
#if TVLA_FUNCTIONS
				print_tvp_call (cnode, current_block);
#else
				print_tvp_block_start (cnode, current_block);
				print_tvp_empty ();
				print_tvp_block_end (cnode, current_block);
#endif
			}			
			else
				print_tvp_block_ff (cnode, current_block);
		}

		pop_cfun();
	}
}

void tvla::
print_tvp_file ()
{
	// Clear tvp file contents
	FILE * sets_tvp_file_ptr = fopen (SETS_TVP_FILE, "w"); 
	fprintf (sets_tvp_file_ptr, ""); 
	fclose (sets_tvp_file_ptr); 
	FILE * cfg_tvp_file_ptr = fopen (CFG_TVP_FILE, "w"); 
	fprintf (cfg_tvp_file_ptr, ""); 
	fclose (cfg_tvp_file_ptr); 


	CFG_TVP ("\n#include \"sets.tvp\"");
	CFG_TVP ("\n#include \"predicates.tvp\"");
	CFG_TVP ("\n%%%%");
	CFG_TVP ("\n#include \"actions.tvp\"");
	CFG_TVP ("\n%%%%");
	CFG_TVP ("\n");

	print_tvp_assignments ();

	collect_tvp_pvars ();
	SETS_TVP ("\n%%s PVar {");
	print_tvp_set (program_pvar);
	SETS_TVP ("}\n");
	SETS_TVP ("\n%%s DSel {");
	print_tvp_set (program_dsel);
	SETS_TVP ("}\n");
#if TVLA_FUNCTIONS
	SETS_TVP ("\n%%s Params {");
	print_tvp_set (program_params);
	SETS_TVP ("}\n");
	SETS_TVP ("\n%%s Args {");
	print_tvp_set (program_args);
	if (program_args.size ())
		SETS_TVP(",");
	print_tvp_set (program_recs);
	SETS_TVP ("}\n");
#endif
}


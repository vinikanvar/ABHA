
/************************
 * @author Vini Kanvar
************************/

#include "unlabeled_edges.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

unlabeled_edges::
unlabeled_edges ()
{
	DEBUG ("\nalloc unlabeled_edges=%x", this);
	reference_count = 0;
	NEW_ADDR ("\nnew unlabeled_edges %x", this);
}

unlabeled_edges::
~unlabeled_edges ()
{
	DEBUG ("\ndealloc unlabeled_edges=%x", this);
	DEBUG ("\nGC of allocation_site_based graph");
	GC_ADDR ("\ngc unlabeled_edges %x", this);
	erase ();
}

void unlabeled_edges::
erase ()
{
	out_edge_list.clear ();
	in_edge_list.clear ();
}

void unlabeled_edges::
increment_reference_count ()
{
        reference_count++;
}

void  unlabeled_edges::
decrement_reference_count ()
{
        if (!reference_count)
        {
                RESULT ("\nError: reference count of unlabeled_edges was already 0");
                return;
        }

        reference_count--;
        DEBUG ("\nCount = %d (after decr) of unlabeled_edges", reference_count);
        if (!reference_count)
        {
#if GC
                DEBUG ("\nGC unlabeled_edges");
                delete this;
#endif
        }
}

/**
 * This function checks if THIS unlabeled_edges is same as the parameter unlabeled_edges.
 */

bool unlabeled_edges::
is_value_same (unlabeled_edges & value)
{
	// If address of THIS and g is same, return true;
	if (this == &value)
	{
		DEBUG ("\nOptimum graph is_value_same()");
		return true;
	}

        return (out_edge_list == value.out_edge_list);
}

/**
 * This function creates a copy of THIS unlabeled_edges.
 */

unlabeled_edges * unlabeled_edges::
copy_value (bool is_loop_merge)
{
	DEBUG ("\ncopy_value()");
        unlabeled_edges * new_value = new unlabeled_edges ();
        new_value->copy_value (*this, is_loop_merge);
	DEBUG ("\ncopied value");
	fflush (dump_file);
        return new_value;
}

/**
 * This function copies VALUE to THIS unlabeled_edges.
 */

void unlabeled_edges::
copy_value (unlabeled_edges & value, bool is_loop_merge)
{
	DEBUG ("\ncopy_value()");
	map<label, set<label> >::iterator ei;
	for (ei = value.out_edge_list.begin (); ei != value.out_edge_list.end (); ei++)
	{
		label ptr = ei->first;
		set<label> pte = ei->second;
		if (pte.size ())
		{
			DEBUG ("\nptr=%d, pte.size=%d", ptr, pte.size ());
			out_edge_list[ptr].insert (pte.begin (), pte.end ());
		}
	}
}

void unlabeled_edges::
clean ()
{
#if ALLOC_EFFICIENT
	// FIXME
	// remove unreachable heap nodes
	// Do not call clean () if context-dept value has been split into
	// unaffected part (saved as aux) and changing part (saved
	// flow-sensitively).
#endif
}

void unlabeled_edges::
gen (label variable, set<label> & dest_vars)
{
	if (!dest_vars.size ())
		return;

	if (!program.is_proper_var (variable))
		return;

	if (dest_vars.size ())
		out_edge_list[variable].insert (dest_vars.begin (), dest_vars.end ());
}

void unlabeled_edges::
gen (set<label> & variables, set<label> & dest_vars)
{
	set<label>::iterator vi;
	for (vi = variables.begin (); vi != variables.end (); vi++)
		gen (*vi, dest_vars);
}

void unlabeled_edges::
count_dead_vars (set<label> & variables)
{
#if ALLOC_STATISTICS_CONTAINER
	DEBUG ("\nkill(variables)");
	set<label>::iterator vi;
	for (vi = variables.begin (); vi != variables.end (); vi++)
	{
		label dead_v = *vi;
		if (out_edge_list.find (dead_v) != out_edge_list.end ())
		{
			dead_locals_stats.dead_locals_pta.insert (dead_v);
			dead_locals_stats.tot_dead_locals_pta++;
		}
	}
	dead_locals_stats.tot_filterings++;
#endif
}

void unlabeled_edges::
kill (label variable)
{
	if (out_edge_list.find (variable) == out_edge_list.end ())
	{
		DEBUG ("\nNo pointee of variable=%d is found", variable);
		return;
	}

	DEBUG ("\nErasing pointee of variable=%d", variable);
	out_edge_list.erase (variable);
}

void unlabeled_edges::
kill (set<label> & variables)
{
	DEBUG ("\nkill(variables)");
	set<label>::iterator vi;
	for (vi = variables.begin (); vi != variables.end (); vi++)
	{
		DEBUG ("\nkilling var=%d", *vi);
		kill (*vi);
	}
}

void unlabeled_edges::
kill_pointees (set<label> & pointees)
{
	// FIXME: Pathetic coding. Prepare a reverse map of pointees to
	// pointers. Then delete the pointees from the pointers.

	set<label>::iterator ptei;
	for (ptei = pointees.begin (); ptei != pointees.end (); ptei++)
	{
		label pte = *ptei;
		map<label, set<label> >::iterator ptri;
		for (ptri = out_edge_list.begin (); ptri != out_edge_list.end (); ptri++)
		{
			ptri->second.erase (pte);
		}
	}
}

/**
 * This function kills the out_edge_list of THIS graph from VALUE.
 */

void unlabeled_edges::
kill_out_edges (unlabeled_edges & value)
{
	map<label, set<label> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		label src = ei->first;
		set<label> dests = ei->second;
		set<label>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
		{
			value.out_edge_list[src].erase (*di);
		}
	}
}

void unlabeled_edges::
kill_dead_pts_edges (set<label> & live_pts_nodes)
{
        map<label, set<label> >::iterator ei;
        for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
        {
                label v = ei->first;

                // If a pts variable does not correspond to any live node, then
                // delete all its out-edges
                if (live_pts_nodes.find (v) == live_pts_nodes.end ())
                        kill (v);
        }
}

void unlabeled_edges::
get_destination_vars (set<label> & vars, set<label> & dest_vars)
{
	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
	{
		get_destination_vars (*vi, dest_vars);
	}
}

void unlabeled_edges::
get_destination_vars (label variable, set<label> & dest_vars)
{
	if (out_edge_list.find (variable) == out_edge_list.end ())
	{
		DEBUG ("\nPointer of variable %d does not exist");
#if UNDEF_LOCATION
		dest_vars.insert (undef_id);
#endif
		return;
	}

	set<label> vars = out_edge_list[variable];
	dest_vars.insert (vars.begin (), vars.end ());
}

/**
 * This function fetches nodes pointed by VARIABLE.*.FIELD. This function is
 * called by statement where VAR is a stack variable. Therefore, pointee of VAR
 * is typecasted to type of VAR.
 */

void unlabeled_edges::
get_pointer_vars (label var, label offset, set<label> & pointer_vars)
{
	DEBUG ("\nget_pointer_vars()");

	// Get VARIABLE.*
	set<label> dest_vars;
	get_destination_vars (var, dest_vars);

	// Get VARIABLE.*.FIELD
        // Get type of VAR being dereferenced. This is required if a heap
        // field variable needs to be created on-the-fly.
        csvarinfo_t var_info = VEC_index (csvarinfo_t, program.variable_data, var);
        list<label>::iterator fi;

	set<label>::iterator vi;
	for (vi = dest_vars.begin (); vi != dest_vars.end (); vi++)
	{
		label dest_var = *vi;
#if DEBUG_CONTAINER
        	csvarinfo_t dest_var_info = 
			VEC_index (csvarinfo_t, program.variable_data, dest_var);
		DEBUG ("\nget_field_vars(dest_var=%d,offset=%d)", dest_var, offset);
#endif

		// Parameter 1: DEST_VAR = variable to be dereferenced, i.e.
		// the pointee of VAR. Note that if DEST_VAR is a field
		// variable, then decl of csvarinfo of DEST_VAR is the decl of
		// root of the field.  We need to use get_decl(csvarinfo of
		// DEST_VAR) to get decl of field instead of decl of root.

		// Parameter 2: ideally this should be the typecasted type of
		// VAR.  E.g. in MEM[(new_type) VAR].offset, ideally parameter
		// 2 should be new_type. But this information is not saved in
		// constraint_expr and VAR saves its original declared type
		// only. Therefore, we are sending type of VAR only as
		// parameter 2.

		// If pointer var type /= pointee type, and pointer var type /=
		// void *, then we typecast. In short, cases where only pointer
		// and pointee types matter, are handled.
		// However, if pointee variable type /= typecasted type /=
		// pointer var type, then we do not typecast. In short, cases
		// where typecasted type matters, are not handled.

		// FIXME:
		// Save typecasted type of VAR in constraint_expr and pass that
		// as parameter 2.

		get_field_vars (dest_var, var_info->decl, offset, pointer_vars);
	}
}

void unlabeled_edges::
get_field_vars (label var, tree var_type, label offset, set<label> & pointer_vars)
{
	DEBUG ("\nget_field_vars(var=%d,offset=%d)", var, offset);

	if (!program.is_proper_var (var))
	{
#if UNDEF_LOCATION
		pointer_vars.insert (undef_id);
#endif
		return;
	}
	if (!program.heap_var (var))
	{
		csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, var);
		csvarinfo_t vf_info = program.cs_first_vi_for_offset (v_info, offset);
		if (vf_info)
		{
			pointer_vars.insert (vf_info->id);
			DEBUG ("\nNon-heap, vf_info=%s(%d)", vf_info->name, vf_info->id);
			return;
		}

	}

	get_heap_field_vars (var, var_type, offset, pointer_vars);
}

/** 
 * This function is called for heap VAR whose decl may or may not be VOID *.
 * Heap fields are created for VAR_TYPE if offset is not found.
 */

void unlabeled_edges::
get_heap_field_vars (label var, tree var_type, label offset, set<label> & pointer_vars)
{
	DEBUG ("\nget_heap_field_vars(var=%d,offset=%d)", var, offset);

	if (!program.heap_var (var))
	{
		RESULT ("\nError: Stack var=%d offset=%d does not exist", var, offset);
		return;
	}
	// If VAR_TYPE is NULL, do not consider it as an error. We do not
	// perform typecasting in that case and simply find offset from VAR.

	// bool was_heap_void = true;
	// csvarinfo_t hv_info = VEC_index (csvarinfo_t, program.variable_data, var);
	// tree decl = hv_info->decl;
	// If type of HV_INFO was not VOID *.
	// if (decl && TREE_CODE (decl) == VAR_DECL/PARM_DECL 
	//	&& TREE_TYPE (decl) != ptr_type_node)
	// // If HV_INFO already had some fields.
	// // if (hv_info->offset || hv_info->next)
	//	was_heap_void = false;


	DEBUG ("\non-the-fly generation needed.");
	DEBUG ("\nget_heap_field_vars, var=%d offset=%d", var, offset);
	csvarinfo_t heap_field_var = 
		program.generate_heap_field_vars (var, var_type, offset);
	if (!heap_field_var)
	{
		RESULT ("\nError: heap var=%d field=%d not created/found", var, offset);
		return;
	}

	// Heap offset has now been found after creating new VAR_TYPE.

	// If original heap was not of VOID *.
	// if (!was_heap_void)
	// {
		// This is not an error since this function is called even for non-void VAR.
		// // RESULT ("\nError: heap %s(%d) offset=%d not found, although fields exist", 
		// //      hv_info->name, hv_info->id, field + hv_info->offset);
		// RESULT ("\nError:? heap %s(%d) has been re-typecasted", hv_info->name, hv_info->id);
	// }

	DEBUG ("\nTypecasted heap field=%d", heap_field_var->id);
	pointer_vars.insert (heap_field_var->id);
}

/**
 * Fetches nodes pointed by VARIABLE.*.FIELD.*. 
 * 
 * @returns true if the destination is undef and UNDEF node does not exist in
 * THIS graph.
 *
 */

void unlabeled_edges::
get_deref_vars (label variable, label offset, set<label> & dest_vars)
{
	DEBUG ("\nget_deref_vars (%d)", variable);
	set<label> pointer_vars;
	set<label> heap_vars;

	// Get VARIABLE.*.FIELD vars in POINTER_NODES.
	get_pointer_vars (variable, offset, pointer_vars);

	// Get VARIABLE.*.FIELD.* from POINTER_NODES 
	// If out_edge_missing is true, then the destination of
	// get_deref_vars() is undef.
	set<label>::iterator vi;
	for (vi = pointer_vars.begin (); vi != pointer_vars.end (); vi++)
	{
		label v = *vi;
		get_destination_vars (v, dest_vars);
	}
}


/**
 * Fetches nodes that are must pointed by VARIABLE.*.FIELD.
 */

void unlabeled_edges::
get_must_pointer_vars (label variable, label offset, set<label> & dest_nodes)
{
	// Get VARIABLE.*
	set<label> dest_vars;
	get_destination_vars (variable, dest_vars);

	label v = get_single_pointee (dest_vars);
	if (!v)
		return;

	// Get VARIABLE.*.FIELD
        csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, variable);
	set<label> field_vars;
	get_field_vars (v, v_info->decl, offset, field_vars);

	label vf = get_single_pointee (field_vars);
	if (!vf)
		return;

	dest_nodes.insert (vf);
}

label unlabeled_edges::
get_single_pointee (set<label> & dest_vars)
{
	if (dest_vars.size () != 1)
		return 0;

	label v = *(dest_vars.begin ());

	if (v == undef_id)
		return 0;

        // Return empty FIELD_NODES if the only name in DEST_NODES_NAMES is a
        // heap name.
        csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, v);
        if (v_info->is_heap_var)
                return 0;

	return v;
}

unlabeled_edges * unlabeled_edges::
extract_value (set<label> & reachable_from_vars,
	set<label> & destination_of_vars)
{
	DEBUG ("\nextract_reachable_value()");
	unlabeled_edges * reachable_value = new unlabeled_edges;

	set<label> reachable_vars;
	get_reachable_vars (reachable_from_vars, reachable_vars);

#if DEBUG_CONTAINER
        set<label>::iterator ni;
        DEBUG ("\nreachable vars: ");
        for (ni = reachable_vars.begin (); ni != reachable_vars.end (); ni++)
	{
		csvarinfo_t var = program.cs_get_varinfo (*ni);
                DEBUG ("%s(%d), ", var->name, var->id);
	}

#endif

	extract_destination_edges (reachable_vars, *reachable_value);
	extract_destination_edges (destination_of_vars, *reachable_value);

	return reachable_value;
}

void unlabeled_edges::
get_reachable_vars (set<label> & vars, set<label> & reachable_vars)
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
	// Get reachable from all typecasts
	for (vti = var_typecasts.begin (); vti != var_typecasts.end (); vti++)
	{
		csvarinfo_t vt = *vti;
		DEBUG ("\nget_reachable_vars(%s(%d))", vt->name, vt->id);
		get_reachable_vars (vt->id, reachable_vars);
	}
}

void unlabeled_edges::
get_reachable_vars (label var, set<label> & reachable_vars)
{
	// If var has already been considered
	if (reachable_vars.find (var) != reachable_vars.end ())
		return;

	DEBUG ("\nget_reachable_vars(var=%d)", var);

	reachable_vars.insert (var);

        // If the name of THIS var is y.32, then mark y.64 also as reachable.
        // Note that when y.32 is populated, it will recursively populate y.64
        // and so on too. Note that we do not need to insert y.0 because it is
        // not accessible from y.32. In case of access based abstraction, it
        // would be important to insert y.0 if y.0 is connected to y.32 etc via
        // a graph edge in which case out-edges will automatically insert y.0
        // var.

	// NEXT_FIELD of typecasted root node is not initialized. We should
	// fetch using tree of root node by calling GET_REACHABLE_FIELDS()
	// which fetches immediate member fields.
        // label next_field_var = program.get_next_field (var);

	set<label> out_vars;
	if (out_edge_list.find (var) != out_edge_list.end ())
		out_vars = out_edge_list[var];
	// out_vars.insert (next_field_var);

	csvarinfo_t src_var = program.cs_get_varinfo (var);
	program.get_reachable_fields (src_var, out_vars);

	get_reachable_vars (out_vars, reachable_vars);
}

void unlabeled_edges::
extract_destination_edges (set<label> & vars, unlabeled_edges & destination_value)
{
	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
	{
		label rvar = *vi;
		if (out_edge_list.find (rvar) != out_edge_list.end ())
			destination_value.gen (rvar, out_edge_list[rvar]);
		kill (rvar);
	}
}

void unlabeled_edges::
compute_in_edge_list ()
{
	if (in_edge_list.size ())
		return;

	DEBUG ("\nin_edge_list=");
	map<label, set<label> >::iterator outei;
	for (outei = out_edge_list.begin (); outei != out_edge_list.end (); outei++)
	{
		label src = outei->first;
		set<label> dests = outei->second;
		set<label>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
		{
			label dest = *di;
			in_edge_list[dest].insert (src);
			DEBUG ("\ndest=%d<-src=%d", dest, src);
		}
	}
}

void unlabeled_edges::
get_reaching_vars (set<label> & vars, 
	set<label> & reaching_vars)
{
	// vars should not be typecasted because we need to find reaching
	// fields and not reachable fields. Therefore, if var is a field, then
	// it already has correct type in decl, and if var is a root, there is
	// no point finding its typecast.

	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
	{
		get_reaching_vars (*vi, reaching_vars);
	}

//	// Get all typecasts
//	set<csvarinfo_t> var_typecasts;
//	set<label>::iterator vi;
//	for (vi = vars.begin (); vi != vars.end (); vi++)
//	{
//		program.cs_lookup_vi_for_typecasts (*vi, var_typecasts);
//		DEBUG ("\nFound %d types for var_decl=%d", var_typecasts.size (), *vi);
//	}
//	set<csvarinfo_t>::iterator vti;
//	// Get reaching from all typecasts
//	for (vti = var_typecasts.begin (); vti != var_typecasts.end (); vti++)
//	{
//		csvarinfo_t vt = *vti;
//		DEBUG ("\nget_reaching_vars(%s(%d))", vt->name, vt->id);
//		get_reaching_vars (vt->id, reaching_vars);
//	}
}

void unlabeled_edges::
get_reaching_vars (label var, 
	set<label> & reaching_vars)
{
	// If var has already been considered
	if (reaching_vars.find (var) != reaching_vars.end ())
		return;

	DEBUG ("\nget_reaching_vars(var=%d)", var);

	reaching_vars.insert (var);

	set<label> in_vars;
	if (in_edge_list.find (var) != in_edge_list.end ())
	{
		DEBUG ("\nin_edge_list of var=%d", var);
		in_vars = in_edge_list[var];
	}

	// Computing only those fields reaching src_var is difficult.
	// Over-approximately include all fields less than src_var->offset.
#if DEBUG_CONTAINER
	csvarinfo_t src_var = program.cs_get_varinfo (var);
	DEBUG ("\nget_field_var_ids(var=%s(%d))", src_var->name, var);
#endif
	program.get_prev_field_var_ids (var, in_vars);

	get_reaching_vars (in_vars, reaching_vars);
}

void unlabeled_edges::
get_points_to_pairs_statistics (map<label, set<label> > & points_to_pairs,
	unsigned int & tot_ptee_count,
	unsigned int & tot_local_ptee_count,
	unsigned int & tot_global_ptee_count,
	unsigned int & tot_heap_ptee_count,
	unsigned int & tot_ptr_count,
	unsigned int & tot_local_ptr_count,
	unsigned int & tot_global_ptr_count,
	unsigned int & tot_heap_ptr_count)

{
	map<label, set<label> >::iterator pi;
	for (pi = points_to_pairs.begin (); 
		pi != points_to_pairs.end (); 
		pi++)
	{
		set<label> dests = pi->second;
		dests.erase (undef_id);
		tot_ptee_count += dests.size ();
		tot_ptr_count++;

		label src = pi->first;
		csvarinfo_t src_var = program.cs_get_varinfo (src);
		if (!src_var || !src_var->decl)
			continue;
		if (program.global_var (src))
		{
			tot_global_ptee_count += dests.size ();
			tot_global_ptr_count++;
		}
		else if (program.heap_var (src))
		{
			tot_heap_ptee_count += dests.size ();
			tot_heap_ptr_count++;
		}
		else
		{
			tot_local_ptee_count += dests.size ();
			tot_local_ptr_count++;
		}
		
	}
}

void unlabeled_edges::
get_context_used_points_to_pairs_statistics (map<unsigned int, map<label, set<label> > > & context_used_points_to_pairs,
	float & avg_context_ptr_used_ptees,
	float & avg_context_local_ptr_used_ptees,
	float & avg_context_global_ptr_used_ptees,
	float & avg_context_heap_ptr_used_ptees)
{
	map<unsigned int, map<label, set<label> > >::iterator cpi;
	for (cpi = context_used_points_to_pairs.begin (); cpi != context_used_points_to_pairs.end (); cpi++)
	{
		unsigned int cid = cpi->first;
		unsigned int ptee_count = 0;
		unsigned int local_ptee_count = 0;
		unsigned int global_ptee_count = 0;
		unsigned int heap_ptee_count = 0;
		unsigned int ptr_count = 0;
		unsigned int local_ptr_count = 0;
		unsigned int global_ptr_count = 0;
		unsigned int heap_ptr_count = 0;

		get_points_to_pairs_statistics (context_used_points_to_pairs[cid],
			ptee_count,
			local_ptee_count,
			global_ptee_count,
			heap_ptee_count,
			ptr_count,
			local_ptr_count,
			global_ptr_count,
			heap_ptr_count);

		RESULT ("\nContext-id=%d, used unique, ptee, ptrs, unique=%d, local=%d, global=%d, heap=%d, unique=%d, local=%d, global=%d, heap=%d",
			cid, ptee_count, local_ptee_count, global_ptee_count, heap_ptee_count,
			ptr_count, local_ptr_count, global_ptr_count, heap_ptr_count);

		if (ptr_count)
			avg_context_ptr_used_ptees += ((float) ptee_count) / ptr_count;
		if (local_ptr_count)
			avg_context_local_ptr_used_ptees += ((float) local_ptee_count) / local_ptr_count;
		if (global_ptr_count)
			avg_context_global_ptr_used_ptees += ((float) global_ptee_count) / global_ptr_count;
		if (heap_ptr_count)
			avg_context_heap_ptr_used_ptees += ((float) heap_ptee_count) / heap_ptr_count;

		DEBUG ("\navg context ptr used ptees, used unique=%f, local=%f, global=%f, heap=%f",
			avg_context_ptr_used_ptees, avg_context_local_ptr_used_ptees, 
			avg_context_global_ptr_used_ptees, avg_context_heap_ptr_used_ptees);
	}

	unsigned int cids = context_used_points_to_pairs.size ();
	if (cids)
	{
		avg_context_ptr_used_ptees /= cids;
		avg_context_local_ptr_used_ptees /= cids;
		avg_context_global_ptr_used_ptees /= cids;
		avg_context_heap_ptr_used_ptees /= cids;
	}
	DEBUG ("\navg context ptr used ptees, used unique=%f, local=%f, global=%f, heap=%f",
		avg_context_ptr_used_ptees, avg_context_local_ptr_used_ptees, 
		avg_context_global_ptr_used_ptees, avg_context_heap_ptr_used_ptees);
}

void unlabeled_edges::
get_field_statistics (label var,
	unsigned int & field_count,
	set<label> & visited_nodes)
{
	if (visited_nodes.find (var) != visited_nodes.end ())
		return;

	visited_nodes.insert (var);

	map<label, set<label> > out_field_edges;
	program.get_all_typecasted_out_fields (var, out_field_edges);

	map<label, set<label> >::iterator ei;
	for (ei = out_field_edges.begin (); ei != out_field_edges.end (); ei++)
	{
		set<label> dests = ei->second;
		field_count += dests.size ();

		set<label>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
			get_field_statistics (*di, field_count, visited_nodes);
	}
}

void unlabeled_edges::
get_valid_graph_statistics (map<label, set<label> > & valid_points_to_pairs,
	unsigned int & count_explicit_valid_nodes,
	unsigned int & count_explicit_valid_edges,
	unsigned int & count_valid_nodes,
	unsigned int & count_valid_edges)
{
	set<label> valid_nodes;

	// Count explicitly saved nodes and edges

	map<label, set<label> >::iterator pi;
	for (pi = valid_points_to_pairs.begin (); pi != valid_points_to_pairs.end (); pi++)
	{
		label src = pi->first;
		valid_nodes.insert (src);

		set<label> dests = pi->second;
		valid_nodes.insert (dests.begin (), dests.end ());

		count_explicit_valid_edges += dests.size ();
		count_valid_edges += dests.size ();
	}

	count_explicit_valid_nodes += valid_nodes.size ();
	count_valid_nodes += valid_nodes.size ();
	DEBUG ("\nexplicitly saved valid nodes=%d", valid_nodes.size ());

	// Count implicitly saved field nodes and edges

	set<label> visited_nodes;

	set<label>::iterator ni;
	for (ni = valid_nodes.begin (); ni != valid_nodes.end (); ni++)
	{
		label v = *ni;
		unsigned int field_count = 0;
		get_field_statistics (v, field_count, visited_nodes);
		DEBUG ("\nvar=%d, field_count=%d", v, field_count);

		count_valid_nodes += field_count;
		count_valid_edges += field_count;
	}

}

void unlabeled_edges::
get_graph_statistics (map<label, set<label> > & points_to_pairs)
{
	// Copy all edges to program_points_to_pairs
	map<label, set<label> >::iterator pi;
	for (pi = out_edge_list.begin (); pi != out_edge_list.end (); pi++)
	{
		label src = pi->first;
		set<label> dests = pi->second;
		points_to_pairs[src].insert (dests.begin (), dests.end ());
	}
}

void unlabeled_edges::
get_graph_statistics (unsigned int & max_num_nodes,
	float & max_avg_out_edges,
	map<label, set<label> > & program_points_to_pairs,
	map<label, set<label> > & program_root_aliases,
	set<set<list<int> > > & program_aliases,
	map<label, set<label> > & program_reachable_roots,
	// map<label, set<list<label> > > & var_aliases,
	map<list<label>, set<list<label> > > & ap_alias_set,
	map<map<label, set<label> >, map<list<label>, set<list<label> > > > & memoized_points_to_alias,
	bool print)
{
#if UNDEF_LOCATION
	// Remove undef_id points-to pairs
	map<label, set<label> > refined_out_edges;
	map<label, set<label> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		set<label> s = ei->second;
		s.erase (undef_id);
		if (!s.size ())
			continue;
		refined_out_edges[ei->first] = s;
	}
#endif

#if 0
	// Node-edge information
	get_nodes_edges (max_num_nodes, max_avg_out_edges, print);
#endif

#if POINTS_TO
	// Points-to pair information
	if (print)
	{
		set<label> empty;
#if UNDEF_LOCATION
		print_points_to_pairs (refined_out_edges, empty);
#else
		print_points_to_pairs (out_edge_list, empty);
#endif
	}
	// Copy all edges from refined_out_edges to program_points_to_pairs
	map<label, set<label> >::iterator pi;
#if UNDEF_LOCATION
	for (pi = refined_out_edges.begin (); pi != refined_out_edges.end (); pi++)
#else
	for (pi = out_edge_list.begin (); pi != out_edge_list.end (); pi++)
#endif
	{
		label src = pi->first;
		set<label> dests = pi->second;
		program_points_to_pairs[src].insert (dests.begin (), dests.end ());
	}
#endif

//	get_access_paths (var_aliases);

#if ALIAS_STATISTICS_CONTAINER
#if UNDEF_LOCATION
//	if (memoized_points_to_alias.find (refined_out_edges) == memoized_points_to_alias.end ())
#else
//	if (memoized_points_to_alias.find (out_edge_list) == memoized_points_to_alias.end ())
#endif
	{
		get_ap_alias_set (ap_alias_set);
//		map<list<label>, set<list<label> > > ap_alias_set_curr;
//		get_ap_alias_set (ap_alias_set_curr);
#if UNDEF_LOCATION
//		memoized_points_to_alias[refined_out_edges] = ap_alias_set_curr;
#else
//		memoized_points_to_alias[out_edge_list] = ap_alias_set_curr;
#endif
//		merge_map (ap_alias_set_curr, ap_alias_set);
//		DEBUG ("\nMemoizing:");
		// print_memoized_value (memoized_points_to_alias);
	}
//	else
//	{
//		RESULT ("\nMemoizing helps!");
#if UNDEF_LOCATION
//		merge_map (memoized_points_to_alias[refined_out_edges], ap_alias_set);
#else
//		merge_map (memoized_points_to_alias[out_edge_list], ap_alias_set);
#endif
//	}

	DEBUG ("\ndone get_ap_alias_set() in get_graph_statistics()");
#endif

#if 0
	// Alias information

	set<set<list<int> > > set_of_aliases;
	get_aliases (set_of_aliases, program_aliases);
	if (print)
	{
		DEBUG ("\nOur graph:");
		print_aliases (set_of_aliases);
	}
	// DEBUG ("\nOur compact graph:");
	// unlabeled_edges * compact_g = get_compact_graph ();
	// compact_g->print_aliases (set_of_aliases, program_aliases);

	// Root alias information

	map<label, set<label> > root_aliases;
	get_root_aliases (root_aliases, program_root_aliases);
	if (print)
		print_root_aliases (root_aliases);

	// Compaction may introduce spurious root_aliases information. For
	// example, if {x=&y;z=&y;} else {x=&y;w=&y;} our graph =
	// {(x,n1)(y,n2)(y,n3)(z,n4)(w,n5)(n1,*,n2),(n1,*.n3)(n4,*,n2)(n5,*,n3)}.
	// Here w and z are not reachable from each other. However, after
	// compaction, i.e. after merging n2 and n3 which have the same name y,
	// we spuriously get that w and z are reachable.

	// map<label, set<label> > compact_root_aliases;
	// compact_g->print_root_aliases (compact_root_aliases);

	// Reachability

	map<label, set<label> > reachable_roots;
	get_reachable_roots (reachable_roots, program_reachable_roots);
	if (print)
		print_reachable_roots (reachable_roots);
#endif
}

void unlabeled_edges::
dump_data_flow_value (unsigned int funcid, unsigned int bbid, unsigned int bbio, 
	FILE * edge_file_ptr,
	FILE * heap_file_ptr,
	FILE * unique_edge_file_ptr,
	set<map<label, map<label, set<label> > > > & unique_points_to_graphs)
{
	// data flow value -- graph -- labeled edges
	map<label, map<label, set<label> > > dfg;

	// Print empty line to denote new context
	if (out_edge_list.size ())
	{
		fprintf (edge_file_ptr, "\n");
		fprintf (unique_edge_file_ptr, "\n");
	}

	set<label> vars;
	map<label, set<label> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		label src = ei->first;
               	csvarinfo_t sv_info = VEC_index (csvarinfo_t, program.variable_data, src);
		if (src == undef_id || !sv_info || !sv_info->decl)
			continue;
               	if (DECL_ARTIFICIAL (sv_info->decl))
			continue;
		if (program.heap_var (src))
			fprintf (heap_file_ptr, "%d ", src);
		vars.insert (src);
		set<label> s = ei->second;
		set<label>::iterator si;
		for (si = s.begin (); si != s.end (); si++)
		{
			label dest = *si;
               		csvarinfo_t dv_info = VEC_index (csvarinfo_t, program.variable_data, dest);
			if (dest == undef_id || !dv_info || !dv_info->decl)
				continue;
	               	if (DECL_ARTIFICIAL (dv_info->decl))
				continue;
			if (program.heap_var (dest))
				fprintf (heap_file_ptr, "%d ", dest);
			vars.insert (dest);

			fprintf (edge_file_ptr, "%d %d %d %d 0 %d\n", funcid, bbid, bbio, src, dest);

			dfg[src][0].insert (dest);
		}
	}

	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
	{
		label var = *vi;
		map<label, set<label> > out_field_edges;
		program.get_all_typecasted_out_fields (var, out_field_edges);
		map<label, set<label> >::iterator fi;
		for (fi = out_field_edges.begin (); fi != out_field_edges.end (); fi++)
		{
			label field = fi->first;
			set<label> dests = fi->second;

			set<label>::iterator di;
			for (di = dests.begin (); di != dests.end (); di++)
			{
				label dest = *di;
	               		csvarinfo_t dv_info = VEC_index (csvarinfo_t, program.variable_data, dest);
				if (dest == undef_id || !dv_info || !dv_info->decl)
					continue;
		               	if (DECL_ARTIFICIAL (dv_info->decl))
					continue;
				if (program.heap_var (dest))
					fprintf (heap_file_ptr, "%d ", dest);

				fprintf (edge_file_ptr, "%d %d %d %d %d %d\n", funcid, bbid, bbio, var, field, dest);

				dfg[var][field].insert (dest);
			}
		}
	}

	dump_unique_data_flow_value (dfg, unique_points_to_graphs, unique_edge_file_ptr);
}

void unlabeled_edges::
dump_unique_data_flow_value (map<label, map<label, set<label> > > & dfg, 
	set<map<label, map<label, set<label> > > > & unique_points_to_graphs,
	FILE * unique_edge_file_ptr)
{
	if (!dfg.size ())
		return;
	if (unique_points_to_graphs.find (dfg) != unique_points_to_graphs.end ())
		return;
	unique_points_to_graphs.insert (dfg);

	unsigned int uf = 1;	// arbitrary
	unsigned int ub = unique_points_to_graphs.size ();
	// denoting OUT program point, so that useful_alias_sets are not
	// computed by standalone script.
	unsigned int ui = 1;	

	map<label, map<label, set<label> > >::iterator ofl;
	for (ofl = dfg.begin (); ofl != dfg.end (); ofl++)
	{
		label src = ofl->first;
		map<label, set<label> > out_field_edge = ofl->second;
		map<label, set<label> >::iterator ofe;
		for (ofe = out_field_edge.begin (); ofe != out_field_edge.end (); ofe++)
		{
			label field = ofe->first;
			set<label> dests = ofe->second;
			set<label>::iterator di;
			for (di = dests.begin (); di != dests.end (); di++)
			{
				label dest = *di;
				fprintf (unique_edge_file_ptr, "%d %d %d %d %d %d\n", uf, ub, ui, src, field, dest);
			}
		}
	}
}

/** 
 * Find max length of the acyclic paths reaching VAR. An edge is added to
 * VISITED_*_EDGES every time for every new access path. This has become
 * possible because it is not passed as reference. 
 *
 * This function basically pushes the length of the AP of VAR to its
 * destination nodes by adding 1. It then recursively calls this function on
 * its destination nodes. This is done until every edge is covered exactly once
 * (visited_*_edges) along every access path.
 *
 * Note: We have considered visited_*_edges instead of visited_nodes because
 * the latter misses out counting back edges in an AP.
 */

unsigned int unlabeled_edges::
get_max_acyclic_ap_len (map<label, set<label> > & points_to_edges)
{
	map<label, unsigned int> max_acyclic_len;
	set<label> vars;
	map<label, set<label> >::iterator ei;
	for (ei = points_to_edges.begin (); ei != points_to_edges.end (); ei++)
	{
		label src = ei->first;
		vars.insert (src);
		set<label> dests = ei->second;
		vars.insert (dests.begin (), dests.end ());
	}

	set<label> visited_nodes;
	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
	{
		label var = *vi;

//		map<label, set<label> > visited_points_to_edges;
//		map<label, set<label> > visited_field_edges;
//		get_max_acyclic_ap_len (var, 1, points_to_edges, 
//			visited_points_to_edges, visited_field_edges, 
//			max_acyclic_len);

		get_max_acyclic_ap_len (var, points_to_edges, 
			visited_nodes, max_acyclic_len);
	}

	vars.erase (undef_id);
	
	DEBUG ("\nmax_acyclic_len=");
	map<label, unsigned int>::iterator ci;
	unsigned int count = 0;
	for (ci = max_acyclic_len.begin (); ci != max_acyclic_len.end (); ci++)
	{
		unsigned int new_count = ci->second;
#if DEBUG_CONTAINER
                csvarinfo_t vinfo = VEC_index (csvarinfo_t, program.variable_data, ci->first);
		DEBUG ("\n(var=%s(%d),%d)", vinfo->name, ci->first, new_count);
#endif
		if (count < new_count)
			count = new_count;
	}

	RESULT ("\nlocal_max_acyclic_len=%d", count);
	return count;
}

/** 
 * VISITED_POINTS_TO_EDGES: map from source var to set of pointees visited.
 * VISITED_FIELD_EDGES: map from source var to set of out-fields visited.
 * VAR_CURR_LEN: Each occurrence of VAR in different APs has a different
 * VAR_CURR_LEN (length of acyclic AP reaching in that AP). VAR_CURR_LEN should
 * match the sequence of activation records followed for the current AP;
 * otherwise, every new AP passing through VAR will add to the length computed
 * from an old AP passing through VAR.
 */

void unlabeled_edges::
get_max_acyclic_ap_len (label var, 
	unsigned int var_curr_len,
	map<label, set<label> > & points_to_edges,
	map<label, set<label> > visited_points_to_edges, 
	map<label, set<label> > visited_field_edges, 
	map<label, unsigned int> & max_acyclic_len)
{
	if (var == undef_id)
		return;

	unsigned int var_old_len = max_acyclic_len[var];
	if (var_old_len < var_curr_len)
	{
		max_acyclic_len[var] = var_curr_len;
		DEBUG ("\nvar=%d,old=%d,curr=%d,max=%d", var, var_old_len, var_curr_len, var_curr_len);
	}
	else
		DEBUG ("\nvar=%d,old=%d,curr=%d,max=%d", var, var_old_len, var_curr_len, var_old_len);

	set<label> field_vars;
	if (visited_field_edges.find (var) != visited_field_edges.end ())
		field_vars = visited_field_edges[var];

	map<label, set<label> > out_field_edges;
	program.get_all_typecasted_out_fields (var, out_field_edges);
	map<label, set<label> >::iterator fi;
	for (fi = out_field_edges.begin (); fi != out_field_edges.end (); fi++)
	{
		label field = fi->first;
		set<label> dests = fi->second;

		if (field_vars.find (field) != field_vars.end ())
			continue;

		map<label, set<label> > vis = visited_field_edges;
		vis[var].insert (field);

		set<label>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
		{
			label dest = *di;
			DEBUG ("\nsrc=%d->f=%d->dest=%d", var, field, dest);

			get_max_acyclic_ap_len (dest, var_curr_len + 1, points_to_edges, 
				visited_points_to_edges, vis, max_acyclic_len);
		}
	}

	set<label> pointees;
	if (visited_points_to_edges.find (var) != visited_points_to_edges.end ())
		pointees = visited_points_to_edges[var];

	map<label, set<label> >::iterator ei;
	set<label> dests = points_to_edges[var];
	set<label>::iterator di;
	DEBUG ("\nvar=%d->dests=", var);
	for (di = dests.begin (); di != dests.end (); di++)
		DEBUG ("%d,", *di);
	for (di = dests.begin (); di != dests.end (); di++)
	{
		label dest = *di;

		if (pointees.find (dest) != pointees.end ())
			continue;

		map<label, set<label> > vis = visited_points_to_edges;
		vis[var].insert (dest);

		DEBUG ("\nsrc=%d->dest=%d", var, dest);

		get_max_acyclic_ap_len (dest, var_curr_len + 1, points_to_edges, 
			vis, visited_field_edges, max_acyclic_len);
	}
}

/** 
 * Using VISITED_NODES (passed as reference). This is actual depth first algo. 
 *
 * This function collects the height of each node (i.e. the number of
 * dereferences that succeed each node up till the leaf). The height may not be
 * the max possible height of the graph. This is because we use DFS (i.e. do
 * not revisit an already visited node) on our non-regular gPT graph (that
 * where the nodes in a loop have multiple in-edges). Therefore, effectively
 * some random back edges/cycles get removed to form one of the many possible
 * spanning trees that can be constructed out of the graph. This spanning tree
 * may not have the longest path possible from the graph. Therefore, the height
 * calculated is not the maximum possible. Note that a regular graph has only
 * one possible spanning tree but our graphs are non-regular.
 *
 * HEIGHT[] is needed so that if a node is revisited, its previously computed
 * height can be recalled.
 * Cycles in DAG have a problem that if a successor is already visited but its
 * height is not yet computed, then current incompletely computed height gets
 * used. A height of a node would not yet have been computed if the node is in
 * a cycle. 
 */

void unlabeled_edges::
get_max_acyclic_ap_len (label var, 
	map<label, set<label> > & points_to_edges,
	set<label> & visited_nodes, 
	map<label, unsigned int> & height)
{
	if (var == undef_id)
		return;

        if (visited_nodes.find (var) != visited_nodes.end ())
                return;

        DEBUG ("\nget_max_acyclic_ap_len(var=%d)", var);

        visited_nodes.insert (var);
        height[var] = 1;

        unsigned int var_old_height = height[var];

	map<label, set<label> > out_field_edges;
	program.get_all_typecasted_out_fields (var, out_field_edges);
	map<label, set<label> >::iterator fi;
	for (fi = out_field_edges.begin (); fi != out_field_edges.end (); fi++)
	{
		label field = fi->first;
		set<label> dests = fi->second;

		set<label>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
		{
			label dest = *di;
			DEBUG ("\nsrc=%d->f=%d->dest=%d", var, field, dest);

			get_max_acyclic_ap_len (dest, points_to_edges, visited_nodes, height);
	
			if (var_old_height < height[dest] + 1)
			{
				height[var] = height[dest] + 1;
				var_old_height = height[var];
			        DEBUG ("\nheight[var=%d]=%d, height[dest=%d]=%d",
                	 	       var, height[var], dest, height[dest]);
			}
		}
	}

	map<label, set<label> >::iterator ei;
	set<label> dests = points_to_edges[var];
	set<label>::iterator di;
	DEBUG ("\nvar=%d->dests=", var);
	for (di = dests.begin (); di != dests.end (); di++)
	        if (visited_nodes.find (*di) == visited_nodes.end ())
			DEBUG ("%d,", *di);
	for (di = dests.begin (); di != dests.end (); di++)
	{
		label dest = *di;

		DEBUG ("\nsrc=%d->dest=%d", var, dest);

		get_max_acyclic_ap_len (dest, points_to_edges, visited_nodes, height);

		if (var_old_height < height[dest] + 1)
		{
			height[var] = height[dest] + 1;
			var_old_height = height[var];
		        DEBUG ("\nheight[var=%d]=%d, height[dest=%d]=%d",
                 	       var, height[var], dest, height[dest]);
		}
	}
}

void unlabeled_edges::
get_access_paths (map<label, set<list<label> > > & var_aps,
	bool is_k)
{
	DEBUG ("\nget_access_paths(var_aps,is_k=%d)", is_k);
	set<label> vars;
	map<label, set<label> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		label src = ei->first;
                csvarinfo_t vinfo = VEC_index (csvarinfo_t, program.variable_data, src);
                if (vinfo && vinfo->decl && !DECL_ARTIFICIAL (vinfo->decl))
			vars.insert (src);

		set<label> dests = ei->second;
		set<label>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
		{
			label dest = *di;
                	vinfo = VEC_index (csvarinfo_t, program.variable_data, dest);
	                if (vinfo && vinfo->decl && !DECL_ARTIFICIAL (vinfo->decl))
				vars.insert (dest);
		}

		// vars.insert (dests.begin (), dests.end ());
	}

	set<label>::iterator vi;
	for (vi = vars.begin (); vi != vars.end (); vi++)
	{
		label var = *vi;
		set<label> visited_nodes;

		if (is_k)
			get_k_access_paths (var, var_aps);
		else
		{
			// ?? Needto use TEMP_VAR_APS: Since APs of each
			// sequence of activation records is governed by a new
			// set of VISITED_NODES, their APs should also be new.
			// Therefore, APs computed from old sequence of
			// activation records is not passed to a new sequence
			// of activation records.

			map<label, set<list<label> > > temp_var_aps;
			get_acyclic_access_paths (var, visited_nodes, temp_var_aps);
			map<label, set<list<label> > >::iterator mi;
			for(mi = temp_var_aps.begin (); mi != temp_var_aps.end (); mi++)
			{
				set<list<label> > aps = mi->second;
				var_aps[mi->first].insert (aps.begin (), aps.end ());
			}			
		}
	}
	DEBUG ("\ndone get_access_paths(var_aps,is_k=%d)", is_k);
}

/** 
 * This function basically pushes the access paths of VAR to its destination
 * nodes by appending the out-edge field to the access paths of VAR. It then
 * recursively calls this function on its destination nodes. This is done upto
 * k length of every access path.
 */

void unlabeled_edges::
get_k_access_paths (label var, 
	map<label, set<list<label> > > & var_aps)
{
	csvarinfo_t vinfo = VEC_index (csvarinfo_t, program.variable_data, var);
	if (vinfo && vinfo->decl && DECL_ARTIFICIAL (vinfo->decl))
		return;	

	DEBUG ("\nget_k_access_paths(var=%d, var_aps)", var);
	list<label> base_ap;
	base_ap.push_back (var);
	if (is_ap_valid_alias (base_ap))
		var_aps[var].insert (base_ap);
#if DEBUG_CONTAINER
	else
	{
                csvarinfo_t vinfo = VEC_index (csvarinfo_t, program.variable_data, var);
		DEBUG ("\nInvalid ap for alias=%s(%d)", vinfo->name, var);
	}
#endif

	map<label, set<label> > out_field_edges;
	program.get_all_typecasted_out_fields (var, out_field_edges);
	map<label, set<label> >::iterator fi;
	for (fi = out_field_edges.begin (); fi != out_field_edges.end (); fi++)
	{
		label field = fi->first;
		set<label> dests = fi->second;

		set<label>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
		{
			label dest = *di;

			DEBUG ("\nsrc=%d->f=%d->dest=%d", var, field, dest);
			// Push access paths of dest to its successors only if the
			// access paths of dest change.
			if (append_k_access_paths (var, field, dest, var_aps))
				get_k_access_paths (dest, var_aps);
		}
	}

	map<label, set<label> >::iterator ei;
	set<label> dests;
	if (out_edge_list.find (var) != out_edge_list.end ())
		dests = out_edge_list[var];
	set<label>::iterator di;
	for (di = dests.begin (); di != dests.end (); di++)
	{
		label dest = *di;
		// Push access paths of dest to its successors only if the
		// access paths of dest change.
		if (append_k_access_paths (var, ASTERISK, dest, var_aps))
			get_k_access_paths (dest, var_aps);
	}
	DEBUG ("\ndone get_k_access_paths(var=%d, var_aps[var].size=%d)", 
		var, var_aps[var].size ());
}

bool unlabeled_edges::
append_k_access_paths (label src,
	label field,
	label dest,
	map<label, set<list<label> > > & var_aps)
{
	DEBUG ("\nappend_k_access_paths: src=%d, field=%d, dest=%d", src, field, dest);
	bool has_changed = false;

	set<list<label> > src_aps = var_aps[src];
	set<list<label> >::iterator api;
	for (api = src_aps.begin (); api != src_aps.end (); api++)
	{
		list<label> ap = *api;

		append_ap_field (ap, field);

		// When following was not used, ALLOC_BASED, L=1,
		// hmmer took 356 seconds vs. 10 hours (earlier).
		if (*(--ap.end ()) == wild_card_id)
			continue;

		if (var_aps[dest].find (ap) != var_aps[dest].end ())
			continue;

		if (!is_ap_valid_alias (ap))
			continue;

		var_aps[dest].insert (ap);
		has_changed = true;		

		#if DEBUG_CONTAINER
		DEBUG ("\nsrc=%d, dest=%d, ap=", src, dest);
		print_access_path (ap);
		#endif
	}

	DEBUG ("\ndone append_k_access_paths: src=%d, field=%d, dest=%d", src, field, dest);
	return has_changed;
}

void unlabeled_edges::
append_ap_field (list<label> & ap, label field)
{
	DEBUG ("\nappend_ap_field, field=%d", field);

	label last = *(--ap.end ());
	if (last == wild_card_id)
	{
		DEBUG ("\ndone append_ap_field, field=%d", field);
		return;
	}

	// Since AP already has within MAX_LEN_PRINT number of pointers,
	// appending a non-pointer field will still retain that property.
//	if (field)
//	{
//		ap.push_back (field);
//		DEBUG ("\ndone append_ap_field, field=%d", field);
//		return;
//	}

	unsigned int ap_len = ap.size ();
//	unsigned int ap_len = 0;
//	list<label>::iterator li;
//	for (li = ap.begin (); li != ap.end (); li++)
//	{
//		label l = *li;
//		if (!l)
//			ap_len++;
//	}

	if (ap_len == MAX_LEN_PRINT)
		ap.push_back (wild_card_id);
	else if (ap_len < MAX_LEN_PRINT)
		ap.push_back (field);
        else if (ap_len > MAX_LEN_PRINT)
        {
                // label last = *(--ap.end ());
                // if (last != wild_card_id)
                {
                        // RESULT ("\nError: ap size is greater than %d", MAX_LEN_PRINT);
                        RESULT ("\nError: ap has more than %d pointer fields", MAX_LEN_PRINT);
                        print_access_path (ap);
                }
        }
	DEBUG ("\ndone append_ap_field, field=%d", field);
}

void unlabeled_edges::
collect_aps (map<label, set<list<label> > > & var_aps,
	set<list<label> > & all_aps)
{
	map<label, set<list<label> > >::iterator vapi;
	for (vapi = var_aps.begin (); vapi != var_aps.end (); vapi++)
	{
		set<list<label> > aps = vapi->second;
		all_aps.insert (aps.begin (), aps.end ());
	}
}

/** 
 * Following get_/append_ functions are to compute all possible APS to compare
 * with deterministic_/non_deterministic_graph live APs.
 */

void unlabeled_edges::
get_access_paths (set<list<label> > & aps,
	struct cgraph_node * cnode)
{
#if INFO_CONTAINER
	print_value (NULL);
#endif

	set<label> vars;
	map<label, set<list<label> > > sent_var_aps;
	map<label, set<list<label> > > new_var_aps;

	map<label, set<label> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		label var = ei->first;
                csvarinfo_t vinfo = VEC_index (csvarinfo_t, program.variable_data, var);
                if (!vinfo || !vinfo->decl || vinfo->is_heap_var)
			continue;
		if (cnode && !program.is_in_scope (var, cnode))
			continue;

		set<label> visited_nodes;

		list<label> base_ap;
		set<list<label> > empty_aps;
		empty_aps.insert (base_ap);

		DEBUG ("\nSTART var=%d", var);
		push_k_access_paths (empty_aps, var, var, sent_var_aps, new_var_aps);
	}

	if (new_var_aps.size ())
		RESULT ("\nError: incremental liveness not reached fixpoint");
	collect_aps (sent_var_aps, aps);
}

/** 
 * This function basically pushes the access paths of VAR to its destination
 * nodes by appending the out-edge field to the access paths of VAR. It then
 * recursively calls this function on its destination nodes. This is done upto
 * k length of every access path.
 */

void unlabeled_edges::
get_k_access_paths (label var, 
	map<label, set<list<label> > > & sent_var_aps,
	map<label, set<list<label> > > & new_var_aps)
{
	DEBUG ("\nget_k_access_paths(var=%d, sent_var_aps, new_var_aps)", var);
	set<list<label> > new_src_aps = new_var_aps[var];
	sent_var_aps[var].insert (new_src_aps.begin (), new_src_aps.end ());
	new_var_aps.erase (var);
	
	push_k_access_paths (new_src_aps, var, ASTERISK, sent_var_aps, new_var_aps);

	map<label, set<label> > out_field_edges;
	program.get_all_typecasted_out_fields (var, out_field_edges);

	map<label, set<label> >::iterator fi;
	for (fi = out_field_edges.begin (); fi != out_field_edges.end (); fi++)
	{
		label field = fi->first;
		set<label> dests = fi->second;

		set<label>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
		{
			label dest = *di;

			DEBUG ("\nsrc=%d->f=%d->dest=%d", var, field, dest);

			push_k_access_paths (new_src_aps, dest, field, sent_var_aps, new_var_aps);
		}
	}
	new_src_aps.clear ();
}

void unlabeled_edges::
push_k_access_paths (set<list<label> > & src_aps,
	label src_field,
	label in_field,
	map<label, set<list<label> > > & sent_var_aps,
	map<label, set<list<label> > > & new_var_aps)
{
	DEBUG ("\nappend field, var=%d, in_field=%d", src_field, in_field);
	if (out_edge_list.find (src_field) == out_edge_list.end ())
		return;
	set<label> changed_aps;
	set<label> * dests = &out_edge_list[src_field];
	set<label>::iterator di;
	for (di = dests->begin (); di != dests->end (); di++)
	{
		label dest = *di;
		// Push access paths of dest to its successors only if the
		// access paths of dest change.
		if (append_k_access_paths (src_aps, in_field, dest, sent_var_aps, new_var_aps))
			changed_aps.insert (dest);
	}

	// Breadth first
	set<label>::iterator ca;
	for (ca = changed_aps.begin (); ca != changed_aps.end (); ca++)
	{
		label var = *ca;
		get_k_access_paths (var, sent_var_aps, new_var_aps);
	}
	DEBUG ("\ndone get_k_access_paths(var=%d, src_aps.size=%d)", 
		src_field, src_aps.size ());
}

bool unlabeled_edges::
append_k_access_paths (set<list<label> > & src_aps,
	label field,
	label dest,
	map<label, set<list<label> > > & sent_var_aps,
	map<label, set<list<label> > > & new_var_aps)
{
	DEBUG ("\nappend to dest: src, field=%d, dest=%d", field, dest);
	bool has_changed = false;

	set<list<label> >::iterator api;
	for (api = src_aps.begin (); api != src_aps.end (); api++)
	{
		list<label> ap = *api;

		unsigned int ap_len = ap.size ();

		if (ap_len < MAX_LEN_PRINT)
			ap.push_back (field);
		else
			continue;

		if (sent_var_aps[dest].find (ap) != sent_var_aps[dest].end ())
			continue;
		if (new_var_aps[dest].find (ap) != new_var_aps[dest].end ())
			continue;

		new_var_aps[dest].insert (ap);
		has_changed = true;		

		#if DEBUG_CONTAINER
		DEBUG ("\nfield=%d, dest=%d, ap=", field, dest);
		print_access_path (ap);
		#endif
	}

	DEBUG ("\ndone append_k_access_paths: src, field=%d, dest=%d", field, dest);
	return has_changed;
}

/** 
 * Find APs due to VAR. A node is added to VISITED_NODES every time for
 * every new access path. This has become possible because it is not passed as
 * reference. 
 * This function basically pushes the access paths of VAR to its destination
 * nodes by appending the out-edge field to the access paths of VAR. It then
 * recursively calls this function on its destination nodes. This is done until
 * every destination node is covered exactly once (visited_nodes) along every
 * access path.
 */

void unlabeled_edges::
get_acyclic_access_paths (label var, 
	set<label> visited_nodes, 
	map<label, set<list<label> > > & var_aps)
{
	if (visited_nodes.find (var) != visited_nodes.end ())
		return;
	visited_nodes.insert (var);

	list<label> base_ap;
	base_ap.push_back (var);
	var_aps[var].insert (base_ap);

	map<label, set<label> > out_field_edges;
	program.get_all_typecasted_out_fields (var, out_field_edges);
	map<label, set<label> >::iterator fi;
	for (fi = out_field_edges.begin (); fi != out_field_edges.end (); fi++)
	{
		label field = fi->first;
		set<label> dests = fi->second;
		set<label>::iterator di;
		for (di = dests.begin (); di != dests.end (); di++)
		{
			label dest = *di;
			DEBUG ("\nsrc=%d->f=%d->dest=%d", var, field, dest);
			append_acyclic_access_paths (var, field, dest, var_aps);
			get_acyclic_access_paths (dest, visited_nodes, var_aps);
		}
	}

	map<label, set<label> >::iterator ei;
	set<label> dests;
	if (out_edge_list.find (var) != out_edge_list.end ())
		dests = out_edge_list[var];
	set<label>::iterator di;
	for (di = dests.begin (); di != dests.end (); di++)
	{
		label dest = *di;
		append_acyclic_access_paths (var, ASTERISK, dest, var_aps);
		get_acyclic_access_paths (dest, visited_nodes, var_aps);
	}
}

void unlabeled_edges::
append_acyclic_access_paths (label src,
	label field,
	label dest,
	map<label, set<list<label> > > & var_aps)
{
	set<list<label> > src_aps = var_aps[src];
	set<list<label> >::iterator api;
	for (api = src_aps.begin (); api != src_aps.end (); api++)
	{
		list<label> ap = *api;
		ap.push_back (field);
		var_aps[dest].insert (ap);
#if DEBUG_CONTAINER
		DEBUG ("\nsrc=%d, dest=%d, ap=", src, dest);
		print_access_path (ap);
#endif
	}
}

void unlabeled_edges::
get_non_temp_ap_alias_set (map<list<label>, set<list<label> > > & ap_alias_set,
        map<list<label>, set<list<label> > > & ap_alias_set_non_temp)
{
        map<list<label>, set<list<label> > >::iterator pi;
        for (pi = ap_alias_set.begin (); pi != ap_alias_set.end (); pi++)
        {
		list<label> ap = pi->first;
                label v = *(ap.begin ());
                csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, v);
                if (DECL_ARTIFICIAL (v_info->decl))
			continue;

		set<list<label> > aps = pi->second;
		set<list<label> >::iterator apsi;
		for (apsi = aps.begin (); apsi != aps.end (); apsi++)
		{
			list<label> sp = *apsi;
                	label sv = *(sp.begin ());
                	csvarinfo_t sv_info = VEC_index (csvarinfo_t, program.variable_data, sv);
                	if (DECL_ARTIFICIAL (sv_info->decl))
				continue;
			ap_alias_set_non_temp[ap].insert (sp);
		}
        }
}

void unlabeled_edges::
get_non_temp_ap_alias_set (map<list<label>, list<list<label> > > & ap_alias_set,
        map<list<label>, list<list<label> > > & ap_alias_set_non_temp)
{
        map<list<label>, list<list<label> > >::iterator pi;
        for (pi = ap_alias_set.begin (); pi != ap_alias_set.end (); pi++)
        {
		list<label> ap = pi->first;
                label v = *(ap.begin ());
                csvarinfo_t v_info = VEC_index (csvarinfo_t, program.variable_data, v);
                if (DECL_ARTIFICIAL (v_info->decl))
			continue;

		list<list<label> > aps = pi->second;
		list<list<label> >::iterator apsi;
		for (apsi = aps.begin (); apsi != aps.end (); apsi++)
		{
			list<label> sp = *apsi;
                	label sv = *(sp.begin ());
                	csvarinfo_t sv_info = VEC_index (csvarinfo_t, program.variable_data, sv);
                	if (DECL_ARTIFICIAL (sv_info->decl))
				continue;
			ap_alias_set_non_temp[ap].push_back (sp);
		}
        }
}

void unlabeled_edges::
get_ap_alias_set (map<list<label>, set<list<label> > > & ap_alias_set)
{
	DEBUG ("\nget_ap_alias_set()");

	map<label, set<list<label> > > var_aps;
	bool is_k = true;
	get_access_paths (var_aps, is_k);

	DEBUG ("\ndone get_access_paths()");

#if DEBUG_CONTAINER
	map<label, set<list<label> > >::iterator mi;
	for (mi = var_aps.begin (); mi != var_aps.end (); mi++)
	{
		DEBUG ("\n%d=", mi->first);
		set<list<label> > s = mi->second;
		set<list<label> >::iterator si;
		for (si = s.begin (); si != s.end (); si++)
		{
			DEBUG ("(");
			list<label> ap = *si;
			print_access_path (ap);		
			DEBUG (")");
		}
	}
#endif

	map<label, set<list<label> > >::iterator pi;
	for (pi = var_aps.begin (); pi != var_aps.end (); pi++)
	{
		if (pi->first == undef_id)
			continue;

		set<list<label> > aps = pi->second;

		// Computing ap_alias_set

		set<list<label> >::iterator api;
		for (api = aps.begin (); api != aps.end (); api++)
		{
			list<label> ap = *api;
			merge_set (aps, ap_alias_set[ap]);
		}		

#if 0
		//  Computing ap_pairs

		set<list<label> >::iterator api1;
		for (api1 = aps.begin (); api1 != aps.end (); api1++)
		{
			list<label> ap1 = *api1;

			set<list<label> >::iterator api2;
			for (api2 = api1; api2 != aps.end (); api2++)
			{
				if (api1 == api2)
					continue;

				list<label> ap2 = *api2;

				get_ap_pair (ap1, ap2, ap_pairs);
			}
		}
#endif
	}
	DEBUG ("\ndone get_ap_alias_set()");
}

bool unlabeled_edges::
is_useful_path (list<label> & ap,
	set<list<label> > & useful_paths)
{
	list<label> ap1 = ap;
	// ap1.remove (wild_card_id);
	return useful_paths.find (ap1) != useful_paths.end ();
}

bool unlabeled_edges::
is_ap_valid_alias (list<label> & ap1)
{	
	label l1;

	// Ignore if heap path
	l1 = *(ap1.begin ());
	if (program.heap_var (l1))
		return false;

	// Ignore if var followed by field edge, eg x->32. This alias pair will
	// get captured with x.32+32 var.
	label l1_next = 0;
	if (l1 && ap1.size () > 1)
	{
		l1_next = *(++ap1.begin ());
		DEBUG ("\nl1=%d, l1_next=%d", l1, l1_next);
		if (l1_next) return false; 
	}
	return true;
}

void unlabeled_edges::
get_ap_pair (list<label> & ap1, list<label> & ap2,
	set<pair<list<label>, list<label> > > & ap_pairs)
{
	DEBUG ("\nget_ap_pair()");
/*
	// I think the following should not be applied.  Two APs with same
	// frontier fields could be node aliases -- these should not be
	// ignored.
#if SUMM_K_PREFIX == 0 || SUMM_K_CONSISTENT == 0
	// The last field edge may be a wild card in case of SUMM_K_PREFIX.
	// Therefore, the following does not hold for SUMM_K_PREFIX.

	// If ap1 and ap2 have same addresses due to field edges of structure,
	// then do not consider them as aliases. They are aliased by points-to
	// edges only if at least one of them has ASTERISK as the last label.
	l1 = *(ap1.rbegin ());
	l2 = *(ap2.rbegin ());
	DEBUG ("\nl1=%d, l2=%d", l1, l2);
	if (l1 != ASTERISK && l2 != ASTERISK)
	{
		if (ap1.size () == 1)
			return false;
		if (ap2.size () == 1)
			return false;
		if (l1 != l2)
		{
			RESULT ("\nError: Link alias should have same frontier fields");
			RESULT ("\n\t!!(");
			print_access_path (ap1);
			RESULT (",");
			print_access_path (ap2);
			RESULT (")");
		}
		return false;
	}
#endif
*/

#if SUMMARIZE_ALIASED_PATHS
#else
	if (*(--ap1.end ()) == wild_card_id)
		return;
	if (*(--ap2.end ()) == wild_card_id)
		return;
#endif

	if (ap1 < ap2)
		ap_pairs.insert (make_pair (ap1, ap2));
	else
		ap_pairs.insert (make_pair (ap2, ap1));

	DEBUG ("\ndone get_ap_pair()");
}

void unlabeled_edges::
print_ap_alias_set (map<list<label>, list<list<label> > > & ap_alias_set)
{
	map<list<label>, list<list<label> > >::iterator psi;
	for (psi = ap_alias_set.begin (); psi != ap_alias_set.end (); psi++)
	{
		list<label> ap = psi->first;
		RESULT ("\n\t\t");
		print_access_path (ap);
		RESULT (" -> ");

		list<list<label> > apss = psi->second;
		list<list<label> >::iterator apsi;
		for (apsi = apss.begin (); apsi != apss.end (); apsi++)
		{
			list<label> aps = *apsi;
			print_access_path (aps);
			RESULT (",");
		}
	}
}

void unlabeled_edges::
print_ap_alias_set  (map<list<label>, set<list<label> > > & ap_alias_set)
{
	map<list<label>, set<list<label> > >::iterator psi;
	for (psi = ap_alias_set.begin (); psi != ap_alias_set.end (); psi++)
	{
		list<label> ap = psi->first;
		RESULT ("\n\t\t");
		print_access_path (ap);
		RESULT (" -> ");

		set<list<label> > apss = psi->second;
		set<list<label> >::iterator apsi;
		for (apsi = apss.begin (); apsi != apss.end (); apsi++)
		{
			list<label> aps = *apsi;
			print_access_path (aps);
			RESULT (",");
		}
	}
}

void unlabeled_edges::
print_access_paths (map<label, set<list<label> > > & var_aps)
{
	map<label, set<list<label> > >::iterator vapi;
	for (vapi = var_aps.begin (); vapi != var_aps.end (); vapi++)
	{
		if (vapi->first == undef_id)
			continue;
		set<list<label> > aps = vapi->second;
		if (aps.size () <= 1)
			continue;
		DEBUG ("\n\t%d=", vapi->first);
		RESULT ("\n\t\t{");
		print_access_paths (aps);
		RESULT ("}");
	}
}

void unlabeled_edges::
print_access_paths (set<list<label> > & aps)
{
	set<list<label> >::iterator api;
	for (api = aps.begin (); api != aps.end (); api++)
	{
		list<label> ap = *api;
		print_access_path (ap);
		RESULT (",");
	}
}

void unlabeled_edges::
print_access_path (list<label> & ap)
{
	list<label>::iterator li;
	for (li = ap.begin (); li != ap.end (); li++)
	{
		label l = *li;
		if (l == ASTERISK)
		{
			RESULT ("0.");
		}
		else if (li == ap.begin ())
		{
			csvarinfo_t var = program.cs_get_varinfo (l);
			if (var)
			{
				RESULT ("%s(%d).", var->name, l);
			}
			else
			{
				RESULT ("!%d.", l);
			}
		}
#if SUMM_K_PREFIX || SUMM_K_CONSISTENT
                else if (l == wild_card_id)
		{
                        RESULT ("+.");
		}
#endif
		else
		{
			RESULT ("%d.", l);
		}
	}
}

unsigned int unlabeled_edges::
compare_memoized_value (map<label, set<label> > & out_edges,
	map<map<label, set<label> >, set<pair<list<label>, list<label> > > > & memoized_points_to_alias)
{
	set<label> empty;
	DEBUG ("\ncompare_memoized_value");
	print_points_to_pairs (out_edges, empty);
	map<map<label, set<label> >, set<pair<list<label>, list<label> > > >::iterator vi;
	for (vi = memoized_points_to_alias.begin (); vi != memoized_points_to_alias.end (); vi++)
	{
		DEBUG ("\nNext=");
		map<label, set<label> > memoized_out_edges = vi->first;
		print_points_to_pairs (memoized_out_edges, empty);
		if (out_edges == memoized_out_edges)
		{
			DEBUG ("\nMatch");
		}
		else
		{
			DEBUG ("\nDont match");
		}
	}

}

unsigned int unlabeled_edges::
print_memoized_value (map<map<label, set<label> >, set<pair<list<label>, list<label> > > > & memoized_points_to_alias)
{
	DEBUG ("\nMemoized_points_to_alias:");
	map<map<label, set<label> >, set<pair<list<label>, list<label> > > >::iterator vi;
	for (vi = memoized_points_to_alias.begin (); vi != memoized_points_to_alias.end (); vi++)
	{
		DEBUG ("\nNext=");
		DEBUG ("\n");
		map<label, set<label> > out_edges = vi->first;
		map<label, set<label> >::iterator ei;
		for (ei = out_edges.begin (); ei != out_edges.end (); ei++)
		{	
			DEBUG ("%d->", ei->first);
			set<label> s = ei->second;
			set<label>::iterator si;
			for (si = s.begin (); si != s.end (); si++)
				DEBUG ("%d,", *si);
		}
	}
}

void unlabeled_edges::
print_points_to_pairs (label ptr, map<label, set<label> > & points_to_pairs)
{
	if (points_to_pairs.find (ptr) == points_to_pairs.end ())
		return;
		
	csvarinfo_t ptr_info = VEC_index (csvarinfo_t, program.variable_data, ptr);
	set<label> ptes = points_to_pairs[ptr];
	set<label>::iterator pi;
	for (pi = ptes.begin (); pi != ptes.end (); pi++)
	{
		label pte = *pi;
		if (pte == undef_id)
			continue;
		csvarinfo_t pte_info = VEC_index (csvarinfo_t, program.variable_data, pte);
		if (ptr_info->is_global_var)
		{
			RESULT ("\n\t\t# %s(%d) -> ", ptr_info->name, ptr);
		}
		else
		{
			RESULT ("\n\t\t%s(%d) -> ", ptr_info->name, ptr);
		}

		if (pte_info->is_global_var)
		{
			RESULT ("# %s(%d)", pte_info->name, pte);
		}
		else
		{
			RESULT ("%s(%d)", pte_info->name, pte);
		}
	}
}

void unlabeled_edges::
print_points_to_pairs (map<label, set<label> > & points_to_pairs)
{
	DEBUG ("\nunlabeled_edges::print_points_to_pairs ()");
	unsigned int heap_to_stack_pointers = 0;
	map<label, set<label> >::iterator ei;
	for (ei = points_to_pairs.begin (); ei != points_to_pairs.end (); ei++)
	{
		label ptr = ei->first;
		print_points_to_pairs (ptr, points_to_pairs);
	}
}

void unlabeled_edges::
get_used_points_to_pairs (map<label, set<label> > & points_to_pairs,
	basic_block bb,
	map<label, set<label> > & used_points_to_pairs)
{
	set<label> used_pointers = program.get_used_pointers (bb, points_to_pairs);
	set<label>::iterator pi;
	for (pi = used_pointers.begin (); pi != used_pointers.end (); pi++)
	{
		label ptr = *pi;
		if (points_to_pairs.find (ptr) == points_to_pairs.end ())
			continue;
		
		set<label> ptes = points_to_pairs[ptr];
		used_points_to_pairs[ptr].insert (ptes.begin (), ptes.end ());
	}
}

void unlabeled_edges::
print_used_points_to_pairs (map<label, set<label> > & points_to_pairs,
	basic_block bb)
{
	set<label> used_pointers = program.get_used_pointers (bb, points_to_pairs);
	set<label>::iterator pi;
	for (pi = used_pointers.begin (); pi != used_pointers.end (); pi++)
	{
		label ptr = *pi;
		print_points_to_pairs (ptr, points_to_pairs);
	}
}

unsigned int unlabeled_edges::
print_points_to_pairs (map<label, set<label> > & points_to_pairs, set<label> & heap_to_stack_pointees)
{
	DEBUG ("\nunlabeled_edges::print_points_to_pairs ()");
	unsigned int heap_to_stack_pointers = 0;
	map<label, set<label> >::iterator ei;
	for (ei = points_to_pairs.begin (); ei != points_to_pairs.end (); ei++)
	{
		label ptr = ei->first;
		set<label> ptes = ei->second;
		set<label>::iterator pi;
		for (pi = ptes.begin (); pi != ptes.end (); pi++)
		{
			label pte = *pi;
			if (pte == undef_id)
				continue;
			csvarinfo_t ptr_info = VEC_index (csvarinfo_t, program.variable_data, ptr);
			csvarinfo_t pte_info = VEC_index (csvarinfo_t, program.variable_data, pte);

#if SUMM_K_CONSISTENT
			if (program.heap_var (ptr) && program.is_stack_pointer (pte_info))
			{
				RESULT ("\n\t\t!!!%s(%d) -> %s(%d)", ptr_info->name, ptr, pte_info->name, pte);
				heap_to_stack_pointees.insert (pte);
				heap_to_stack_pointers++;
			}
			else
#endif
			{
				RESULT ("\n\t\t%s(%d) -> %s(%d)", ptr_info->name, ptr, pte_info->name, pte);
			}
		}
	}
	return heap_to_stack_pointers;
}

void unlabeled_edges::
print_value (FILE * file)
{
	DEBUG ("\nunlabeled_edges::print_graph (%x), ref_count=%d", this, reference_count);
	map<label, set<label> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		label ptr = ei->first;
		set<label> ptes = ei->second;
		set<label>::iterator pi;
		for (pi = ptes.begin (); pi != ptes.end (); pi++)
		{
			label pte = *pi;
			if (pte == undef_id)
				continue;
			csvarinfo_t ptr_info = VEC_index (csvarinfo_t, program.variable_data, ptr);
			csvarinfo_t pte_info = VEC_index (csvarinfo_t, program.variable_data, pte);
			RESULT ("\n\t%s(%d) -> %s(%d)", ptr_info->name, ptr, pte_info->name, pte);
//			RESULT ("\n%d -> %d", ptr, pte);
		}
	}
}


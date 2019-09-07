
/*******************************************************************************
  * This code has been extracted from tree-ssa-structalias.c of GCC. It was 
  * refactored by Prashant Singh Rawat. It was further improved by Prachi Yogi,
  * Sudakshina Das, Swati Rathi, Avantika Gupta, Pritam Gharat, and of course
  * me (Vini) ;-)
*******************************************************************************/


#include "parser.hh"

// Whether or not to split blocks containing pointer dereferences
#define SPLIT_DEREF 0

// Split if liveness_analysis_deterministic/non_deterministic since we need pta
// at IN of deref statement. 
#define SPLIT_LHS_ONLY_DEREF 	1	

// Split call block to create AUX_BLOCK (empty block before call block) if
// liveness_analysis_deterministic/non_deterministic
#define SPLIT_CALL_INTO_AUX 	1	

// Supratik sir needs points-to information at each block. So we keep only one
// statement per block and print points-to information at IN of each block.
#define SPLIT_ALL (0 || RHS_POINTEES_STATS)

// Perform name based merging if the program point is a loop join
#define LOOP_MERGE_OPTIMIZATION 0

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

#if HEAP_TYPE_BASED_NAME
unsigned int parser::
heap_type_count = 0;
#endif

parser::
parser ()
{
	main_cnode = NULL;
	multi_rhs = false;
	compute_only_pinfo = false;
	compute_alias_and_pinfo = false;
	all_contexts_together = true;
	check_deref = false;
	deref_stmt = false;
	count_malloc_calls = 0;
}

void parser::
map_arguments_at_call (gimple stmt, tree decl, bool generate_liveness, basic_block bb, struct cgraph_node * cnode)
{
   DEBUG ("\nmap_arguments_at_call");

   VEC(ce_s, heap) *rhsc = NULL;
   size_t j;
   int argoffset = 1;
   csvarinfo_t fi;

   /* Generate liveness for call via function pointers and library routines. */
   if (generate_liveness) {
       DEBUG ("\nGenerate liveness for function pointers and library routines");

       struct constraint_expr *exp;
       unsigned i;

       for (j = 0; j < gimple_call_num_args (stmt); j++) {
	   DEBUG ("\nMapping argument %d", j);
           tree arg = gimple_call_arg (stmt, j);
           if (field_must_have_pointers (arg) && TREE_CODE (arg) != ADDR_EXPR) {
	       DEBUG ("\nfield_must_have_pointers");
               VEC (ce_s, heap) *results = NULL;
               cs_get_constraint_for (arg, &results, bb, cnode);
               FOR_EACH_VEC_ELT (ce_s, results, i, exp)
	       {
		   DEBUG ("\nGenerating liveness of variable %d", exp->var);	
                   ((block_information *)(bb->aux))->add_to_parsed_data_indices (exp->var, false, bb);	// generate_liveness_constraints // Vini: Why commented out???
	       }
               VEC_free (ce_s, heap, results);
           }
       }
       return;
   }

   /* Map call arguments. */
   fi = cs_get_vi_for_tree (decl, bb, cnode);

   for (j = 0; j < gimple_call_num_args (stmt); j++) {
       struct constraint_expr lhs ;
       struct constraint_expr *rhsp;
       tree arg = gimple_call_arg (stmt, j);
       if (field_must_have_pointers (arg)) {
           cs_get_constraint_for (arg, &rhsc, bb, cnode);
           lhs.type = SCALAR;
           lhs.var = cs_first_vi_for_offset (fi, argoffset)->id;
           lhs.offset = 0;
           while (VEC_length (ce_s, rhsc) != 0) {
               rhsp = VEC_last (ce_s, rhsc);
		DEBUG ("\nmapped arguments:");
   		DEBUG ("\nlhs var %d, type %d", lhs.var, lhs.type);
		DEBUG ("\nrhs var %d, type %d", rhsp->var, rhsp->type);
              cs_process_constraint (new_constraint (lhs, *rhsp), bb);
               VEC_pop (ce_s, rhsc);
               multi_rhs = true;
           }
          multi_rhs = false;
       }
       argoffset++;
   }
   VEC_free (ce_s, heap, rhsc);

   DEBUG ("\nDone map_arguments_at_call");
}

// Added by Vini

void parser::
map_function_pointer_arguments (struct cgraph_node * src_function, basic_block call_site, struct cgraph_node * called_function)
{
   DEBUG ("\nmap_function_pointer_arguments()");
   DEBUG ("\nsrc_function=%s", cgraph_node_name (src_function));
   DEBUG ("\ncalled_function=%s", cgraph_node_name (called_function));
   DEBUG ("\n");
   // FIXME: check that this call_site has only one statement.
   gimple_stmt_iterator gsi = gsi_start_bb (call_site);
   gimple stmt = gsi_stmt (gsi);

   VEC(ce_s, heap) *rhsc = NULL;
   size_t j;
   int argoffset = 1;
   csvarinfo_t fi;

   // Count number of parameters
   unsigned int num = 0;
   for (tree t = DECL_ARGUMENTS (called_function->decl); t; t = DECL_CHAIN (t))
        ++num;
   // Check the number of parameters and arguments. If they are different, then
   // do not perform any mapping. 
   if (num != gimple_call_num_args (stmt))
   {
	DEBUG ("\nMapping of src_function and called_function is wrong.");
        VEC_free (ce_s, heap, rhsc);
	return;
   }

   fi = cs_get_vi_for_tree (called_function->decl, call_site, src_function);

#if DEBUG_CONTAINER
   DEBUG ("\nFunction call: ");
   print_gimple_stmt (dump_file, stmt, 0, 0);
#endif

   for (j = 0; j < gimple_call_num_args (stmt); j++) {
       DEBUG ("\narg=%d", j);
       struct constraint_expr lhs ;
       struct constraint_expr *rhsp;
       tree arg = gimple_call_arg (stmt, j);
       if (field_must_have_pointers (arg)) {
           DEBUG ("\narg has pointers");
           cs_get_constraint_for (arg, &rhsc, call_site, src_function);
           lhs.type = SCALAR;
           csvarinfo_t param = cs_first_vi_for_offset (fi, argoffset);
	   // Due to wrong function pointer's callee, the number of arguments
	   // may not be equal to number of parameters. Return of this is the
	   // case.
	   if (!param)
           {
                VEC_free (ce_s, heap, rhsc);
		return;
           }
           lhs.var = param->id;
           lhs.offset = 0;
	   DEBUG ("\nmapped arguments:");
   	   DEBUG ("\nlhs var %d, type %d", lhs.var, lhs.type);
           while (VEC_length (ce_s, rhsc) != 0) {
               rhsp = VEC_last (ce_s, rhsc);
		DEBUG ("\nrhs var %d, type %d", rhsp->var, rhsp->type);
	       cs_process_constraint (new_constraint (lhs, *rhsp), call_site);
               VEC_pop (ce_s, rhsc);
               multi_rhs = true;
           }
          multi_rhs = false;
       }
       argoffset++;
   }
   VEC_free (ce_s, heap, rhsc);

   DEBUG ("\nDone map_arguments_at_call");
}

/*-------------------------------------------------------------------------------------
  A call statement can return a value. This mapping has to be performed (after the call
  has been made) at the return block. 
  ------------------------------------------------------------------------------------*/
void parser::
map_return_value (basic_block call_block, struct cgraph_node * src_function, basic_block end_block, struct cgraph_node * called_function)
{
   DEBUG ("\nmap_return_value");
   bool found_rhs = true;
   /* Is there a receiving pointer value in the call statement? */
   gimple call_stmt = bb_call_stmt (call_block);
#if DEBUG_CONTAINER
   DEBUG ("\nCall sttmt: ");
   print_gimple_stmt (dump_file, call_stmt, 0, 0);
#endif
   if (is_gimple_call (call_stmt)) 
   {
      tree lhsop = gimple_call_lhs (call_stmt);
      if (lhsop && field_must_have_pointers (lhsop)) 
      {
         DEBUG ("\nlhs is pointer");
         found_rhs = false;
         gimple_stmt_iterator ret_gsi;
         for (ret_gsi = gsi_start_bb (end_block); !gsi_end_p (ret_gsi); gsi_next (&ret_gsi)) 
         {
            gimple ret_stmt = gsi_stmt (ret_gsi);
#if DEBUG_CONTAINER
            DEBUG ("\nreturn stmt: ");
            print_gimple_stmt (dump_file, ret_stmt, 0, 0);
#endif
            if (gimple_code (ret_stmt) == GIMPLE_RETURN)
            {
               tree rhsop = gimple_return_retval (ret_stmt);
	       if (rhsop != NULL_TREE)
               {
                  /* Map it to the return value of return statement. */
                  VEC(ce_s, heap) *lhsc = NULL, *rhsc = NULL;
	          if (rhsop && AGGREGATE_TYPE_P (TREE_TYPE (lhsop)))  /* Look into : Structure variables */
	          {
	        	DEBUG ("\naggregate_type_p");
	                cs_get_constraint_for (lhsop, &lhsc, call_block, src_function);
	                cs_get_constraint_for (rhsop, &rhsc, end_block, called_function);
			cs_do_structure_copy (lhsop, lhsc, rhsop, rhsc, call_block); 
			// Do not free. sjeng gives error.
	                 // VEC_free (ce_s, heap, lhsc);
		         // VEC_free (ce_s, heap, rhsc);
	          }
	          else 
	          {
			DEBUG ("\nnot aggregate_type_p");
	                cs_get_constraint_for (lhsop, &lhsc, call_block, src_function);
	                cs_get_constraint_for (rhsop, &rhsc, end_block, called_function);
	                cs_process_all_all_constraints (lhsc, rhsc, call_block);

	                  VEC_free (ce_s, heap, lhsc);
		          VEC_free (ce_s, heap, rhsc);
	          }

		  found_rhs = true;
		  // END_BLOCK can have only one return var. If found, exit.
                  break;
               }
	    }
         }
      }
   }
   // This may not be an error because a function pointer may be pointing to a
   // wrong (over-approximate) called_function
   if (!found_rhs)
	DEBUG ("\ncall-statement expects return, but return-block not found");
}

csvarinfo_t parser::
get_received_var (basic_block call_block, struct cgraph_node * src_function)
{
	gimple call_stmt = bb_call_stmt (call_block);
	if (is_gimple_call (call_stmt)) 
	{
		tree lhsop = gimple_call_lhs (call_stmt);
		if (lhsop && field_must_have_pointers (lhsop)) 
		{
			VEC(ce_s, heap) *lhsc = NULL;
			cs_get_constraint_for (lhsop, &lhsc, call_block, src_function);
			struct constraint_expr *lhsp;
			unsigned int i;

			FOR_EACH_VEC_ELT (ce_s, lhsc, i, lhsp) 
			{ 
				return cs_get_varinfo (lhsp->var);
			}
                        VEC_free (ce_s, heap, lhsc);
		}
	}

	return NULL;
}

csvarinfo_t parser::
get_return_var (basic_block return_block, struct cgraph_node * called_function)
{
         gimple_stmt_iterator ret_gsi;
         for (ret_gsi = gsi_start_bb (return_block); !gsi_end_p (ret_gsi); gsi_next (&ret_gsi)) 
         {
            gimple ret_stmt = gsi_stmt (ret_gsi);
#if DEBUG_CONTAINER
            DEBUG ("\nreturn stmt: ");
            print_gimple_stmt (dump_file, ret_stmt, 0, 0);
#endif
            if (gimple_code (ret_stmt) == GIMPLE_RETURN)
            {
               tree rhsop = gimple_return_retval (ret_stmt);
	       if (rhsop != NULL_TREE)
               {
                  /* Map it to the return value of return statement. */
                  VEC(ce_s, heap) *rhsc = NULL;
                  cs_get_constraint_for (rhsop, &rhsc, return_block, called_function);

		  struct constraint_expr *rhsp;
		  unsigned int j;

		  FOR_EACH_VEC_ELT (ce_s, rhsc, j, rhsp) 
		  { 
		        // END_BLOCK can have only one return var. If found, exit.
			return cs_get_varinfo (rhsp->var);
		  }
                  VEC_free (ce_s, heap, rhsc);
               }
	    }
         }
	return NULL;
}

set<unsigned int> parser::
get_return_vars (struct cgraph_node * called_function)
{
	set<unsigned int> ret_vars;
        basic_block end_block = get_end_block_of_function (called_function);
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
                csvarinfo_t ret_var = get_return_var (return_block, called_function);
                if (ret_var && ret_var->decl && TREE_TYPE (ret_var->decl) && 
			TREE_CODE (TREE_TYPE (ret_var->decl)) == POINTER_TYPE)
                {
                        DEBUG ("\nRET=%s(%d)", ret_var->name, ret_var->id);
                        ret_vars.insert (ret_var->id);
                }
        }
	return ret_vars;
}

void parser::
process_library_call (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
   if (gimple_call_flags (stmt) & ECF_NORETURN)
   {
	((block_information *)(bb->aux))->set_block_type (NORETURN_BLOCK); 
	#if DEBUG_CONTAINER
	print_gimple_stmt (dump_file, stmt, 0, 0);
	#endif
	RESULT ("\nNORETURN");
	return;
   }

   DEBUG ("\nin process lib");
   /* Generate liveness. */
   map_arguments_at_call (stmt, NULL, true, bb, cnode);
   /* Handle malloc by introducing a points to to heap. */
   if (gimple_call_flags (stmt) & ECF_MALLOC) {
       tree lhs = gimple_call_lhs (stmt);
       if (lhs && field_must_have_pointers (lhs))
       {
           csvarinfo_t heap_info = cs_make_constraint_from_heapvar (lhs, "heap", bb, cnode);
           save_heap_location (stmt, heap_info->id);
	   count_malloc_calls++;
       }
   }
}

gimple parser::
bb_call_stmt (basic_block bb)
{
   gimple_stmt_iterator gsi;
   gimple stmt;
   for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi)) {
      stmt = gsi_stmt (gsi);
      if (is_gimple_call (stmt))
         return stmt;
   }
   return NULL;
}

/*-------------------------------------------------
	FUNCTIONS FROM tree-ssa-structalias.c
---------------------------------------------------*/

/* Return the position, in bits, of FIELD_DECL from the beginning of its
   structure.  */

HOST_WIDE_INT parser::
bitpos_of_field (const tree fdecl)
{
  if (!host_integerp (DECL_FIELD_OFFSET (fdecl), 0)
      || !host_integerp (DECL_FIELD_BIT_OFFSET (fdecl), 0))
    return -1;

  return (TREE_INT_CST_LOW (DECL_FIELD_OFFSET (fdecl)) * BITS_PER_UNIT
          + TREE_INT_CST_LOW (DECL_FIELD_BIT_OFFSET (fdecl)));
}


/* Create a new constraint consisting of LHS and RHS expressions.  */

constraint_t parser::
new_constraint (const struct constraint_expr lhs,
                const struct constraint_expr rhs)
{
  DEBUG ("\n(constraint_t) pool_alloc (constraint_pool)");
  constraint_t ret = (constraint_t) pool_alloc (constraint_pool);
  ret->lhs = lhs;
  ret->rhs = rhs;
  ret->previous_phi = NULL;
  return ret;
}

/* Return true if two constraint expressions A and B are equal.  */

bool parser::
constraint_expr_equal (struct constraint_expr a, struct constraint_expr b)
{
  return a.type == b.type && a.var == b.var && a.offset == b.offset;
}

/* Return true if two constraints A and B are equal.  */

bool parser::
constraint_equal (struct constraint a, struct constraint b)
{
  return constraint_expr_equal (a.lhs, b.lhs)
    && constraint_expr_equal (a.rhs, b.rhs);
}

/* Return a printable name for DECL  */

const char * parser::
alias_get_name (tree decl)
{
  const char *res;
  char *temp;
  int num_printed = 0;

  if (DECL_ASSEMBLER_NAME_SET_P (decl))
    res = IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (decl));
  else
    res= get_name (decl);
  if (res != NULL)
    return res;

  res = "NULL";
  if (!dump_file)
    return res;

  if (TREE_CODE (decl) == SSA_NAME)
    {
      num_printed = asprintf (&temp, "%s_%u",
                              alias_get_name (SSA_NAME_VAR (decl)),
                              SSA_NAME_VERSION (decl));
    }
  else if (DECL_P (decl))
    {
      num_printed = asprintf (&temp, "D.%u", DECL_UID (decl));
    }
  if (num_printed > 0)
    {
      res = ggc_strdup (temp);
      free (temp);
    }
  return res;
}

/* Return true if V is a tree that we can have subvars for.
   Normally, this is any aggregate type.  Also complex
   types which are not gimple registers can have subvars.  */

inline bool parser::
var_can_have_subvars (const_tree v)
{
  /* Volatile variables should never have subvars.  */
  if (TREE_THIS_VOLATILE (v))
  {
    DEBUG ("\ntree_this_volatile");
    return false;
  }

  /* Non decls or memory tags can never have subvars.  */
  if (!DECL_P (v))
  {
    DEBUG ("\n!decl_p");
    return false;
  }

  /* Aggregates without overlapping fields can have subvars.  */
  if (TREE_CODE (TREE_TYPE (v)) == RECORD_TYPE)
  {
    DEBUG ("\nrecord_type");
    return true;
  }

  // FIXME: MEM_REF (for example, *x) can also have subvars

  DEBUG ("\nvar cannot have subvars");
  return false;
}

bool parser::
is_stack_pointer (csvarinfo_t & v)
{
	if (!v)
		return false;
	if (!v->decl)
		return false;
	if (heap_var (v->id))
		return false;
	if (TREE_CODE (v->decl) == FUNCTION_DECL)
		return false;
	if (TREE_CODE (v->decl) == VAR_DECL || TREE_CODE (TREE_TYPE (v->decl)) == ARRAY_TYPE)
		return false;
	return true;
}

/* Return true if T is a type that does contain pointers.  */

bool parser::
type_must_have_pointers (tree t)
{
  if (POINTER_TYPE_P (t))
  {
    DEBUG ("\npointer_type_p");
    return true;
  }

  if (TREE_CODE (t) == ARRAY_TYPE)
  {
    DEBUG ("\narray_type");
    return type_must_have_pointers (TREE_TYPE (t));
  }

  /* A function or method can have pointers as arguments, so track
     those separately.  */
  if (TREE_CODE (t) == FUNCTION_TYPE
      || TREE_CODE (t) == METHOD_TYPE)
  {
    DEBUG ("\nfunction_type or method_type");
    return true;
  }

  // FIXME: Swati: This check is to consider x=y, x=*y, *x=y type of structure
  // assignment statements.
  if (RECORD_OR_UNION_TYPE_P (t))
  {
    DEBUG ("\nrecord_or_union_type_p");
    return true; 
  }

  // FIXME: To deal with *x=y, x=*y statements, where lhs and/or rhs is not an
  // address.
  //if (TREE_CODE (t) == MEM_REF)
  //{
  //  DEBUG ("\nmem_ref");
  //  return true;
  //}

  DEBUG ("\ntype does not have pointers");

  return false;
}

bool parser::
field_must_have_pointers (tree t)
{
  DEBUG ("\nfield_must_have_pointers");
  return type_must_have_pointers (TREE_TYPE (t));
}

void check (VEC(fieldoff_s,heap) *fieldstack )
{
       if (VEC_length (fieldoff_s, fieldstack) <= 1
          || VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE) {
	  DEBUG ("\n4** will be executed");
       }
       else
   	  DEBUG ("\n4** will NOT be executed");
}

/** 
 * Given index of POINTER_RECORD (pointer to a variable), this function returns
 * a vector of field offsets of the variable pointed by POINTER_RECORD.
 */

VEC (fieldoff_s, heap) * parser:: 
get_fieldstack (unsigned int pointer_record) 
{ 
        csvarinfo_t var = VEC_index (csvarinfo_t, variable_data, pointer_record); 
        // Extract record from pointer_record 
        tree type; 
        if (var && var->decl && TREE_TYPE (var->decl)) 
	{
                type = TREE_TYPE (var->decl); 
#if DEBUG_CONTAINER
		DEBUG ("\n============\n");
		print_node_brief (dump_file, "", var->decl, 0);
		DEBUG ("\n------------\n");
		print_node (dump_file, "", type, 0);
		DEBUG ("\n============\n");
#endif
	}
 
        VEC (fieldoff_s, heap) * fieldstack = NULL; 
        push_fields_onto_fieldstack (type, &fieldstack, 0); 
        DEBUG ("\nNumber of fields: %d", VEC_length (fieldoff_s, fieldstack)); 
  
        fieldoff_s * fo = NULL; 
        unsigned int j; 
        DEBUG ("\nOffsets: "); 
        for (j = 0; VEC_iterate (fieldoff_s, fieldstack, j, fo); j++) 
        { 
                //if (fo->has_unknown_size || fo->offset < 0)  
                        DEBUG ("%s(%lld), ", fo->offset); 
        } 
 
        return fieldstack; 
}


/* Given a TYPE, and a vector of field offsets FIELDSTACK, push all
   the fields of TYPE onto fieldstack, recording their offsets along
   the way.

   OFFSET is used to keep track of the offset in this entire
   structure, rather than just the immediately containing structure.
   Returns false if the caller is supposed to handle the field we
   recursed for.  */

bool parser::
push_fields_onto_fieldstack (tree type, VEC(fieldoff_s,heap) **fieldstack, HOST_WIDE_INT offset)
{
  DEBUG ("\npush_fields_onto_fieldstack");
  DEBUG ("\nVEC_length (fieldoff_s, *fieldstack)=%d", VEC_length (fieldoff_s, *fieldstack)); 
  unsigned int i = 0;
  fieldoff_s *fo = NULL;
  FOR_EACH_VEC_ELT (fieldoff_s, *fieldstack, i, fo)
  {
	DEBUG ("%lld,", fo->offset);
  }

  tree field;
  bool empty_p = true;

  if (TREE_CODE (type) != RECORD_TYPE)
    return false;

  DEBUG ("\npush_fields 1--");

  /* If the vector of fields is growing too big, bail out early.
     Callers check for VEC_length <= MAX_FIELDS_FOR_FIELD_SENSITIVE, make
     sure this fails.  */
  // FIXME: Vini: We have not handled the case when a structure has more than
  // MAX_FIELDS_FOR_FIELD_SENSITIVE number of fields, i.e. we do not perform
  // safe field insensitive analysis in this case. It would be better to
  // terminate in such a case, or not put such a restriction at all.
  // -fplugin=./plugin.so -O3 works
  // -fplugin=./plugin.so -O0 does not work
  if (VEC_length (fieldoff_s, *fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE)
  {
    RESULT ("\nError: field insensitive");
    return false;
  }

  DEBUG ("\npush_fields 2--");

  // FIXME: Vini: Create a list of field dereferences in this loop

  for (field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
    if (TREE_CODE (field) == FIELD_DECL)
      {
        DEBUG ("\npush_fields 3--");
	DEBUG ("\nField %s in loop", get_name (field));
        bool push = false;
        HOST_WIDE_INT foff = bitpos_of_field (field);
        DEBUG ("\nfoff=%d", foff);

        if (!var_can_have_subvars (field)
            || TREE_CODE (TREE_TYPE (field)) == QUAL_UNION_TYPE
            || TREE_CODE (TREE_TYPE (field)) == UNION_TYPE)
 	{
	  DEBUG ("\n!var_can_have_subvars");
          push = true;
	}
        else if (!push_fields_onto_fieldstack
                    (TREE_TYPE (field), fieldstack, offset + foff)
                 && (DECL_SIZE (field)
                     && !integer_zerop (DECL_SIZE (field))))
	{
          /* Empty structures may have actual size, like in C++.  So
             see if we didn't push any subfields and the size is
             nonzero, push the field onto the stack.  */
  	  DEBUG ("\npush_fields 4--");
	  check (*fieldstack);
          push = true;
	}
	DEBUG ("\nField %s has push=%d", get_name (field), push);

        if (push)
          {
            DEBUG ("\npush_fields 5--");
	    DEBUG ("\nField %s to be pushed", get_name (field));
            fieldoff_s *pair = NULL;
            bool has_unknown_size = false;
            bool must_have_pointers_p;

	    DEBUG ("\nVEC_empty (fieldoff_s, *fieldstack)=%d, VEC_length (fieldoff_s, *fieldstack)=%d", 
		VEC_empty (fieldoff_s, *fieldstack), VEC_length (fieldoff_s, *fieldstack)); 
            if (!VEC_empty (fieldoff_s, *fieldstack))
	    {
              DEBUG ("\npush_fields 6--");
	      DEBUG ("\nField %s 6--", get_name (field));
	      check (*fieldstack);
              pair = VEC_last (fieldoff_s, *fieldstack);
            }

	    DEBUG ("\noffset=%lld, foff=%lld", offset, foff);
            /* If there isn't anything at offset zero, create sth.  */
            if (!pair
                && offset + foff != 0)
              {
  		DEBUG ("\npush_fields 7--");
	        DEBUG ("\nField %s 7--", get_name (field));
		DEBUG ("\nbefore VEC_length (fieldoff_s, *fieldstack)=%d", VEC_length (fieldoff_s, *fieldstack)); 
                pair = VEC_safe_push (fieldoff_s, heap, *fieldstack, NULL);
                pair->offset = 0;
                pair->size = offset + foff;
                pair->has_unknown_size = false;
                pair->must_have_pointers = false;
                pair->may_have_pointers = false;
                pair->only_restrict_pointers = false;
		DEBUG ("\nafter VEC_length (fieldoff_s, *fieldstack)=%d", VEC_length (fieldoff_s, *fieldstack)); 
		DEBUG ("\npair->offset=%lld", pair->offset);
		DEBUG ("\n7-- pushed fields:");
		unsigned int i = 0;
		fieldoff_s *fo = NULL;
		FOR_EACH_VEC_ELT (fieldoff_s, *fieldstack, i, fo)
		{
			DEBUG ("%lld,", fo->offset);
		}

              }
            if (!DECL_SIZE (field)
                || !host_integerp (DECL_SIZE (field), 1))
	    {
     	      DEBUG ("\npush_fields 8--");
	      DEBUG ("\nField %s 8--", get_name (field));
              has_unknown_size = true;
            }
#if DEBUG_CONTAINER
            else 
	    {
	      DEBUG ("\npush_fields 9--");
	      DEBUG ("\nField %s 9--", get_name (field));
            }
#endif
	    check (*fieldstack);

            /* If adjacent fields do not contain pointers merge them.  */
            must_have_pointers_p = field_must_have_pointers (field);
            if (pair
                && !has_unknown_size
                && !must_have_pointers_p
                && !pair->must_have_pointers
                && !pair->has_unknown_size
                && pair->offset + (HOST_WIDE_INT)pair->size == offset + foff)
              {
  		DEBUG ("\npush_fields 10--");
	        DEBUG ("\nField %s 10--", get_name (field));
                pair->size += TREE_INT_CST_LOW (DECL_SIZE (field));
              }
            else
              {
  		DEBUG ("\npush_fields 11--");
	        DEBUG ("\nField %s 11--", get_name (field));
		DEBUG ("\nbefore VEC_length (fieldoff_s, *fieldstack)=%d", VEC_length (fieldoff_s, *fieldstack)); 
	        check (*fieldstack);
                pair = VEC_safe_push (fieldoff_s, heap, *fieldstack, NULL);	// PROBLEM: fieldstack not working
	        check (*fieldstack);
                pair->offset = offset + foff;
                pair->has_unknown_size = has_unknown_size;
                if (!has_unknown_size)
                  pair->size = TREE_INT_CST_LOW (DECL_SIZE (field));
                else
                  pair->size = -1;
                pair->must_have_pointers = must_have_pointers_p;
                pair->may_have_pointers = true;
                pair->only_restrict_pointers
                  = (!has_unknown_size
                     && POINTER_TYPE_P (TREE_TYPE (field))
                     && TYPE_RESTRICT (TREE_TYPE (field)));
		DEBUG ("\nafter VEC_length (fieldoff_s, *fieldstack)=%d", VEC_length (fieldoff_s, *fieldstack)); 
		DEBUG ("\npair->offset=%lld", pair->offset);
		DEBUG ("\n11-- pushed fields:");
		unsigned int i = 0;
		fieldoff_s *fo = NULL;
		FOR_EACH_VEC_ELT (fieldoff_s, *fieldstack, i, fo)
		{
			DEBUG ("i=%d,%lld,", i, fo->offset);
		}
              }
	      // Added by Vini
              pair->field_decl = field;
	      DEBUG ("\npush_fields 12--");
	      DEBUG ("\nField %s 12--", get_name (field));
	      check (*fieldstack);
          }

	DEBUG ("\npush_fields 13--");
	DEBUG ("\nField %s 13--", get_name (field));
	check (*fieldstack);
        empty_p = false;
      }

  return !empty_p;
}

tree parser::
get_decl (csvarinfo_t var)
{
	tree root_decl = var->decl;
	HOST_WIDE_INT var_offset = var->offset;

	DEBUG ("\nget_decl (%s, %lld)", var->name, var_offset);
	// DEBUG ("\nroot: ");
	// print_node (dump_file, 0, root_decl, 0);

	return get_decl_recursively (root_decl, 0, var_offset);
}

/** 
 * Given VAR tree and VAR_OFFSET, which is its offset position from its
 * outermost structure, this function returns the tree declaration which is at
 * SEARCH_OFFSET position from its outermost structure.
 */

tree parser::
get_decl_recursively (tree var_decl, HOST_WIDE_INT var_offset, HOST_WIDE_INT search_offset)
{
	if (var_offset == search_offset)
	{
		DEBUG ("\nFound=%lld", search_offset);
		// print_node (dump_file, 0, var_decl, 0);
		return var_decl;
	}

	if (!TREE_TYPE (var_decl) || !RECORD_OR_UNION_TYPE_P (TREE_TYPE (var_decl)))
		return NULL;

	for (tree field = TYPE_FIELDS (TREE_TYPE (var_decl)); field; field = TREE_CHAIN (field))
	{
		if (TREE_CODE (field) == FIELD_DECL)
		{
			HOST_WIDE_INT field_offset = bitpos_of_field (field);
			DEBUG ("\nfield %s, field_offset=%lld, var+field offset=%lld", 
				get_name (field), field_offset, var_offset + field_offset);
			tree ret = get_decl_recursively (field, var_offset + field_offset, search_offset);
			if (ret)
				return ret;
		}
	}
	return NULL;
}

/** 
 * This function returns field variables inside structure VAR->decl.  Note that
 * var could be a heap variable that has been typecasted to var->decl. Old
 * typecasts are not considered.
 * It returns recursively nested fields. If MERGED_NON_POINTER_FIELDS=1, then
 * fields exist only in the root node i.e., the recursively nested fields are
 * already flattened out in the root node and we need not traverse the root
 * recursively.
 */

void parser::
get_reachable_fields (csvarinfo_t var, set<unsigned int> & reachable_fields)
{
	DEBUG ("\nget_reachable_fields (%s)", var->name);
	// DEBUG ("\nroot: ");
	// print_node (dump_file, 0, root, 0);

        if (!var)
		return;
        if (!var->decl)
		return;
	DEBUG ("\nvar_decl found");

        // Return if variable has no fields.
        if (!var->offset && !var->next)
		return;
        // Return if variable is function. (NEXT field of function csvarinfo_t
        // is connected to its function parameter).
        if (function_var (var))
		return;
        // Return if variable is function parameter. (OFFSET field of parameter
        // csvarinfo_t is set to the position of the parameter with respect to
        // other parameters).
        if (parameter_var (var))
		return;


	DEBUG ("\nvar_decl=%s(%d)", var->name, var->id);
	tree var_decl = get_decl (var);
	csvarinfo_t root = cs_lookup_vi_for_tree (var->decl);
	if (root)
	{
		// ROOT: id root (stack/heap) of the field var. Note that
		// tree of root of fields is different from root in case of stack??
		// But tree root of all fields is same as root in case of heap.
		// VAR_DECL: field tree of var
		// VAR->offset: field offset of var from ROOT
#if MERGE_NON_POINTER_FIELDS
		// If non-pointer fields are merged, then only root (i.e. with
		// offset=0) will have subfields, no other (pointer) field will
		// have subfields. Therefore, no need to traverse recursively.
		if (!var->offset)
		{
			for (csvarinfo_t start = root; start; start = start->next)
			{
				DEBUG ("\nsrc=%s(%d), field=%s(%d), may_have_pointers=%d", root->name, root->id,
					start->name, start->id, start->may_have_pointers);
				// DEBUG ("\n-----------");
				// print_node (dump_file, 0, start->field_decl, 0);
				// DEBUG ("\n-----------");
#if IGNORE_NON_POINTER_FIELDS
				if (start->field_decl && TREE_TYPE (start->field_decl)
					&& TREE_CODE (TREE_TYPE (start->field_decl)) == POINTER_TYPE) 
#endif
					reachable_fields.insert (start->id);
			}
		}
#else
		get_reachable_fields_recursively (root, var_decl, var->offset, reachable_fields);
#endif
	}
}

/** 
 * Given a structure VAR_DECL at address VAR_OFFSET from ROOT, this function
 * finds member fields that are nested inside this structure. Note that
 * the member fields of the non-pointer first field of every structure are
 * considered as nested.
 */

void parser::
get_reachable_fields_recursively (csvarinfo_t root, tree var_decl, HOST_WIDE_INT var_offset, set<unsigned int> & reachable_fields)
{
	DEBUG ("\nget_reachable_fields_recursively (root=%s(%d), root_offset=%lld, var_offset=%lld, may_have_pointers=%d)", 
		root->name, root->id, root->offset, var_offset, root->may_have_pointers);
	if (!TREE_TYPE (var_decl) || !RECORD_OR_UNION_TYPE_P (TREE_TYPE (var_decl)))
		return;

	for (tree field = TYPE_FIELDS (TREE_TYPE (var_decl)); field; field = TREE_CHAIN (field))
	{
		if (TREE_CODE (field) == FIELD_DECL)
		{
			HOST_WIDE_INT field_offset = bitpos_of_field (field);
			DEBUG ("\n%s, offset=%lld", get_name (var_decl), field_offset);
			csvarinfo_t field_var = 
				cs_first_vi_for_offset (root, var_offset + field_offset);
			if (!field_var)
			{
				RESULT ("\nError: cs_first_vi_for_offset (%s(%d), offset=%lld+%lld) not found",
					root->name, root->id, var_offset, field_offset);
				continue;
			}
			DEBUG ("\nfield %s, field_offset=%lld, root+field offset=%lld -- var=%s(%d, may_have_pointers=%d)", 
				get_name (field), field_offset, var_offset + field_offset, 
				field_var->name, field_var->id, field_var->may_have_pointers);
			// DEBUG ("\n-----------");
			// print_node (dump_file, 0, field, 0);
			// DEBUG ("\n-----------");

			reachable_fields.insert (field_var->id);

			// If FIELD is the first field of the structure at
			// VAR_OFFSET, then the member fields of FIELD are also
			// REACHABLE_FIELDS of the structure at VAR_OFFSET.
			if (!field_offset)
				get_reachable_fields_recursively 
					(root, field, var_offset + field_offset, reachable_fields);
		}
	}
}
/** 
 * Given a structure VAR_DECL at address VAR_OFFSET from root, this function
 * finds member fields that are nested inside this structure. Note that
 * the member fields of the non-pointer first field of every structure are
 * considered as nested.
 */

void parser::
get_reachable_fields_recursively (tree var_decl, HOST_WIDE_INT var_offset, set<unsigned int> & reachable_fields)
{
	if (!TREE_TYPE (var_decl) || !RECORD_OR_UNION_TYPE_P (TREE_TYPE (var_decl)))
		return;

	for (tree field = TYPE_FIELDS (TREE_TYPE (var_decl)); field; field = TREE_CHAIN (field))
	{
		if (TREE_CODE (field) == FIELD_DECL)
		{
			HOST_WIDE_INT field_offset = bitpos_of_field (field);
			DEBUG ("\n%s, offset=%lld", get_name (var_decl), field_offset);

			// 0 is not a subfield of a structure. In GCC, 0 is
			// represented by root varinfo only.
			if (var_offset + field_offset)
				reachable_fields.insert (var_offset + field_offset);

			// If FIELD is the first field of the structure at
			// VAR_OFFSET, then the member fields of FIELD are also
			// REACHABLE_FIELDS of the structure at VAR_OFFSET.
			if (!field_offset)
				get_reachable_fields_recursively 
					(field, var_offset + field_offset, reachable_fields);
		}
	}
}

void parser::
get_subfield_offsets (tree root, set<unsigned int> & subfields)
{
	if (!root)
		return;
	if (!TREE_TYPE (root))
		return;
	if (TREE_CODE (TREE_TYPE (root)) == POINTER_TYPE)
	{
		subfields.insert (0);
		return;
	}
	// Find subfields offset from ROOT.
	get_reachable_fields_recursively (root, 0, subfields);
}

/**
 * This function returns all TREE of locations accessible by AP.  There could
 * multiple possible TREE because ROOT or the first member of structure ROOT or
 * the first of the first member of structure ROOT or so on... could all be
 * followed by FIELDS.
 */

void parser::
get_ap_trees (list<unsigned int> & ap, set<tree> & ap_trees)
{
	if (!ap.size ())
		return;

	unsigned int root_id = *(ap.begin ());
	csvarinfo_t root_info = cs_get_varinfo (root_id);
	DEBUG ("\nroot_info=%s", root_info->name);

	if (!root_info)
		return;

	// If root is x.32, then root_info->decl saves the tree of x and not
	// x.32. Function get_decl() returns tree of x.32.
	tree root_type = get_decl (root_info);
	if (!root_type)
		return;

	list<unsigned int> fields = ap;
	list<unsigned int>::iterator root_it = fields.begin ();
	fields.erase (root_it);

	get_ap_trees (root_type, fields, ap_trees);
}

/** 
 * FIELDS is not passed by reference. We compute AP_TREES for all possible ROOT
 * types followed by FIELDS.
 */

void parser::
get_ap_trees (tree root, list<unsigned int> fields, set<tree> & ap_trees)
{
	DEBUG ("\n----%s---", get_name (root));
	// print_node (dump_file, 0, root, 0);
	
	if (!TREE_TYPE (root))
		return;

	// If ROOT is a structure, then recursively call get_ap_trees() on
	// first member of ROOT.	
	if (RECORD_OR_UNION_TYPE_P (TREE_TYPE (root)))
	{
		if (TYPE_FIELDS (TREE_TYPE (root)))
		{
			tree member = TYPE_FIELDS (TREE_TYPE (root));
			get_ap_trees (member, fields, ap_trees);
		}
	}

	// If FIELDS is empty, then the computed type is in ROOT
	if (!fields.size ())
	{
		ap_trees.insert (root);
		DEBUG ("\nFound tree");
		return;
	}

	unsigned int field = *(fields.begin ());

	// If first field in FIELDS is zero, then ROOT should be of pointer
	// type. Zero field does not represent first member of ROOT in GCC.
	if (!field)
	{
		DEBUG ("\nfield=%d", field);
		if (TREE_CODE (TREE_TYPE (root)) == POINTER_TYPE)
		{
			DEBUG ("\nroot is ptr");
			list<unsigned int>::iterator fi = fields.begin ();
			fields.erase (fi);
			tree ptr = TREE_TYPE (root);
			get_ap_trees (ptr, fields, ap_trees);
		}
		return;
	}

	// If first field in FIELDS is non-zero, then ROOT is a structure. We
	// find the fields of ROOT with the same offset as the first field in
	// FIELDS. This search of FIELD is a recursive function on nested
	// structures. get_decl_recursively() returns first type with matching
	// offset. We need to take into consideration all types nested at the
	// same offset --- this has been done by calling get_ap_trees() recursively
	// (above) on first member of root.
	DEBUG ("\nget_decl_recursively (root,0,%d)", field);
	// print_node_brief (dump_file, 0, root, 0);
 	tree field_tree = get_decl_recursively (root, 0, field);
	if (field_tree)
	{
		DEBUG ("\nfound field_tree");
		list<unsigned int>::iterator fi = fields.begin ();
		fields.erase (fi);
		// TREE_TYPE to remove FIELD_DECL top
		get_ap_trees (field_tree, fields, ap_trees);
	}
}

/* Count the number of arguments DECL has, and set IS_VARARGS to true
   if it is a varargs function.  */

unsigned int parser::
count_num_arguments (tree decl, bool *is_varargs)
{
  unsigned int num = 0;
  tree t;

  /* Capture named arguments for K&R functions.  They do not
     have a prototype and thus no TYPE_ARG_TYPES.  */
  for (t = DECL_ARGUMENTS (decl); t; t = DECL_CHAIN (t))
    ++num;

  /* Check if the function has variadic arguments.  */
  for (t = TYPE_ARG_TYPES (TREE_TYPE (decl)); t; t = TREE_CHAIN (t))
    if (TREE_VALUE (t) == void_type_node)
      break;
  if (!t)
    *is_varargs = true;

  return num;
}

/* Return true if FIELDSTACK contains fields that overlap.
   FIELDSTACK is assumed to be sorted by offset.  */

bool parser::
check_for_overlaps (VEC (fieldoff_s,heap) *fieldstack)
{
  fieldoff_s *fo = NULL;
  unsigned int i;
  HOST_WIDE_INT lastoffset = -1;

  FOR_EACH_VEC_ELT (fieldoff_s, fieldstack, i, fo)
    {
      if (fo->offset == lastoffset)
        return true;
      lastoffset = fo->offset;
    }
  return false;
}


/* qsort comparison function for two fieldoff's PA and PB */
// This function cannot be made a member function of this class

int
fieldoff_compare (const void *pa, const void *pb)
{
  const fieldoff_s *foa = (const fieldoff_s *)pa;
  const fieldoff_s *fob = (const fieldoff_s *)pb;
  unsigned HOST_WIDE_INT foasize, fobsize;

  if (foa->offset < fob->offset)
    return -1;
  else if (foa->offset > fob->offset)
    return 1;

  foasize = foa->size;
  fobsize = fob->size;
  if (foasize < fobsize)
    return -1;
  else if (foasize > fobsize)
    return 1;
  return 0;
}

/* Sort a fieldstack according to the field offset and sizes.  */
void parser::
sort_fieldstack (VEC(fieldoff_s,heap) *fieldstack)
{
  VEC_qsort (fieldoff_s, fieldstack, fieldoff_compare);
}


/*----------------------------------------------------------------------
  The base implementation. The method implements points-to analysis
  using callstrings method. All the functions that have _cs_ 
  prepended to their names have been lifted from tree-ssa-structalias.c
  ---------------------------------------------------------------------*/

/* Return the varmap element N */
csvarinfo_t parser::
cs_get_varinfo (unsigned int n)
{
   return VEC_index (csvarinfo_t, csvarmap, n);
}

/* Insert ID as the variable id for tree T in the vi_for_tree map.  */
void parser::
cs_insert_vi_for_tree (tree t, csvarinfo_t vi)
{
   DEBUG ("\ncs_insert_vi_for_tree(vi=%s(%d))\n", vi->name, vi->id);
   void **slot = pointer_map_insert (vi_for_tree, t);
   gcc_assert (vi);
   gcc_assert (*slot == NULL);
   *slot = vi;
}

bool parser::
is_proper_var (unsigned int varid)
{
   // return (varid > 2);
   // Changed by Vini

  // SUMM_K_CONSISTENT: node with is_summary_node has
  // var_id=wild_card_id which is a proper_var because it can represents any
  // proper field.
   return (varid > MAX_IMPROPER_ID);
}

/**
 * Used by dfa/points_to_analysis_fi.cpp: WILD_CARD_ID and varid > MAX_IMPROPER_ID
 * represent a variable.
 */

bool parser::
is_repr_var (unsigned int varid)
{
#if SUMM_K_CONSISTENT
	if (varid == wild_card_id)		return true;
#endif

	return (varid > MAX_IMPROPER_ID);
}

bool parser::
parm_decl (unsigned int varid)
{
   return (TREE_CODE (SSAVAR (cs_get_varinfo (varid)->decl)) 
	  == PARM_DECL);
}

struct cgraph_node * parser::
scoping_fn (unsigned int varid)
{
   return cs_get_varinfo (varid)->scoping_function;
}

bool parser::
var_defined_in_cfun (unsigned int varid, struct cgraph_node * cnode)
{
   return (cnode == scoping_fn (varid));
}

bool parser::
heap_var (unsigned int varid)
{
   return (cs_get_varinfo (varid)->is_heap_var);
}


bool parser::
global_var (unsigned int varid)
{
   return (cs_get_varinfo (varid)->is_global_var);
}

bool parser::
param_var (csvarinfo_t variable)
{
	if (variable && variable->decl && !variable->is_heap_var &&
                TREE_CODE (variable->decl) == PARM_DECL)
		return true;
	return false;
}

bool parser::
is_array (unsigned int vid)
{
	csvarinfo_t variable = 
		VEC_index (csvarinfo_t, program.variable_data, vid);

	if (TREE_CODE (variable->decl) == VAR_DECL &&
		TREE_CODE (TREE_TYPE (variable->decl)) == ARRAY_TYPE)
		return true;
	return false;
}

bool parser::
is_union (unsigned int vid)
{
	csvarinfo_t variable = 
		VEC_index (csvarinfo_t, program.variable_data, vid);

	if (TREE_CODE (variable->decl) == VAR_DECL &&
		TREE_CODE (TREE_TYPE (variable->decl)) == UNION_TYPE)
		return true;
	return false;
}

bool parser::
unexpandable_var (unsigned int var, HOST_WIDE_INT offset)
{
   return (offset == 0 ||
           !is_proper_var (var) ||
           offset == UNKNOWN_OFFSET ||
           cs_get_varinfo (var)->is_heap_var);
}

bool parser::
function_var (csvarinfo_t var)
{
	if (TREE_CODE (TREE_TYPE (var->decl)) == FUNCTION_TYPE 
		|| TREE_CODE (TREE_TYPE (var->decl)) == METHOD_TYPE)
		return true;
	return false;
}

bool parser::
parameter_var (csvarinfo_t var)
{
	if (TREE_CODE (var->decl) == PARM_DECL)
		return true;
	return false;
}

/* Given a gimple tree T, return the constraint expression vector for it
   to be used as the rhs of a constraint.  */
void parser::
cs_get_constraint_for_rhs (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
   gcc_assert (VEC_length (ce_s, *results) == 0);
   cs_get_constraint_for_1 (t, results, false, false, bb, cnode);
}

/* Return a new variable info structure consisting for a variable
   named NAME, and using constraint graph node NODE.  Append it
   to the vector of variable info structures.  */
csvarinfo_t parser::
cs_new_var_info (tree t, const char *name, struct cgraph_node * cnode)
{
   unsigned index = VEC_length (csvarinfo_t, csvarmap);
   DEBUG ("\n(csvarinfo_t) pool_alloc (csvarinfo_pool)");
   csvarinfo_t ret = (csvarinfo_t) pool_alloc (csvarinfo_pool);
   DEBUG ("\ncs_new_var_info index: %d, %s", index, name);
   DEBUG ("\nis_full_var = %d", t==NULL_TREE);

   ret->id = index;
   ret->name = name;
   ret->decl = t;
   ret->is_unknown_size_var = false;
   ret->is_full_var = (t == NULL_TREE);
   ret->is_heap_var = false;
   ret->may_have_pointers = true;
   ret->is_global_var = (t == NULL_TREE);
   /* Vars without decl are artificial and do not have sub-variables.  */
   // void* type of heap is marked as global_var.
   if (t && DECL_P (t))
     ret->is_global_var = (is_global_var (t)
                          /* We have to treat even local register variables
                             as escape points.  */
                          || (TREE_CODE (t) == VAR_DECL
                              && DECL_HARD_REGISTER (t)));
   //ret->constraints_with_vi_as_lhs = NULL;
   ret->scoping_function = (ret->is_global_var) ? NULL : cnode;
   ret->next = NULL;

   VEC_safe_push (csvarinfo_t, heap, csvarmap, ret);
   DEBUG ("\ncs_new_var_info=%s(%d) done", ret->name, ret->id);
   return ret;
}

/* Create a varinfo structure for NAME and DECL, and add it to VARMAP.
   This will also create any varinfo structures necessary for fields
   of DECL.  */
csvarinfo_t parser::
cs_create_variable_info_for_1 (tree decl, const char *name, struct cgraph_node * cnode)
{
   DEBUG ("\ncs_create_variable_info_for_1");
   DEBUG ("\nCreating var %s", name);

   csvarinfo_t vi, newvi;
   tree decl_type = TREE_TYPE (decl);	// decl=VAR_DECL, decl_type=RECORD_TYPE
   tree declsize = DECL_P (decl) ? DECL_SIZE (decl) : TYPE_SIZE (decl_type);
   VEC (fieldoff_s,heap) *fieldstack = NULL;
   fieldoff_s *fo;
   unsigned int i;

   if (!declsize || !host_integerp (declsize, 1)) {
	DEBUG ("\nis_full_var 1 for %s, %s", get_name (decl), name);
      vi = cs_new_var_info (decl, name, cnode);
      vi->offset = 0;
      vi->size = ~0;
      vi->fullsize = ~0;
      vi->is_unknown_size_var = true;
      vi->is_full_var = true;
      vi->may_have_pointers = true;
      return vi;
   }
   /* Collect field information.  */
   if (var_can_have_subvars (decl)
      /* ???  Force us to not use subfields for global initializers
	 in IPA mode.  Else we'd have to parse arbitrary initializers.  */
      && !(is_global_var (decl) && DECL_INITIAL (decl))) {

       DEBUG ("\nglobal variable 2: ");
       // print_node (dump_file, "", DECL_INITIAL (decl), 0);
	DEBUG ("\nis_full_var 2 for %s, %s", get_name (decl), name);
       fieldoff_s *fo = NULL;
       bool notokay = false;
       unsigned int i;

	// Comment this to make it field insensitive -- but too imprecise (e.g.
	// in h264ref, function pointer starts pointing to itsefl)
       push_fields_onto_fieldstack (decl_type, &fieldstack, 0);

       if (VEC_length (fieldoff_s, fieldstack) <= 1
          || VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE) {
	  DEBUG ("\n4-- will be executed");
       }
       else
   	  DEBUG ("\n4-- will NOT be executed");

       if (VEC_length (fieldoff_s, fieldstack) <= 1)
	{
  	  DEBUG ("\n<=1");
	}
       if (VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE)
	{
  	  DEBUG ("\n> MAX_FI... %d", MAX_FIELDS_FOR_FIELD_SENSITIVE);
	}
       else
  	  DEBUG ("\n< MAX_FI... %d", MAX_FIELDS_FOR_FIELD_SENSITIVE);

       for (i = 0; !notokay && VEC_iterate (fieldoff_s, fieldstack, i, fo); i++)
	   if (fo->has_unknown_size || fo->offset < 0) {
	       notokay = true;
	       break;
	   }

          /* We can't sort them if we have a field with a variable sized type,
 	  which will make notokay = true.  In that case, we are going to return
	  without creating varinfos for the fields anyway, so sorting them is a
	  waste to boot.  */
       if (!notokay) {

	   DEBUG ("\nis_full_var 3 for %s, %s", get_name (decl), name);
	   sort_fieldstack (fieldstack);
	   /* Due to some C++ FE issues, like PR 22488, we might end up
	      what appear to be overlapping fields even though they,
	      in reality, do not overlap.  Until the C++ FE is fixed,
	      we will simply disable field-sensitivity for these cases.  */
	   notokay = check_for_overlaps (fieldstack);
       }

       if (notokay)
	   VEC_free (fieldoff_s, heap, fieldstack);
   }

   if (VEC_length (fieldoff_s, fieldstack) <= 1)
   {
        DEBUG ("\n<=1");
   }
   if (VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE)
   {
        DEBUG ("\n> MAX_FI... %d", MAX_FIELDS_FOR_FIELD_SENSITIVE);
   }
   else
   {
	  DEBUG ("\n< MAX_FI... %d", MAX_FIELDS_FOR_FIELD_SENSITIVE);
   }


   /* If we didn't end up collecting sub-variables create a full
      variable for the decl.  */
   // MAX_FIELDS_FOR_FIELD_SENSITIVE is set to 0 if gcc is run with -O0 flag. 
   // It is set to 100 on my machine when gcc is run with -O3 flag.
   // FIXME: Vini: A structure with only field has VEC_length = 1; therefore, 
   // should we modify the check to <= 0
   if (VEC_length (fieldoff_s, fieldstack) <= 1
      || VEC_length (fieldoff_s, fieldstack) > MAX_FIELDS_FOR_FIELD_SENSITIVE) {

	DEBUG ("\nis_full_var 4 for %s, %s", get_name (decl), name);
       vi = cs_new_var_info (decl, name, cnode);
       vi->offset = 0;
       vi->may_have_pointers = true;
       vi->fullsize = TREE_INT_CST_LOW (declsize);
       vi->size = vi->fullsize;
       vi->is_full_var = true;
       VEC_free (fieldoff_s, heap, fieldstack);
       return vi;
   }

   DEBUG ("\nis_full_var 5 for %s, %s", get_name (decl), name);

   // FIXME: the non-pointer subfields are also stored. These should
   // not be considered.
   vi = cs_new_var_info (decl, name, cnode);
   vi->fullsize = TREE_INT_CST_LOW (declsize);
   for (i = 0, newvi = vi;
       VEC_iterate (fieldoff_s, fieldstack, i, fo);
       ++i, newvi = newvi->next) {

	DEBUG ("\nis_full_var 6 %s, %s\n", get_name (decl), name);

       const char *newname = "NULL";
       char *tempname;

       if (dump_file) {
	   asprintf (&tempname, "%s." HOST_WIDE_INT_PRINT_DEC
		    "+" HOST_WIDE_INT_PRINT_DEC, name, fo->offset, fo->size);
	   newname = ggc_strdup (tempname);
	   free (tempname);

           DEBUG ("\nnewname %s", newname);
       }
       DEBUG ("\noffset %llu, size %d", fo->offset, fo->size);
       newvi->name = newname;
       newvi->offset = fo->offset;
       newvi->size = fo->size;
       newvi->fullsize = vi->fullsize;
       newvi->may_have_pointers = fo->may_have_pointers;
       // Removed by Prashant ??
       // newvi->only_restrict_pointers = fo->only_restrict_pointers;
       if (i + 1 < VEC_length (fieldoff_s, fieldstack))
	   newvi->next = cs_new_var_info (decl, name, cnode);
       // Added by Vini
       newvi->field_decl = fo->field_decl;
   }

   VEC_free (fieldoff_s, heap, fieldstack);
   if (vi)
      DEBUG ("\nreturning vi %s, id %d, offset %llu\n", vi->name, vi->id, vi->offset);
   return vi;
}

unsigned int parser::
cs_create_variable_info_for (tree decl, const char *name, basic_block bb, struct cgraph_node * cnode)
{
   DEBUG ("\ncs_create_variable_info_for\n");
   DEBUG ("\nname %s\n", name);
   csvarinfo_t vi = cs_create_variable_info_for_1 (decl, name, cnode);
   DEBUG ("\ncreated vi %s, id %d, offset %llu\n", vi->name, vi->id, vi->offset);
   unsigned int id = vi->id;

   cs_insert_vi_for_tree (decl, vi);

   /* Create initial constraints for globals.  */
   for (; vi; vi = vi->next) {
       if (!vi->may_have_pointers || !vi->is_global_var)
	   continue;

       DEBUG ("\nloop -- vi %s, id %d, offset %llu\n", vi->name, vi->id, vi->offset);	

	// Vini: DECL_INITIAL (decl) is true only if decl is global variable
	// and it has been initialized with ADDRESSOF globally.
	// FIXME: Here, this global ADDRESSOF constraint is inserted right
	// above the first use of the decl variable. This is wrong. For
	// example, 
	// int *global=&v1; int 
	// int main() {
	//    if (condition) global=&v2; }
	// The following code will wrongly insert the global constraint
	// inside the if condition, instead of outside it; therefore, v1 will
	// unsafely get overwritten by v2.

       /* If this is a global variable with an initializer,
 	  generate constraints for it. */
       if (DECL_INITIAL (decl)) {
#if DEBUG_CONTAINER
	   DEBUG ("\nglobal variable: ");
	   //print_node (dump_file, "", decl, 0);
	   DEBUG ("\nDECL_INITIAL(decl): ");
	   //print_node (dump_file, "", DECL_INITIAL (decl), 0);
#endif
	   VEC (ce_s, heap) *rhsc = NULL;
	   struct constraint_expr lhs, *rhsp;
	   unsigned i;
	   cs_get_constraint_for_rhs (DECL_INITIAL (decl), &rhsc, bb, cnode);
	   lhs.var = vi->id;
	   lhs.offset = 0;
	   lhs.type = SCALAR;
	   FOR_EACH_VEC_ELT (ce_s, rhsc, i, rhsp)		// Vini: Why commented out????
	       cs_process_constraint (new_constraint (lhs, *rhsp), bb);
	   VEC_free (ce_s, heap, rhsc);			// Vini: Why commented out????
       }
    }

   DEBUG ("\nreturn of cs_create_variable_info_for id %d\n", id);
   return id;
}

/**
 * Find the variable id for tree T in the map. If T doesn't exist in the map,
 * create an entry for it and return it. Use cs_lookup_vi_for_tree if you do
 * not want to create a new csvarinfo_t.
 */

  csvarinfo_t parser::
cs_get_vi_for_tree (tree stmt, basic_block bb, struct cgraph_node * cnode)
{
   DEBUG ("\ncs_get_vi_for_tree");
   tree t = SSAVAR (stmt);
   void **slot = pointer_map_contains (vi_for_tree, t);
   if (slot == NULL)
   {
       DEBUG ("\nslot == NULL");

       csvarinfo_t vi = cs_get_varinfo (cs_create_variable_info_for (t, alias_get_name (t), bb, cnode));
#if DEBUG_CONTAINER
       if (vi)
         DEBUG ("\nIN cs_get_vi_for_tree: vi %s, id %d, offset %llu\n", vi->name, vi->id, vi->offset);
#endif
       return vi;
       //return cs_get_varinfo (cs_create_variable_info_for (t, alias_get_name (t), bb, cnode));
   }

#if DEBUG_CONTAINER
   csvarinfo_t vi = (csvarinfo_t) *slot;
   if (vi)
      DEBUG ("\nslot %s, offset %llu\n", vi->name, vi->offset);
#endif 

   return (csvarinfo_t) *slot;
}

/* Find the variable info for tree T in VI_FOR_TREE. If T does not
   exist in the map, return NULL, otherwise, return the varinfo 
   we found.  */
csvarinfo_t parser::
cs_lookup_vi_for_tree (tree t)
{
   void **slot = pointer_map_contains (vi_for_tree, t);
   if (slot == NULL)
       return NULL;

   return (csvarinfo_t) *slot;
}

/* Get a scalar constraint expression for a new temporary variable.  */
struct constraint_expr parser::
cs_new_scalar_tmp_constraint_exp (const char *name, struct cgraph_node * cnode)
{
   struct constraint_expr tmp;
   csvarinfo_t vi;

   vi = cs_new_var_info (NULL_TREE, name, cnode);
   vi->offset = 0;
   vi->size = -1;
   vi->fullsize = -1;
   vi->is_full_var = 1;

   tmp.var = vi->id;
   tmp.type = SCALAR;
   tmp.offset = 0;

   return tmp;
}

/* CHANGE DUE TO GCC-4.7.2
   function make_heapvar_for of gcc-4.6.* is modified to make_heapvar in gcc-4.7.2.
   This cs_make_heapvar_for is also modified */

/* Temporary storage for fake var decls.  */
struct obstack fake_var_decl_obstack;

/* Build a fake VAR_DECL acting as referrer to a DECL_UID.  */

tree parser::
build_fake_var_decl (tree type)
{
  tree decl = (tree) XOBNEW (&fake_var_decl_obstack, struct tree_var_decl);
  memset (decl, 0, sizeof (struct tree_var_decl));
  TREE_SET_CODE (decl, VAR_DECL);
  TREE_TYPE (decl) = type;
  DECL_UID (decl) = allocate_decl_uid ();
  SET_DECL_PT_UID (decl, -1);
  layout_decl (decl, 0);
  return decl;
}

/**
 * MEM[...] contains type casted value of the pointer. MEM_REF appears when
 * test.c is compiled with -O3 option.
 * This function returns the inside of POINTER_TYPE ptr, which is used as
 * MEM_REF (typecasted) in PTR_USE.
 */

tree parser::
get_memref_casted_inside_type (tree ptr_use, tree ptr)
{
	DEBUG ("\nget_memref_casted_inside_type");

	// print_node (dump_file, 0, ptr_use, 0);
	// PTR may have MEM[...]
	tree top = ptr_use;
	// PTR may have &MEM[...]
	if (ptr_use && TREE_CODE (ptr_use) == ADDR_EXPR)
	{
		DEBUG ("\nptr_use is ADDR_EXPR");
		top = TREE_OPERAND (ptr_use, 0);
	}

	tree subtree = top;
	if (top && TREE_CODE (top) == COMPONENT_REF)
	{
		DEBUG ("\nptr_use has COMPONENT_REF");
		tree subtree = TREE_OPERAND (top, 0);
		// PTR may have multiple COMPONENT_REF. For example,
		// MEM[...].f.g has two COMPONENT_REF.
		return get_memref_casted_inside_type (subtree, ptr);
	}

	if (subtree && TREE_CODE (subtree) == MEM_REF)
	{
		DEBUG ("\nptr_use has MEM_REF");
		// We desire to find the casted type of PTR. Check that PTR is
		// actually inside USE_PTR (i.e. in this subtree).
		tree arg0 = TREE_OPERAND (subtree, 0);
		if (arg0 != ptr)
		{
			// This case arises in test43.c where MEM[t1]=MEM[t2].
			// We want to find t2 but we are exploring lhs.
			DEBUG ("\nLooking into wrong MEM_REF");
			return NULL;
		}

		// x=... is not being handled in this function:
		// get_memref_casted_inside_type().  LHS is MEM_REF, which is
		// DEREF type. TREE_OPERAND(0) of MEM_REF is ADDR_EXPR type.
		// This means LHS is SCALAR.  Therefore, type of LHS is
		// TREE_TYPE(MEM_REF). Therefore, type of heap pointed by LHS
		// is TREE_TYPE(TREE_TYPE(MEM_REF)).  However, since
		// TREE_OPERAND(0) cannot be PTR, we are not handling it here.
		// x=x.0_1 (test20.c)

		// MEM[...]
		// This is MEM_REF, which is DEREF type. TREE_OPERAND(0) of
		// MEM_REF is non ADDR_EXPR type. This means it is DEREF.
		// Therefore, its type is POINTER_TYPE containing
		// TREE_TYPE(MEM_REF). Therefore, type of heap pointed by it is
		// TREE_TYPE(MEM_REF).
		// &MEM[(struct node *)v].g (test31i.c)
		// MEM[(struct node **)p]=... (test31i.c)

		tree tree_type = TREE_TYPE (subtree);
		if (TREE_CODE (tree_type) != VOID_TYPE)
		{
			DEBUG ("\nFound type in ptr_use");
			// print_node (dump_file, 0, ptr_use, 0);
			return tree_type;
		}
	}

	return NULL;
}

/** 
 * This function returns the inside of POINTER_TYPE ptr if it is not VOID_TYPE.
 */

tree parser::
get_inside_type (tree ptr)
{
	// If PTR is COMPONENT_REF or MEM_REF, then the casted type is
	// available. First TREE_TYPE() is used to get one level down from
	// COMPONENT_REF/MEM_REF. TREE_TYPE(TREE_TYPE()) is used to remove
	// POINTER_TYPE in order to return the inside of PTR.
	if (TREE_CODE (ptr) == COMPONENT_REF || TREE_CODE (ptr) == MEM_REF)
	{
		DEBUG ("\nptr is COMPONENT_REF|MEM_REF");
		tree tt = TREE_TYPE (ptr);
		if (tt && TREE_CODE (tt) == POINTER_TYPE)
		{
			DEBUG ("Computed type from indirect lhs");
			// print_node (dump_file, 0, TREE_TYPE (TREE_TYPE (ptr)), 0);
			return TREE_TYPE (TREE_TYPE (ptr));
		}
		else
		{
			RESULT ("\nError: We have reached a non-pointer.");
			return NULL;
		}
	}

	DEBUG ("\nptr = %s: ", get_name (ptr));
	// print_node (dump_file, 0, ptr, 0);
	tree ptr_decl = SSAVAR (ptr);
	if (!ptr_decl) 	return NULL;
	DEBUG ("\nptr_decl: ");
	// print_node (dump_file, 0, ptr_decl, 0);
	tree ptr_pointer = TREE_TYPE (ptr_decl);
	if (!ptr_pointer) return NULL;
	DEBUG ("\nptr_pointer: ");
	// print_node (dump_file, 0, ptr_pointer, 0);
	tree ptr_type = TREE_TYPE (ptr_pointer);
	if (!ptr_type) return NULL;
	DEBUG ("\nptr_type: ");
	if (TREE_CODE (ptr_type) == VOID_TYPE) return NULL;

	DEBUG ("\nFound type in ptr");
	DEBUG ("Computed type from direct lhs");
	// print_node (dump_file, 0, ptr_type, 0);
	return ptr_type;
}

/**
 * This function returns the type inside POINTER_TYPE if PTR is not of 'void *'
 * type. Otherwise it traverses the SSA use-chains to find and return the
 * inside of the casted type of PTR. Note that this function is called to find
 * the type of heap location which needs the inside of POINTER_TYPE created by
 * malloc().
 */

tree parser::
get_casted_inside_type (tree ptr)
{
	DEBUG ("\nget_casted_inside_type()");
	if (!ptr)
		return NULL;

	// Get inside of POINTER_TYPE ptr if a non-VOID_TYPE is already
	// present.
	tree inside_type = get_inside_type (ptr);
	if (inside_type)
		return inside_type;

	// If ptr is not SSA_NAME, then we cannot find its type
	if (TREE_CODE (ptr) != SSA_NAME)
	{
		DEBUG ("\nptr is not SSA_NAME");
		return NULL;
	}
	DEBUG ("\nptr is SSA_NAME");
	
	tree casted_inside_type = NULL;
	gimple stmt;
	imm_use_iterator imm_iter;
	DEBUG ("\nTraversing ssa uses");
	FOR_EACH_IMM_USE_STMT (stmt, imm_iter, ptr)
	{
		if (!is_gimple_assign (stmt)) 
			continue;
#if DEBUG_CONTAINER
		DEBUG ("\nIterate: ");
		print_gimple_stmt (dump_file, stmt, 0, 0);
#endif

		// use_operand_p use_p;
		// FOR_EACH_IMM_USE_ON_STMT (use_p, imm_iter)
		// {
		// 	tree use = USE_FROM_PTR (use_p);
		//	DEBUG ("\nuse ssa\n");
		//	print_node (dump_file, 0, use, 0);
		// }

		tree lhsop = gimple_assign_lhs (stmt);
 		tree rhsop = (gimple_num_ops (stmt) == 2) ? gimple_assign_rhs1 (stmt) : NULL;

		if (rhsop == ptr)
			if (casted_inside_type = get_casted_inside_type (lhsop))
				BREAK_FROM_IMM_USE_STMT (imm_iter);

		// The typecasted value could be retrieved from LHS/RHS also if
		// PTR is used as MEM[(struct node *)ptr] in LHS/RHS.

		// Note that cs_get_constraint_for() is not helpful in deriving
		// type since it stores void* type of variable used inside MEM.

		// DEBUG ("\nget_memref_casted_inside_type (lhs)");
		// print_node (dump_file, 0, lhsop, 0);
		if (casted_inside_type = get_memref_casted_inside_type (lhsop, ptr))
		{
			DEBUG ("\nComputed type from memref lhs");
			BREAK_FROM_IMM_USE_STMT (imm_iter);
		}

		// DEBUG ("\nget_memref_casted_inside_type (rhs)");
		// print_node (dump_file, 0, rhsop, 0);
		if (casted_inside_type = get_memref_casted_inside_type (rhsop, ptr))
		{
			DEBUG ("\nComputed type from memref rhs");
			BREAK_FROM_IMM_USE_STMT (imm_iter);
		}
	}
	if (!casted_inside_type)
	{
		DEBUG ("\ncasted type not found");
		return NULL;
	}

	DEBUG ("\ncasted_inside_type found");
	// print_node (dump_file, 0, casted_inside_type, 0);
	return casted_inside_type;
}

/**
 * This function computes the tree of heap allocated by malloc(). It removes
 * POINTER_TYPE from the VAR.
 */

tree parser::
get_heap_decl (tree var)
{
	DEBUG ("\nget_heap_decl()");

	// Get inside of POINTER_TYPE var i.e. get the type of the heap
	// location pointed by var.
	tree casted_var_inside_type = get_casted_inside_type (var);

	tree heap_decl;
	if (casted_var_inside_type)
	{
		DEBUG ("\nGot casted_var_inside_type");
		// Use this if casted_var_inside_type contains RECORD_TYPE (e.g.) directly
		heap_decl = build_fake_var_decl (casted_var_inside_type);
		// Use this if casted_var_inside_type is VAR_DECL containing
		// POINTER_TYPE containing RECORD_TYPE (e.g.)
		//heap_decl = build_fake_var_decl (TREE_TYPE (TREE_TYPE (SSAVAR (casted_var_inside_type))));
	}
	// Benchmark bzip2. default_bzalloc() returns heap with 'void *'. Its
	// type cannot be derived. This is not an error.
	else
	{
		// Do not print bb and cnode. They might be null.
		RESULT ("\nError:? Cannot compute typecasted value of heap");
		// Prashant: C type 'void *' is ptr_type_node
		heap_decl = build_fake_var_decl (ptr_type_node);
		// A heap location is not of POINTER_TYPE. Create VOID_TYPE.
		// But this gives some problem with cs_first_vi_for_offset().
		// heap_decl = build_fake_var_decl (void_type_node);
		DECL_EXTERNAL (heap_decl) = 1;
		return heap_decl;
	}

	return heap_decl;
}

// Added by Vini
/** 
 * Create fields of H of type HEAP_POINTER_TYPE in program.variable_data and
 * return H.FIELD.  
 * Note that this function is called only for x->f=... or ...=x->f type of
 * statements and not x=... or ..=x since we need to ensure that pointee of x
 * is in correct typecast while f is dereferenced in former type of statements
 * (i.e. those involving x->f). It does not matter whether or not pointee of x
 * is in correct typecast in latter type of statements (i.e. those involving x
 * only).
 */

csvarinfo_t parser::
generate_heap_field_vars (unsigned int heap_var, tree heap_pointer_type, unsigned int field)
{
	DEBUG ("\nprogram::generate_heap_field_vars(heap_var=%d, heap_pointer_type, field=%d)", 
		heap_var, field);
	csvarinfo_t original_heap = VEC_index (csvarinfo_t, variable_data, heap_var);

	if (!original_heap || !original_heap->is_heap_var)
	{
		RESULT ("\nError: generate_heap_field_nodes() has been called for a non-heap node");
		return NULL;
	}

	// If HEAP_POINTER_TYPE is NULL or HEAP_DECL is NULL (e.g. when
	// HEAP_POINTER_TYPE is VOID *), do not consider it as an error. We do
	// not perform typecasting in that case and simply find offset from
	// VAR.

	// Find offset only 
	// (a) if fields need to be created (i.e. field/=0) or
	// (b) heap_decl is NULL or
	// (c) if original_heap is heap_pointer_type

	// Get inside of POINTER_TYPE var i.e. get the type of the heap
	// location pointed by heap_pointer_type.
	// get_decl() is important because if original_heap is member field
	// then original_heap->decl is type of root var; whereas heap_decl is
	// type of member field only.
	tree heap_decl = get_casted_inside_type (heap_pointer_type);
	if (!field || !heap_decl || TREE_TYPE (get_decl (original_heap)) == heap_decl)
	{
		// Check if H.FIELD variable name exists in VARIABLE_DATA.
		DEBUG ("\nFind field=%d, from %s(%d)", field, original_heap->name, original_heap->id);
		csvarinfo_t heap_field_var = cs_first_vi_for_offset (original_heap, field);

		// cs_get_constraint_for_component_ref() states that "in languages like
		// C, you can access one past the end of an array.  You aren't allowed
		// to dereference it, so we can ignore this constraint. When we handle
		// pointer subtraction, we may have to do something cute here.". 
		// In hmmer, scan=r->program[1] is such a case. We simply ignore such a
		// case.
		if (!heap_field_var)
		{
			RESULT ("\nError: original_heap=%s(%d) field=0 not found or typecast not found!",
				original_heap->name, original_heap->id);
			return NULL;
		}

		// If H.FIELD is present in VARIABLE_DATA.
		DEBUG ("\nheap_field_var=%s(%d)", heap_field_var->name, heap_field_var->id);
		return heap_field_var;
	}

	// Either H.FIELD is not present in VARIABLE_DATA or H->decl and
	// H->next need to be connected to it.

	DEBUG ("\nTypecasting heap var %s(%d), offset %d",
		original_heap->name, original_heap->id, original_heap->offset);

	// If original_heap is a field i.e. original_heap is a field of a super
	// root and the field is being typecasted.
	// For example, if heap.s.32 (s is the allocation site) is dereferenced
	// via 64, then we want to create heap.s.96 and not heap.s.32.64 or
	// heap.s.32.96. Therefore, we need to find heap.s from heap.s.32 and
	// we need to add 32 and 64 for the offset of the new heap variable.
	// const char * base_heap_name = cs_lookup_vi_for_tree (original_heap->decl)->name;
	// In this case, the chain of newly generated subfields of
	// original_heap need to be appended to chain of super root. This is
	// tricky. 

	// We assume that original_heap is the super root itself.

	if (original_heap->offset)
	{
		RESULT ("\nError: field typecasting is not handled. original_heap=%s(%d), offset=%lld", 
			original_heap->name, original_heap->id, original_heap->offset);
		return NULL;

		// FIXME: It may be that VAR is T2 and points to heap field
		// whose root is of type T1 but its own type is T2. Therefore,
		// root type of pointee and typecasted type (of VAR=T2) do not
		// match. This is not an error. In fact it is unsafe even when
		// no typecasting has been done.
	}

	csvarinfo_t heap_field_var = cs_make_heapvar_offset_for
		(original_heap, heap_pointer_type, field, original_heap->name, NULL, NULL);

	if (heap_field_var)
		DEBUG ("\nNew heap var %s(%d)", heap_field_var->name, heap_field_var->id);

	return heap_field_var;
}

/* Create a new heap variable with NAME. Return the created variable.  */

csvarinfo_t parser::
cs_make_heapvar_for (tree lhs, const char *name, basic_block bb, struct cgraph_node * cnode)
{
	DEBUG ("\ncs_make_heapvar_for()");

	// Get heap type from lhs
	tree heap_decl = get_heap_decl (lhs);
	if (!heap_decl)
	{
		RESULT ("\nError: heap_decl not created");
		return NULL;
	}

#if HEAP_TYPE_BASED_NAME
	tree heap_type = TREE_TYPE (heap_decl);
	if (!heap_type)
	{
		RESULT ("\nError: heap type not found");
		return NULL;
	}
	// Check if heap of this type has already been created. 
	if (heap_type_id.find (heap_type) != heap_type_id.end ())
	{
	     unsigned int heap_id = heap_type_id[heap_type];
	     DEBUG ("\nHeap type %d already present", heap_id);
	     csvarinfo_t heap_var = VEC_index (csvarinfo_t, variable_data, heap_id);
	     return heap_var;
	}

	/* Append 'heap' with the its index in csvarinfo. */
	DEBUG ("\nheap_type_count=%d", heap_type_count);
	char *tempname;
	heap_type_count++;
	asprintf (&tempname, "%s.T%d", name, heap_type_count);
#else
	char *tempname;
	unsigned int alloc_site = VEC_length (csvarinfo_t, csvarmap);
	asprintf (&tempname, "%s.%d", name, VEC_length (csvarinfo_t, csvarmap));
#endif

	const char * heap_name = ggc_strdup (tempname);

	unsigned int heap_id = cs_create_variable_info_for (heap_decl, heap_name, bb, cnode);

	csvarinfo_t heap_var = VEC_index (csvarinfo_t, variable_data, heap_id);
	for (csvarinfo_t temp = heap_var; temp; temp = temp->next)
	{
		temp->is_heap_var = true;
		temp->scoping_function = NULL;
		heap_to_alloc_site[temp->id] = alloc_site;
	}

	DEBUG ("\n%s(%d) TYPE:\n", heap_var->name, heap_var->id);
	// print_node (dump_file, 0, heap_type, 0);

#if HEAP_TYPE_BASED_NAME
	// Populate heap_type_id map with newly created heap location.
	heap_type_id[heap_type] = heap_id;
#endif

	return heap_var;
}

/** 
 * Create offsets of heap variables with HEAP_NAME. This function is called
 * on-the-fly with the analysis i.e. when ORIGINAL_HEAP is already in existence
 * and its OFFSET has not been found. Since ORIGINAL_HEAP is already in existence
 * in VARIABLE_DATA at offset 0, replace newly created offset 0 with
 * ORIGINAL_HEAP in the chain of offsets.
 */

csvarinfo_t parser::
cs_make_heapvar_offset_for (csvarinfo_t original_heap, 
	tree heap_pointer_type, 
	unsigned int offset, 
	const char * heap_name, 
	basic_block bb, 
	struct cgraph_node * cnode)
{
	DEBUG ("\ncs_make_heapvar_offset_for()");

	// Benchmark bzip2. default_bzalloc() returns heap with 'void *'. Its
	// type cannot be derived. This is not an error.

	// Create all offsets of type HEAP_POINTER_TYPE
	tree heap_decl = get_heap_decl (heap_pointer_type);
	if (!heap_decl)
	{
		RESULT ("\nError: heap_decl not created");
		return NULL;
	}

	// get_alloc_site_typecast() returns the varinfo that originally had
	// heap_decl type of tree. Note that currently new_heap->decl may not
	// be heap_decl

	// I don't know why this does not work.
	// csvarinfo_t new_heap = cs_lookup_vi_for_tree (heap_decl);
	csvarinfo_t new_heap = get_alloc_site_typecast (original_heap->id, heap_decl);

	// HEAP_DECL does not exist in VARIABLE_DATA
	if (!new_heap)
	{
		#if INTERMEDIATE_RESULT
		RESULT ("\non-the-fly creation of heap nodes.");
		#endif

		DEBUG ("\ntypecasted type not found");
		unsigned int alloc_site = heap_to_alloc_site[original_heap->id];
		char * typecasted_heap_name = get_new_type_heap_name (heap_name, alloc_site);
		unsigned int heap_id = cs_create_variable_info_for (heap_decl, typecasted_heap_name, bb, cnode);
		new_heap = VEC_index (csvarinfo_t, variable_data, heap_id);
		for (csvarinfo_t temp = new_heap; temp; temp = temp->next)
		{
			DEBUG ("\nIterate heap %s(%d)=offset=%d", 
				temp->name, temp->id, temp->offset);
			temp->is_heap_var = true;
			temp->scoping_function = NULL;
			heap_to_alloc_site[temp->id] = alloc_site;
			DEBUG ("\nheap_to_alloc_site[%s(%d)]=%d", temp->name, temp->id, alloc_site);
		}
	}

	// When H is typecasted to H', we change the decl of H and use H
	// instead of H'. Using H' instead of H would lead to too much cloning
	// and is redundant because all typecasts of H have the same in
	// points-to edges and differ only by their type. Things get more
	// complicated with points_to_analysis_fi (see
	// dfa/points_to_analysis_fi.cpp :: generate_field_nodes()).

	typecast_varinfo (original_heap, new_heap);

	// The required offset may not be found exactly in the created chain of
	// offsets. It should, however, overlap. 
	DEBUG ("\nFind heap %s(%d) offset=%d", original_heap->name, original_heap->id, offset);
	csvarinfo_t heap_offset_var = cs_first_vi_for_offset (original_heap, offset);
	if (heap_offset_var)
	{
		DEBUG ("\nReturning heap %s(%d)=offset=%d", 
			heap_offset_var->name, heap_offset_var->id, heap_offset_var->offset);
	}
	else
	{
		DEBUG ("\nHeap %s(%d) offset=%d not found", 
			original_heap->name, original_heap->id, offset);
	}

	return heap_offset_var;
}

/**
 * This function  appends type id of this allocation site to the
 * original_heap_name for better debugging.
 */

char * parser::
get_new_type_heap_name (const char * original_heap_name, unsigned int alloc_site)
{
	if (alloc_site_typecasts.find (alloc_site) == alloc_site_typecasts.end ())
	{
		char * typecasted_heap_name;
		// asprintf allocates space in heap.
		// We append T2 to the heap_name because T1 is the original type itself.
		asprintf (&typecasted_heap_name, "%s.T2", original_heap_name);
		return typecasted_heap_name;
	}
		
	set<tree> types = alloc_site_typecasts[alloc_site];

	// Find the number of typecasts of this allocation id
	unsigned int typecast_count = types.size ();

	char * typecasted_heap_name;
	// asprintf allocates space in heap.
	// We append "+1" to type count and not "+2" because original type has
	// also been added to alloc_site_typecasts by now.
	asprintf (&typecasted_heap_name, "%s.T%d", original_heap_name, typecast_count + 1);
	return typecasted_heap_name;
}

/** 
 * This function returns the typecasted types of var using
 * alloc_site_typecasts. We have assumed that heap fields are not typecasted.
 * Therefore, if var is a heap field, then nothing is returned.  Else all the
 * typecasts (if any) are returned.
 */

set<tree> parser::
get_alloc_site_typecasts (unsigned int var)
{
	set<tree> types;
	csvarinfo_t var_info = VEC_index (csvarinfo_t, variable_data, var);

	// We have assumed that a heap field is not typecasted
	if (var_info->offset)
		return types;

	if (heap_to_alloc_site.find (var) == heap_to_alloc_site.end ())
		return types;
	unsigned int alloc_site = heap_to_alloc_site[var];
	// Fetch csvarinfo using the typecasted types of heap at alloc_site
	if (alloc_site_typecasts.find (alloc_site) == alloc_site_typecasts.end ())
		return types;

	types = alloc_site_typecasts[alloc_site];

	return types;
}

/**
 * This function returns the csvarinfo whose type is same as TYPE and its a
 * typecasted type of var in alloc_site_typecasts.
 */

csvarinfo_t parser::
get_alloc_site_typecast (unsigned int var, tree type)
{
	DEBUG ("\nget_alloc_site_typecast(var=%d,type)", var);
	set<tree> types = get_alloc_site_typecasts (var);
//	if (types.find (type) == types.end ())
//		return false;
	set<tree>::iterator ti;	
	for (ti = types.begin (); ti != types.end (); ti++)
	{
		tree t = *ti;
		if (TREE_TYPE (t) != TREE_TYPE (type))
			continue;

		// cs_lookup_vi_for_tree returns the varinfo that originally
		// had t type of tree. Note that currently type_varinfo->decl
		// may not be t.
		csvarinfo_t type_varinfo = cs_lookup_vi_for_tree (t);
		if (!type_varinfo)
		{
			csvarinfo_t varinfo = VEC_index (csvarinfo_t, variable_data, var);
			RESULT ("\nError: tree lookup on typecast of var=%s(%d) not working", 
				varinfo->name, varinfo->id);
			continue;
		}
		#if DEBUG_CONTAINER
		csvarinfo_t varinfo = VEC_index (csvarinfo_t, variable_data, var);
		DEBUG ("\nTypecaste of var=%s(%d) is in %s(%d)", varinfo->name, varinfo->id,
			type_varinfo->name, type_varinfo->id);
		#endif

		// Note that VAR_DECL of TYPE is different from VAR_DECL stored
		// in cs_lookup_vi_for_tree. But their TREE_TYPE are same. More
		// specifically VAR_DECL of original type_varinfo->decl and
		// TYPE is different.

		return type_varinfo;
	}
	return NULL;
}

void parser::
get_all_typecasted_out_fields (unsigned int var, map<unsigned int, set<unsigned int> > & out_field_edges)
{
	DEBUG ("\nget_all_typecasted_out_fields (var=%d)", var);

	// Collect typecasted types. Note only the root is typecasted.
	// Therefore, cs_lookup_vi_for_typecasts fetches the csvarinfo_t of
	// those var->id that are root and not fields, and the original
	// csvarinfo_t of var -- root and field both.
	
	set<csvarinfo_t> var_typecasts;
	cs_lookup_vi_for_typecasts (var, var_typecasts);
	DEBUG ("\nFound %d types for var_decl=%d", var_typecasts.size (), var);

	set<csvarinfo_t>::iterator vi;
	for (vi = var_typecasts.begin (); vi != var_typecasts.end (); vi++)
	{
		csvarinfo_t typecasted_var = *vi;
		if (!typecasted_var)
		{
			RESULT ("\nError: NULL typecasted_var retrieved");
			continue;
		}
		DEBUG ("\nget_out_fields (%s(%d))", typecasted_var->name, typecasted_var->id);

		get_out_fields (typecasted_var->id, out_field_edges);
	}
	DEBUG ("\ndone get_all_typecasted_out_fields (var=%d)", var);
}

/** 
 * Fetches out-fields of variable of type src_var->decl. Note that variable
 * could be a heap variable that has been typecasted to src_var->decl. Old
 * typecasts are not considered.
 * Although a type of src_var can have only one out-node on every field, but we
 * are passing out_field_edges which holds multiple out-nodes on every field.
 * This is for convenience so that out_field_edges can be accumulated.
 *
 * output: out_field_edges
 */

void parser::
get_out_fields (unsigned int variable, map<unsigned int, set<unsigned int> > & out_field_edges)
{                       
	DEBUG ("\nget_out_fields (variable=%d)", variable);
	csvarinfo_t src_var = VEC_index (csvarinfo_t, variable_data, variable);

	// Generate field nodes nested inside VAR and connect them with an edge
	// labeled with offset difference. 

        DEBUG ("\ninsert field edges (%s(%d))", src_var->name, src_var->id);
        // Get all the field variables inside structure SRC_VAR
        set<unsigned int> reachable_field_vars;
	get_reachable_fields (src_var, reachable_field_vars);
                        
        set<unsigned int>::iterator fi;
        for (fi = reachable_field_vars.begin (); fi != reachable_field_vars.end (); fi++)
        {                       
                unsigned int field_var = *fi;
		DEBUG ("\nfield_var=%d", field_var);
                if (!is_proper_var (field_var))
                        continue;
                        
                csvarinfo_t field_info = VEC_index (csvarinfo_t, variable_data, field_var);
		if (!field_info)
		{
			RESULT ("\nError: field_info of field_var=%d not found", field_var);
			continue;
		}
		DEBUG ("\nfield_info=%s(%d)", field_info->name, field_info->id);
                unsigned int field_edge = field_info->offset - src_var->offset;
                // Do not create a field edge if source and destination nodes are same. e.g.
                // struct type1 { int * p; struct type2 f; }; struct type2 { struct type2 *g; };
                // For x of type1, x.f (source node) reaches x.f.g (destination
                // node) via field edge 0; however, both x.f and x.f.g are
                // represented by the same node.
                if (!field_edge)
                        continue;
                if (field_edge < 0)
                {
                        RESULT ("\nError: Negative field edge");
                        continue;
                }

                out_field_edges[field_edge].insert (field_var);
        }
        DEBUG ("\ndone get_out_fields (variable=%d)", variable);
}

/** 
 * This function is called for stack/heap VARIABLE whose type is not known.
 * Therefore, OFFSET is found for all possible typecasts of VARIABLE in the
 * program.
 */

set<unsigned int> parser::
get_var_fields (unsigned int variable, unsigned int offset)
{
	// Offset 0 means pointer of variable and not variable itself. Not
	// field. empty will be returned in such a case because no typecaseted
	// out field will contain 0 field.
//	if (!offset)
//	{
//		set<unsigned int> var;
//		var.insert (variable);
//		return var;
//	}

	map<unsigned int, set<unsigned int> > out_field_edges;

	get_all_typecasted_out_fields (variable, out_field_edges);
#if DEBUG_CONTAINER
	if (out_field_edges.empty ())
		DEBUG ("\nFields of var=%d are NULL", variable);
	map<unsigned int, set<unsigned int> >::iterator ei;
	for (ei = out_field_edges.begin (); ei != out_field_edges.end (); ei++)
	{
		unsigned int f = ei->first;
		set<unsigned int> pf = ei->second;
		set<unsigned int>::iterator pfi;
		for (pfi = pf.begin (); pfi != pf.end (); pfi++)
		{
			DEBUG ("\n\t%d->f=%d->%d", variable, f, *pfi);
		}
	}
#endif

	if (out_field_edges.find (offset) == out_field_edges.end ())
	{
		set<unsigned int> empty;
		return empty;
	}

	return out_field_edges[offset];
}

set<unsigned int> parser::
get_var_fields (set<unsigned int> & vars, unsigned int offset)
{
	set<unsigned int> var_fields;
	set<unsigned int>::iterator vi;	
	for (vi = vars.begin (); vi != vars.end (); vi++)
	{
		unsigned int v = *vi;	
		set<unsigned int> temp_var_fields = get_var_fields (v, offset);
		var_fields.insert (temp_var_fields.begin (), temp_var_fields.end ());
	}
	return var_fields;
}

set<unsigned int> parser::
get_used_pointers (basic_block current_block,
        map<unsigned int, set<unsigned int> > & points_to_pairs)
{
        set<unsigned int> used_pointers;

        if (!current_block->aux)
                return used_pointers;

        list<pair<unsigned int, bool> > parsed_data_indices =
                ((block_information *)(current_block->aux))->get_parsed_data_indices ();

        list<pair<unsigned int, bool> >::iterator it;
        for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
        {
                unsigned int index = (*it).first;
                bool is_assignment = (*it).second;
                DEBUG ("\nParsed data: index %d, bool %d, block %d, ",
                        index, is_assignment, current_block->index);

               if (is_assignment)
                {
                        constraint_t assignment = VEC_index (constraint_t, assignment_data, index);
                        DEBUG ("\nassignment index=%d, addr=%x", index, assignment);
                        constraint_expr lhs = assignment->lhs;
                        constraint_expr rhs = assignment->rhs;
                        csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, variable_data, lhs.var);
                        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, variable_data, rhs.var);
                        if (lhs.type == DEREF)
                                used_pointers.insert (lhs_variable->id);
#if RHS_POINTEES_STATS
                        if (rhs.type == SCALAR || rhs.type == DEREF)
                                used_pointers.insert (rhs_variable->id);
                        // For RHS, if ...=y->f, then compute not only
                        // pointees of y (say H), but pointees of H.f also.
                        if (rhs.type == DEREF)
                        {
                                // Obtain pointee of y (say H) and obtain H.f in var_offsets
                                DEBUG ("\nvar=%d, offset=%d", rhs_variable->id, rhs.offset);
                                set<unsigned int> rhs_pointees = points_to_pairs[rhs_variable->id];
				used_pointers.insert (rhs_pointees);
                                set<unsigned int> pointee_offsets;
                                if (rhs.offset)
                                        pointee_offsets = get_var_fields (rhs_pointees, rhs.offset);
                                used_pointers.insert (pointee_offsets.begin (), pointee_offsets.end ());
                                if (pointee_offsets.size ())
                                        DEBUG ("\nOFFSET");
                        }
#endif
                }
                else
                {
                        used_pointers.insert (index);
                        // csvarinfo_t variable = VEC_index (csvarinfo_t, variable_data, index); 
                        // RESULT ("Variable id %d, name %s, offset %llu", 
                        //      variable->id, variable->name, variable->offset); 
                }
        }
        return used_pointers;
}

void parser::
copy_csvarinfo (csvarinfo_t src, csvarinfo_t dest)
{
	dest->next = src->next;
	dest->is_unknown_size_var = src->is_unknown_size_var;
	dest->fullsize = src->fullsize;
	dest->is_full_var = src->is_full_var;
	dest->size = src->size;
	dest->decl = src->decl;
}

void parser::
save_original_varinfo (csvarinfo_t original_heap)
{
	// Return if already saved
	if (heap_to_original_info.find (original_heap->id) != heap_to_original_info.end ())
		return;

	// Save if the original info is not saved.
	csvarinfo_t save = &(heap_to_original_info[original_heap->id]);
	copy_csvarinfo (original_heap, save);

	#if DEBUG_CONTAINER
	DEBUG ("\nOriginal=id=%d, is_unknown_size=%d, fullsize=%d, size=%d, is_full_var=%d",
		original_heap->id, original_heap->is_unknown_size_var, 
		original_heap->fullsize, original_heap->size, original_heap->is_full_var);
	if (original_heap->next)
		DEBUG (", next=%s(%d)", original_heap->next->name, original_heap->next->id);

	DEBUG ("\nSaved=id=%d, is_unknown_size=%d, fullsize=%d, size=%d, is_full_var=%d",
		save->id, save->is_unknown_size_var, 
		save->fullsize, save->size, save->is_full_var);
	if (save->next)
		RESULT (", next=%s(%d)", save->next->name, save->next->id);
	#endif
}

void parser::
restore_original_varinfo (csvarinfo_t varinfo)
{
	// Return if original is not saved
	if (heap_to_original_info.find (varinfo->id) == heap_to_original_info.end ())
		return;

	// Restore if the original info is saved
	csvarinfo_t saved = &(heap_to_original_info[varinfo->id]);
	copy_csvarinfo (saved, varinfo);
}

void parser::
typecast_varinfo (csvarinfo_t original_heap, csvarinfo_t new_heap)
{
	if (!original_heap->decl)
	{
		RESULT ("\nError: original_heap->decl=NULL, heap=%s(%d)", 
			original_heap->name, original_heap->id);
	}
	if (!new_heap->decl)
	{
		RESULT ("\nError: new_heap->decl=NULL, heap=%s(%d)", 
			new_heap->name, new_heap->id);
	}

	DEBUG ("\noriginal_heap=%s(%d), typecasted=%s(%d)", 
		original_heap->name, original_heap->id, new_heap->name, new_heap->id);

	RESULT ("\nOld fields of original_heap=%s(%d)=", original_heap->name, original_heap->id);
	csvarinfo_t temp;
	for (temp = original_heap->next; temp; temp = temp->next)
		RESULT ("%s(%d),", temp->name, temp->id);
	print_node (dump_file, 0, original_heap->decl, 0);


	// Save the information of original_heap i.e. if not present already
	save_original_varinfo (original_heap);

	// Save original decl. This may be VOID * or even some non-void type.
	// Typecasting of non-void can happen due to spurious static analysis
	// or even due to the program (e.g. in svcomp benchmark).
	unsigned int alloc_site = heap_to_alloc_site[original_heap->id];
	alloc_site_typecasts[alloc_site].insert (original_heap->decl);


	// new_heap is varinfo that originally had heap_decl type of tree. Note
	// that currently new_heap->decl may not be heap_decl. Therefore, we
	// should not save information from new_heap but its saved original
	// heap (if any). 
	if (heap_to_original_info.find (new_heap->id) != heap_to_original_info.end ())
		new_heap = &(heap_to_original_info[new_heap->id]);

	copy_csvarinfo (new_heap, original_heap);

	// We save all the typecasted types of void* heap in alloc_site_typecasts.
	alloc_site_typecasts[alloc_site].insert (original_heap->decl);

	#if DEBUG_CONTAINER
	print_alloc_site_typecasts ();
	#endif

	RESULT ("\nNew fields of original_heap=%s(%d)=", original_heap->name, original_heap->id);
	for (temp = original_heap->next; temp; temp = temp->next)
		RESULT ("%s(%d),", temp->name, temp->id);
	print_node (dump_file, 0, original_heap->decl, 0);

	// original_heap saves typecasted decl. new_heap continues to store the
	// typecasted decl. cs_lookup_vi_for_tree() continues to fetch new_heap
	// for heap_pointer_type/heap_decl. 
	// Explanation: The typecasted type needs to be saved in new_heap
	// because original_heap may end up losing this information if it gets
	// typecasted again; root of this typecasted structure should be saved
	// in some variable (new_heap) so that cs_lookup_vi_for_tree() should
	// return new_heap. The typecasted structure is required for finding
	// reachable nodes or field nodes of root (which will always remain
	// stored in new_heap). We use alloc_site_typecasts to know the
	// typecasted types. 

//	new_heap->next = NULL;
//	new_heap->decl = NULL;
//
//	void **slot = pointer_map_contains (vi_for_tree, original_heap->decl);
//	if (!slot)
//	{
//		RESULT ("\nError: New field offset variables should be created only if they did not already exist");
//		return NULL;
//	}
//	*slot = original_heap;
//
//	#if DEBUG_CONTAINER
//	csvarinfo_t var = cs_lookup_vi_for_tree (original_heap->decl);
//	DEBUG ("\nFound heap %d", var->id);
//	#endif
}

void parser::
cs_lookup_vi_for_typecasts (unsigned int var, set<csvarinfo_t> & var_typecasts)
{
	// If var has not been typecasted
	csvarinfo_t var_info = VEC_index (csvarinfo_t, variable_data, var);
	var_typecasts.insert (var_info);

	// If var has been typecasted
	set<tree> types = get_alloc_site_typecasts (var);

	set<tree>::iterator ti;
	for (ti = types.begin (); ti != types.end (); ti++)
	{
		csvarinfo_t root = cs_lookup_vi_for_tree (*ti);
		if (root)
		{
			// cs_lookup_vi_for_tree returns the varinfo that originally
			// had t type of tree. Note that currently root->decl
			// may not be t. Restore the original root->decl for
			// which root has been fetched.
			restore_original_varinfo (root);
			var_typecasts.insert (root);
		}
	}

#if DEBUG_CONTAINER
	DEBUG ("\ncs_lookup_vi_for_typecasts (var=%s(%d))=", var_info->name, var_info->id);
	set<csvarinfo_t>::iterator ri;
	for (ri = var_typecasts.begin (); ri != var_typecasts.end (); ri++)
	{
		csvarinfo_t r = *ri;
		DEBUG ("%s(%d),", r->name, r->id);
	}
#endif
}

#if 0
/* Create a new artificial heap variable with NAME.
   Return the created variable.  */

csvarinfo_t parser::
cs_make_heapvar_for (csvarinfo_t lhs, const char *name, basic_block bb, struct cgraph_node * cnode)
{
  csvarinfo_t vi;
  tree heapvar;
  const char *newname = "NULL";
  char *tempname;

  // C type 'void *' is ptr_type_node
  heapvar = build_fake_var_decl (ptr_type_node);
  DECL_EXTERNAL (heapvar) = 1;

  /* Append 'heap' with the its index in csvarinfo. */
  asprintf (&tempname, "%s.%d", name, VEC_length (csvarinfo_t, csvarmap));
  newname = ggc_strdup (tempname);

  vi = cs_new_var_info (heapvar, newname, cnode);
  //vi->is_artificial_var = true;
  vi->is_heap_var = true;
  vi->is_unknown_size_var = true;
  vi->offset = 0;
  vi->fullsize = ~0;
  vi->size = ~0;
  vi->is_full_var = true;
  cs_insert_vi_for_tree (heapvar, vi);

  return vi;
}

// Function created by Vini from cs_make_heapvar_for()
/* Create a new artificial heap variable with NAME.
   Return the created variable.  */
// FIXME: Simply create H.F, H.G etc when H is created in parser::variable_data.

csvarinfo_t parser::
cs_make_heapvar_offset_for (csvarinfo_t original_heap, tree heap_pointer_type, unsigned int offset, const char *name, basic_block bb, struct cgraph_node * cnode)
{
  csvarinfo_t vi;
  tree heapvar;
  const char *newname = "NULL";
  char *tempname;

  // Added by Vini. Offsets of same heap node are given the same tree decl.
  // This is required to search this new heapvar from VARIABLE_DATA. 
  // FIXME: We should set the next of original_heap to point to this newly
  // created heapvar, so that we do not waste time in searching the whole
  // VARIABLE_DATA. 
  // FIELD_CONNECT: This is also important so that H.F.I node is
  // field-connected via NEXT from H=H.F=H.F.G in generate_addressof_nodes ().
  // struct node1 { struct node2 F; }; struct node2 { int * G; int * I; };

  heapvar = original_heap->decl;
  // Commented out by Vini
  // heapvar = build_fake_var_decl (ptr_type_node);
  DECL_EXTERNAL (heapvar) = 1;

  /* Append 'heap' with the its index in csvarinfo. */
  // Added by Vini
  asprintf (&tempname, "%s.%u", name, offset);
  // Commented by Vini
  // asprintf (&tempname, "%s.%d", name, VEC_length (csvarinfo_t, csvarmap));
  newname = ggc_strdup (tempname);

  vi = cs_new_var_info (heapvar, newname, cnode);
  //vi->is_artificial_var = true;
  vi->is_heap_var = true;
  vi->is_unknown_size_var = true;
  vi->offset = offset;			// Set by Vini
  vi->fullsize = ~0;
  vi->size = ~0;
  vi->is_full_var = true;
  // Commented out by Vini. This line does not allow two variables to have the
  // same tree decl.
  // cs_insert_vi_for_tree (heapvar, vi);

  return vi;
}
#endif

/**
 * This function returns all the variables with decl equal DECL.
 */

void parser::
get_field_var_ids (tree decl, set<unsigned int> & field_ids)
{
	if (!decl)
		return;
	DEBUG ("\nget_field_var_ids (tree,...)");

	csvarinfo_t var_info = cs_lookup_vi_for_tree (decl);
	if (!var_info)
		return;
	// Return if variable does not have any fields
	if (!var_info->offset && !var_info->next)
		return;
	unsigned int var_id = var_info->id;

	// Return if variable is function. (NEXT field of function csvarinfo_t
	// is connected to its function parameter).
	if (function_var (var_info) || !is_proper_var (var_id))
		return;

	DEBUG ("\nVar connected to %s(%d): ", var_info->name, var_info->id);
	for (csvarinfo_t temp = var_info; temp; temp = temp->next)
	{
		DEBUG ("%s(%d),", temp->name, temp->id);
		field_ids.insert (temp->id);
	}
}

/**
 * This function fetches the DECL of VAR_ID (from its csvarinfo_t which may
 * have non-zero offset) and then calls GET_FIELD_VAR_IDS(TREE, ...) which then
 * finds back the csvarinfo_t of offset=0.
 */

void parser::
get_field_var_ids (unsigned int var_id, set<unsigned int> & field_ids)
{
	csvarinfo_t var_info = VEC_index (csvarinfo_t, variable_data, var_id);
	if (!var_info)
		return;
	if (!var_info->decl)
		return;

	// Return if variable is function. (NEXT field of function csvarinfo_t
	// is connected to its function parameter).
	if (function_var (var_info) || !is_proper_var (var_id))
		return;

	DEBUG ("\nvar_id=%s(%d==%d)", var_info->name, var_info->id, var_id);

	// All y.0, y.32, y.64 have the same decl. If var_info is for y.32, we
	// want to find all y.0, y.32, y.64. Therefore, pass the decl.
	get_field_var_ids (var_info->decl, field_ids);
}

void parser::
get_field_var_ids (set<unsigned int> & var_ids, set<unsigned int> & field_ids)
{
	set<unsigned int>::iterator vi;
	for (vi = var_ids.begin (); vi != var_ids.end (); vi++)
		get_field_var_ids (*vi, field_ids);
}

void parser::
get_prev_field_var_ids (unsigned int var_id, set<unsigned int> & field_ids)
{
	csvarinfo_t var_info = VEC_index (csvarinfo_t, variable_data, var_id);
	if (!var_info)
		return;
	if (!var_info->decl)
		return;

	// Return if variable is function. (NEXT field of function csvarinfo_t
	// is connected to its function parameter).
	if (function_var (var_info) || !is_proper_var (var_id))
		return;

	csvarinfo_t root_info = cs_lookup_vi_for_tree (var_info->decl);
	if (!root_info)
		return;
	// Return if variable does not have any fields
	if (!root_info->offset && !root_info->next)
		return;
	unsigned int root_id = root_info->id;

	// Return if variable is function. (NEXT field of function csvarinfo_t
	// is connected to its function parameter).
	if (function_var (root_info) || !is_proper_var (root_id))
		return;

	// Root should not be typecasted because we want to find the fields
	// reaching only var_info->decl and not its typecast.

	DEBUG ("\nVar connected to %s(%d): ", var_info->name, var_info->id);
	for (csvarinfo_t temp = root_info; temp; temp = temp->next)
	{
		if (temp->offset > var_info->offset)
			break;
		DEBUG ("%s(%d),", temp->name, temp->id);
		field_ids.insert (temp->id);
	}
}


/**
 * If VAR_ID is y.32, then return y.64. If next field does not exist, it
 * returns VAR_ID. This function is applicable to stack and heap nodes only. In
 * case of globals, VAR_ID is returned.
 */

unsigned int parser::
get_next_field (unsigned int var_id)
{
	csvarinfo_t var_info = VEC_index (csvarinfo_t, variable_data, var_id);
	if (!var_info)
		return var_id;

	if (var_info->is_global_var || !is_proper_var (var_id))
		return var_id;
	DEBUG ("\nvar_id=%s(%d==%d)", 
		var_info->name, var_info->id, var_id);

	csvarinfo_t next_field = var_info->next;
	if (next_field)
	{
		DEBUG ("\nnext_field=%s(%d)", 
			next_field->name, next_field->id);
		return next_field->id;
	}
	DEBUG ("\nnext_field not found");
	return var_id;
}

// Added by Vini
void parser::
get_offset_sequence (tree ref, list<unsigned int> & offset_sequence)
{
	// This ref is of the type x->f and not x.f if x is COMPONENT_REF.
	if (TREE_CODE (ref) == COMPONENT_REF)
	{
		// RESULT ("\n");
		tree subtree = TREE_OPERAND (ref, 0);
		tree offset = TREE_OPERAND (ref, 1);
		
		if (TREE_CODE (offset) == FIELD_DECL)
		{
			DEBUG ("\nbit-pos=%lld\n", int_bit_position (offset));
			// print_node_brief (dump_file, 0, offset, 0);
			get_offset_sequence (subtree, offset_sequence);
			offset_sequence.push_back (int_bit_position (offset));
		}
	}
}

// Added by Vini
void parser::
copy_offset_sequence (list<unsigned int> ** dest, list<unsigned int> & src)
{
	DEBUG ("\ncopy_offset_sequence");
	*dest = new list<unsigned int>;
	DEBUG ("\nAllocate offset_sequence %x", *dest);
	(**dest) = src;
}

// Added by Vini
void parser::
append_offset_sequence (list<unsigned int> ** dest, list<unsigned int> & src)
{
	if (!*dest)
	{
		copy_offset_sequence (dest, src);
		return;
	}
	DEBUG ("\nappend_offset_sequence");
	list<unsigned int>::iterator si;
	for (si = src.begin (); si != src.end (); si++)
		(**dest).push_back (*si);
}

// Added by Vini
void parser::
print_offset_sequence (list<unsigned int> * offset_sequence)
{
	DEBUG ("\nOffset-sequence (addr=%x): ", offset_sequence);
	list<unsigned int>::iterator si;
	for (si = (*offset_sequence).begin (); si != (*offset_sequence).end (); si++)
		DEBUG ("%lld,", *si);
}

/* Create a constraint ID = &FROM. */
void parser::
cs_make_constraint_from (csvarinfo_t vi, int from, basic_block bb)
{
   struct constraint_expr lhs, rhs;

   lhs.var = vi->id;
   lhs.offset = 0;
   lhs.type = SCALAR;

   rhs.var = from;
   rhs.offset = 0;
   rhs.type = ADDRESSOF;
   cs_process_constraint (new_constraint (lhs, rhs), bb);
}

/* Create a new artificial heap variable with NAME and make a
   constraint from it to LHS.  Return the created variable.  */
csvarinfo_t parser::
cs_make_constraint_from_heapvar (tree lhs, const char *name, basic_block bb, struct cgraph_node * cnode)
{
   csvarinfo_t vi = cs_make_heapvar_for (lhs, name, bb, cnode);
   csvarinfo_t lhs_var = cs_get_vi_for_tree (lhs, bb, cnode);
   cs_make_constraint_from (lhs_var, vi->id, bb);

   return vi;
}

/* Find the first varinfo in the same variable as START that overlaps with
   OFFSET.  If there is no such varinfo the varinfo directly preceding
   OFFSET is returned.  */
csvarinfo_t parser::				/* Look into */
cs_first_or_preceding_vi_for_offset (csvarinfo_t start,
				  unsigned HOST_WIDE_INT offset)
{
   /* If we cannot reach offset from start, lookup the first field
      and start from there.  */
   if (start->offset > offset)
       start = cs_lookup_vi_for_tree (start->decl);

   /* We may not find a variable in the field list with the actual
      offset when when we have glommed a structure to a variable.
      In that case, however, offset should still be within the size
      of the variable.
      If we got beyond the offset we look for return the field
      directly preceding offset which may be the last field.  */
   while (start->next && offset >= start->offset
	 && !((offset - start->offset) < start->size))
       start = start->next;
  
   return start;
}

/* Dereference the constraint expression CONS, and return the result.
   DEREF (ADDRESSOF) = SCALAR
   DEREF (SCALAR) = DEREF
   DEREF (DEREF) = (temp = DEREF1; result = DEREF(temp))
   This is needed so that we can handle dereferencing DEREF constraints.  */
void parser::
cs_do_deref (VEC (ce_s, heap) **constraints, basic_block bb, struct cgraph_node * cnode)
{
   DEBUG ("\ncs_do_deref()");
   struct constraint_expr *c;
   unsigned int i = 0;

   FOR_EACH_VEC_ELT (ce_s, *constraints, i, c) {
	// Added by Pritam
	// c->pointer_arithmetic = false;
       if (c->type == SCALAR)
       {
	   DEBUG ("\nSCALAR -> DEREF");
	   c->type = DEREF;
       }
       else if (c->type == ADDRESSOF)
       {
	   DEBUG ("\nADDRESSOF -> SCALAR");
	   c->type = SCALAR;
       }
       else if (c->type == DEREF) 
       {
	   DEBUG ("\nDEREF");
	   struct constraint_expr tmplhs;
	   tmplhs = cs_new_scalar_tmp_constraint_exp ("dereftmp", cnode);
	   cs_process_constraint (new_constraint (tmplhs, *c), bb);
	   c->var = tmplhs.var;
       }
       else
	   gcc_unreachable ();
   }
}

/* Get constraint expressions for offsetting PTR by OFFSET.  Stores the
   resulting constraint expressions in *RESULTS.  */
void parser::
cs_get_constraint_for_ptr_offset (tree ptr, tree offset,
       VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
   DEBUG ("\ncs_get_constraint_for_ptr_offset()");
   struct constraint_expr c;
   unsigned int j, n;
   HOST_WIDE_INT rhsunitoffset, rhsoffset;

   if (offset == NULL_TREE || !host_integerp (offset, 0))
   {
       rhsoffset = UNKNOWN_OFFSET;
       DEBUG ("\nUNKNOWN_OFFSET used in cs_get_constraint_for_ptr_offset() --1");
   }
   else {
       DEBUG ("\nin else of cs_get_constraint_for_ptr_offset()");
       /* Make sure the bit-offset also fits.  */
       rhsunitoffset = TREE_INT_CST_LOW (offset);
       rhsoffset = rhsunitoffset * BITS_PER_UNIT;
       if (rhsunitoffset != rhsoffset / BITS_PER_UNIT)
       {
	   rhsoffset = UNKNOWN_OFFSET;
           DEBUG ("\nUNKNOWN_OFFSET used in cs_get_constraint_for_ptr_offset() --1");
       }
	DEBUG ("\noffset %llu, rhsoffset %llu", offset, rhsoffset);
   }

   cs_get_constraint_for_rhs (ptr, results, bb, cnode);
   if (rhsoffset == 0)
       return;

   /* As we are eventually appending to the solution do not use
      VEC_iterate here. */
   n = VEC_length (ce_s, *results);
   for (j = 0; j < n; j++) {
       csvarinfo_t curr;
       c = *VEC_index (ce_s, *results, j);
       curr = cs_get_varinfo (c.var);

       /* If this varinfo represents a full variable just use it. */
       if (c.type == ADDRESSOF && curr->is_full_var)
       {
	   c.offset = 0;
	   // Added by Pritam
	   // c.pointer_arithmetic = false;
       }
       /* If we do not know the offset add all subfields. */
       else if (c.type == ADDRESSOF && rhsoffset == UNKNOWN_OFFSET) {
	   csvarinfo_t temp = cs_lookup_vi_for_tree (curr->decl);
	   do {
	       struct constraint_expr c2;
	       c2.var = temp->id;
	       c2.type = ADDRESSOF;
	       c2.offset = 0;
	       if (c2.var != c.var)
	       {
		   // Added by Pritam
		   // c2.pointer_arithmetic = false;
		   DEBUG ("\npush c2");
		   VEC_safe_push (ce_s, heap, *results, &c2);
	       }
	       temp = temp->next;
	   } while (temp);
       }
       else if (c.type == ADDRESSOF) {
	   csvarinfo_t temp;
	   unsigned HOST_WIDE_INT offset = curr->offset + rhsoffset;

	   /* Search the sub-field which overlaps with the
	      pointed-to offset.  If the result is outside of the variable
	      we have to provide a conservative result, as the variable is
	      still reachable from the resulting pointer (even though it
	      technically cannot point to anything).  The last and first
	      sub-fields are such conservative results.
	      ???  If we always had a sub-field for &object + 1 then
	      we could represent this in a more precise way.  */
	   if (rhsoffset < 0 && curr->offset < offset)
	       offset = 0;
	   temp = cs_first_or_preceding_vi_for_offset (curr, offset);

	   /* If the found variable is not exactly at the pointed to
	     result, we have to include the next variable in the
	     solution as well.  Otherwise two increments by offset / 2
	     do not result in the same or a conservative superset
	     solution.  */
	   if (temp->offset != offset && temp->next != NULL) {
	       struct constraint_expr c2;
	       c2.var = temp->next->id;
	       c2.type = ADDRESSOF;
	       c2.offset = 0;
	       // Added by Pritam
	       // c2.pointer_arithmetic = false;
	       DEBUG ("\npush c2");
	       VEC_safe_push (ce_s, heap, *results, &c2);
	   }
	   c.var = temp->id;
	   // Added by Pritam
	   // c.pointer_arithmetic = false;
	   c.offset = 0;
       }
       else
       {
	   c.offset = rhsoffset;
	   // Added by Pritam
	   c.pointer_arithmetic = true;
	   DEBUG ("\nc.var=%d, ptr_arith=1", c.var);
       }

       VEC_replace (ce_s, *results, j, &c);
   }
}

/* Given a COMPONENT_REF T, return the constraint_expr vector for it.
   If address_p is true the result will be taken its address of.
   If lhs_p is true then the constraint expression is assumed to be used
   as the lhs.  */
void parser::
cs_get_constraint_for_component_ref (tree t, VEC(ce_s, heap) **results,
				  bool address_p, bool lhs_p, basic_block bb, struct cgraph_node * cnode)
{
   DEBUG ("\ncs_get_constraint_for_component_ref");

   tree orig_t = t;
   HOST_WIDE_INT bitsize = -1;
   HOST_WIDE_INT bitmaxsize = -1;
   HOST_WIDE_INT bitpos;
   tree forzero;
   struct constraint_expr *result;

   /* Some people like to do cute things like take the address of
     &0->a.b */
   forzero = t;
   while (handled_component_p (forzero)
	 || INDIRECT_REF_P (forzero)
	 || TREE_CODE (forzero) == MEM_REF)
       forzero = TREE_OPERAND (forzero, 0);

   if (CONSTANT_CLASS_P (forzero) && integer_zerop (forzero)) {
       struct constraint_expr temp;
       temp.offset = 0;
       temp.var = readonly_id;
       temp.type = SCALAR;
       // Added by Pritam
       // temp.pointer_arithmetic = false;
       DEBUG ("\npush temp");
       VEC_safe_push (ce_s, heap, *results, &temp);
       return;
   }

   /* Handle type-punning through unions. If we are extracting a pointer
      from a union via a possibly type-punning access that pointer
      points to anything, similar to a conversion of an integer to
      a pointer.  */
   if (!lhs_p) {
      tree u;
      for (u = t;
	   TREE_CODE (u) == COMPONENT_REF || TREE_CODE (u) == ARRAY_REF;
	   u = TREE_OPERAND (u, 0))
	if (TREE_CODE (u) == COMPONENT_REF
	    && TREE_CODE (TREE_TYPE (TREE_OPERAND (u, 0))) == UNION_TYPE) 
 	{
            DEBUG ("\nUNION not handled");
	/*
	    // Commented out by Prashant
            struct constraint_expr temp;

            temp.offset = 0;
            temp.var = anything_id;
            temp.type = ADDRESSOF;
            VEC_safe_push (ce_s, heap, *results, &temp);
	*/

	    // Commented by Vini: Do not ignore unions
            // return;
        }
   }

   // The offset is lost after calling get_ref_base_and_extent(). We want to
   // recursively traverse the nested offset sequence if t contains dereference
   // through -> i.e. result->type==DEREF. Therefore, we save the tree in
   // ORIG_TREE here and compute the offset-sequence only if
   // result->type==DEREF below.
   tree orig_tree = t;
   t = get_ref_base_and_extent (t, &bitpos, &bitsize, &bitmaxsize);
   DEBUG ("\nvar=%s, bitpos=%lld, bitsize=%lld, bitmaxsize=%lld\n", 
       get_name (t), bitpos, bitsize, bitmaxsize);

   // print_node (dump_file, 0, t, 0);

   /* Pretend to take the address of the base, we'll take care of
      adding the required subset of sub-fields below.  */
   cs_get_constraint_for_1 (t, results, true, lhs_p, bb, cnode);
   if (VEC_length (ce_s, *results) == 0)
       return;
   else
       gcc_assert (VEC_length (ce_s, *results) == 1);
   
   result = VEC_last (ce_s, *results);
   // Added by Pritam
   // result->pointer_arithmetic = false;
#if DEBUG_CONTAINER
   DEBUG ("\nafter cs_get_constraint_for_1()");
   struct constraint_expr *rhsp;
   unsigned j;
   FOR_EACH_VEC_ELT (ce_s, *results, j, rhsp) {
      DEBUG ("\nrhsp %d offset %llu\n", rhsp->var, rhsp->offset);
   }
#endif

   if (result->type == SCALAR
       && cs_get_varinfo (result->var)->is_full_var)
       /* For single-field vars do not bother about the offset.  */
       result->offset = 0;
   else if (result->type == SCALAR) {
      /* In languages like C, you can access one past the end of an
	 array.  You aren't allowed to dereference it, so we can
	 ignore this constraint. When we handle pointer subtraction,
	 we may have to do something cute here.  */

      if ((unsigned HOST_WIDE_INT)bitpos < cs_get_varinfo (result->var)->fullsize
	  && bitmaxsize != 0) {
	  /* It's also not true that the constraint will actually start at the
	     right offset, it may start in some padding.  We only care about
	     setting the constraint to the first actual field it touches, so
	     walk to find it.  */
	  struct constraint_expr cexpr = *result;
	  csvarinfo_t curr;
	  VEC_pop (ce_s, *results);
	  cexpr.offset = 0;
	  for (curr = cs_get_varinfo (cexpr.var); curr; curr = curr->next) {
	      if (ranges_overlap_p (curr->offset, curr->size,
				    bitpos, bitmaxsize)) {
		  cexpr.var = curr->id;
                  // Added by Pritam
                  // cexpr.pointer_arithmetic = false;
		  DEBUG ("\ncexpr.var=%d curr->offset=%lld", cexpr.var);
		  VEC_safe_push (ce_s, heap, *results, &cexpr);
		  if (address_p)
		     break;
	       }
	   }
	   /* If we are going to take the address of this field then
	      to be able to compute reachability correctly add at least
	      the last field of the variable.  */
	   if (address_p && VEC_length (ce_s, *results) == 0) {
	       curr = cs_get_varinfo (cexpr.var);
	       while (curr->next)
		   curr = curr->next;
	       cexpr.var = curr->id;
	       // Added by Pritam
               // cexpr.pointer_arithmetic = false;
               DEBUG ("\npush cexpr");
	       VEC_safe_push (ce_s, heap, *results, &cexpr);
#if DEBUG_CONTAINER
		DEBUG ("\naddress_p");
               struct constraint_expr *rhsp;
               unsigned j;
               FOR_EACH_VEC_ELT (ce_s, *results, j, rhsp) {
                  DEBUG ("\nrhsp %d offset %llu\n", rhsp->var, rhsp->offset);
               }
#endif
	   }
	   /*
           // Commented out by Prashant
	   else if (VEC_length (ce_s, *results) == 0)
            // Assert that we found *some* field there. The user couldn't be
            // accessing *only* padding.
            // Still the user could access one past the end of an array
            // embedded in a struct resulting in accessing *only* padding.
            // Or accessing only padding via type-punning to a type
            // that has a filed just in padding space.
            {
              cexpr.type = SCALAR;
              cexpr.var = anything_id;
              cexpr.offset = 0;
              VEC_safe_push (ce_s, heap, *results, &cexpr);
            }
	    */
       }
       else if (bitmaxsize == 0) {
	  if (dump_file && (dump_flags & TDF_DETAILS))
	      DEBUG ("Access to zero-sized part of variable, ignoring\n");
       }
       else
	  if (dump_file && (dump_flags & TDF_DETAILS))
	     DEBUG ("Access to past the end of variable, ignoring\n");
   }
   else if (result->type == DEREF) {
      /* If we do not know exactly where the access goes say so.  Note
	 that only for non-structure accesses we know that we access
	 at most one subfiled of any variable.  */
       // Vini: 
       if (bitpos == -1 || bitsize != bitmaxsize || result->offset == UNKNOWN_OFFSET)
       {
	   result->offset = UNKNOWN_OFFSET;
           DEBUG ("\nUNKNOWN_OFFSET used in cs_get_constraint_for_component_ref ()");
       }
	/* Look into : Structure variables */
	// Vini: Used when x->f is a record type and NOT a pointer
       else if (AGGREGATE_TYPE_P (TREE_TYPE (orig_t)))
       {
	   DEBUG ("\nAGGREGATE_TYPE_P (orig_t)");
	   result->offset = bitpos;
	   list<unsigned int> offset_sequence;
	   get_offset_sequence (orig_tree, offset_sequence);
           copy_offset_sequence (&result->offset_sequence, offset_sequence);
	   print_offset_sequence (result->offset_sequence);
	   DEBUG ("\nresult->offset=bitpos=%lld", bitpos);
       }
       else
       {
	   DEBUG ("\n!!! AGGREGATE_TYPE_P (orig_t)");
	   if (result->offset)
		DEBUG ("\nError:? hmmm interesting");
	   result->offset += bitpos;
	   list<unsigned int> offset_sequence;
	   get_offset_sequence (orig_tree, offset_sequence);
           append_offset_sequence (&result->offset_sequence, offset_sequence);
	   print_offset_sequence (result->offset_sequence);
	   DEBUG ("\nresult->offset=%lld,bitpos=%lld", result->offset, bitpos);
       }
   }
   else
       gcc_unreachable ();
}

/* Get a constraint expression vector from an SSA_VAR_P node.
   If address_p is true, the result will be taken its address of.  */
void parser::
cs_get_constraint_for_ssa_var (tree t, VEC(ce_s, heap) **results, bool address_p, basic_block bb, struct cgraph_node * cnode)
{
   DEBUG ("\ncs_get_constraint_for_ssa_var");
   struct constraint_expr cexpr;
   csvarinfo_t vi;

   /* We allow FUNCTION_DECLs here even though it doesn't make much sense. */
   gcc_assert (SSA_VAR_P (t) || DECL_P (t));

   DEBUG ("\ngcc_assert() saved");

   /* For parameters, get at the points-to set for the actual parm decl. */
   if (TREE_CODE (t) == SSA_NAME
       && (TREE_CODE (SSA_NAME_VAR (t)) == PARM_DECL
 	  || TREE_CODE (SSA_NAME_VAR (t)) == RESULT_DECL)
       && SSA_NAME_IS_DEFAULT_DEF (t)) {
       DEBUG ("\nssa again"); 
       cs_get_constraint_for_ssa_var (SSA_NAME_VAR (t), results, address_p, bb, cnode);

       return;
   }

   vi = cs_get_vi_for_tree (t, bb, cnode);
   cexpr.var = vi->id;
   DEBUG ("\nIn cs_get_constraint_for ssa_var: vi %s, id %d, offset %llu\n", 
	vi->name, vi->id, vi->offset);
   DEBUG ("\nIndex of variable %d",vi->id);

   cexpr.type = SCALAR;
   // Added by Pritam
   // cexpr.pointer_arithmetic = false;
   cexpr.offset = 0;

   /* If we are not taking the address of the constraint expr, add all
      sub-fiels of the variable as well.  */
   if (!address_p)
   {
	DEBUG ("\n!address_p");
   }
   if (!vi->is_full_var)
   {
	DEBUG ("\n!vi->is_full_var");
   }
   else
   {
	DEBUG ("\nvi->is_full_var");
   }

   if (!address_p && !vi->is_full_var) {
      for (; vi; vi = vi->next) {
	   cexpr.var = vi->id;
	  
           DEBUG ("\nIndex of variable in loop %d",vi->id);

	   VEC_safe_push (ce_s, heap, *results, &cexpr);
      }
      DEBUG ("\nEnd of loop");
      return;
   }

   DEBUG ("\nPushing cexpr.var=%d", cexpr.var);
   VEC_safe_push (ce_s, heap, *results, &cexpr);
}

/* Given a tree T, return the constraint expression for it.  */
void parser::
cs_get_constraint_for_1 (tree t, VEC (ce_s, heap) **results, bool address_p,
		      bool lhs_p, basic_block bb, struct cgraph_node * cnode)
{
   DEBUG ("\ncs_get_constraint_for_1");
   struct constraint_expr temp;

   /* x = integer is all glommed to a single variable, which doesn't
     point to anything by itself.  That is, of course, unless it is an
     integer constant being treated as a pointer, in which case, we
     will return that this is really the addressof anything.  This
     happens below, since it will fall into the default case. The only
     case we know something about an integer treated like a pointer is
     when it is the NULL pointer, and then we just say it points to
     NULL.

     Do not do that if -fno-delete-null-pointer-checks though, because
     in that case *NULL does not fail, so it _should_ alias *anything.
     It is not worth adding a new option or renaming the existing one,
     since this case is relatively obscure.  */
   if ((TREE_CODE (t) == INTEGER_CST && integer_zerop (t))
      /* The only valid CONSTRUCTORs in gimple with pointer typed
	 elements are zero-initializer.  But in IPA mode we also
	 process global initializers, so verify at least.  */
      || (TREE_CODE (t) == CONSTRUCTOR
	  && CONSTRUCTOR_NELTS (t) == 0)) {
       if (flag_delete_null_pointer_checks) {
	   temp.var = null_id;
           temp.type = ADDRESSOF;
           temp.offset = 0;
           // Added by Pritam
           // temp.pointer_arithmetic = false;
	   DEBUG ("\nnull pointer");

           VEC_safe_push (ce_s, heap, *results, &temp);
       }
       return;
   }

  /* String constants are read-only. Don't consider them. 
   if (TREE_CODE (t) == STRING_CST)
       return;*/

   /* String constants are read-only. */
   if (TREE_CODE (t) == STRING_CST) {
      temp.var = readonly_id;
      temp.type = SCALAR;
      temp.offset = 0;
      // Added by Pritam
      // temp.pointer_arithmetic = false;
      VEC_safe_push (ce_s, heap, *results, &temp);
      return;
   }

   switch (TREE_CODE_CLASS (TREE_CODE (t))) {
       case tcc_expression:
       {
           switch (TREE_CODE (t)) {
	       case ADDR_EXPR:
	 	   DEBUG ("\nADDR_EXPR");

	           cs_get_constraint_for_address_of (TREE_OPERAND (t, 0), results, bb, cnode);
	           return;
	        default:;
	   }
 	   break;
       }
       case tcc_reference:
       {
	   switch (TREE_CODE (t)) {
	       case MEM_REF:
	       {
	 	   DEBUG ("\nMEM_REF");
	           struct constraint_expr cs;
	      	   csvarinfo_t vi, curr;
	           tree off = double_int_to_tree (sizetype, mem_ref_offset (t));
	      	   cs_get_constraint_for_ptr_offset (TREE_OPERAND (t, 0), off, results, bb, cnode);
                   if (VEC_length (ce_s, *results) == 0)
                       return;
	      	   cs_do_deref (results, bb, cnode);

	           /* If we are not taking the address then make sure to process
		      all subvariables we might access.  */
	      	   cs = *VEC_last (ce_s, *results);
                   DEBUG ("\ncs.var=%d, cs.ptr_arith=%d", cs.var, cs.pointer_arithmetic);
		   // Added by Pritam
	           // cs.pointer_arithmetic = false;
	      	   if (address_p || cs.type != SCALAR)
		       return;

	      	   vi = cs_get_varinfo (cs.var);
	      	   curr = vi->next;
	      	   if (!vi->is_full_var && curr) {
		       unsigned HOST_WIDE_INT size;
		       if (host_integerp (TYPE_SIZE (TREE_TYPE (t)), 1))
		           size = TREE_INT_CST_LOW (TYPE_SIZE (TREE_TYPE (t)));
		       else
		           size = -1;
		       for (; curr; curr = curr->next) {
		      	   if (curr->offset - vi->offset < size) {
			       cs.var = curr->id;
			       VEC_safe_push (ce_s, heap, *results, &cs);
			   }
		           else
			       break;
		       }
		   }
	           return;
	       }
	       case ARRAY_REF:
	       case ARRAY_RANGE_REF:
	       case COMPONENT_REF:
	 	   DEBUG ("\nARRAY_REF|ARRAY_RANGE_REF|COMPONENT_REF");
	           cs_get_constraint_for_component_ref (t, results, address_p, lhs_p, bb, cnode);
#if DEBUG_CONTAINER
                   DEBUG ("\nafter ARRAY_REF|ARRAY_RANGE_REF|COMPONENT_REF");
  		   struct constraint_expr *rhsp;
		   unsigned j;
                   FOR_EACH_VEC_ELT (ce_s, *results, j, rhsp) {
	              DEBUG ("\nrhsp %d offset %llu\n", rhsp->var, rhsp->offset);
		   }
#endif

	           return;
	       case VIEW_CONVERT_EXPR:
	 	   DEBUG ("\nVIEW_CONVERT_EXPR");
	           cs_get_constraint_for_1 (TREE_OPERAND (t, 0), results, address_p, lhs_p, bb, cnode);
	    	   return;
	       /* We are missing handling for TARGET_MEM_REF here.  */
	       default:;
	   }
	   break;
       }
       case tcc_exceptional:
       {
	   switch (TREE_CODE (t)) {
	       case SSA_NAME:
	       {
	 	   DEBUG ("\nSSA_NAME");
		   cs_get_constraint_for_ssa_var (t, results, address_p, bb, cnode);
	           return;
	       }
	       case CONSTRUCTOR:
	       {
	 	   DEBUG ("\nCONSTRUCTOR");
	           unsigned int i;
	      	   tree val;
	      	   VEC (ce_s, heap) *tmp = NULL;
	      	   FOR_EACH_CONSTRUCTOR_VALUE (CONSTRUCTOR_ELTS (t), i, val) {
		       struct constraint_expr *rhsp;
		       unsigned j;
		       cs_get_constraint_for_1 (val, &tmp, address_p, lhs_p, bb, cnode);
		       FOR_EACH_VEC_ELT (ce_s, tmp, j, rhsp)
		           VEC_safe_push (ce_s, heap, *results, rhsp);
		       VEC_truncate (ce_s, tmp, 0);
		   }
	           VEC_free (ce_s, heap, tmp);
	           /* We do not know whether the constructor was complete,
	              so technically we have to add &NOTHinG or &ANYTHinG
		      like we do for an empty constructor as well.  */
	           return;
	       }
	       default:;
	   }
	   break;
       }
       case tcc_declaration:
       {
	   DEBUG ("\ntcc_declaration");
	   cs_get_constraint_for_ssa_var (t, results, address_p, bb, cnode);
	   return;
       }
       case tcc_constant:
	   DEBUG ("\ntcc_constant");
	   return;
       default:;
   }
}



/* Efficiently generates constraints from all entries in *RHSC to all
   entries in *LHSC.  */
void parser::
cs_process_all_all_constraints (VEC (ce_s, heap) *lhsc, VEC (ce_s, heap) *rhsc, basic_block bb)
{
   struct constraint_expr *lhsp, *rhsp;
   unsigned i, j;

#if DEBUG_CONTAINER
   DEBUG ("\nBefore: ");
   print_assignment_data ();
#endif

   FOR_EACH_VEC_ELT (ce_s, lhsc, i, lhsp) {
       FOR_EACH_VEC_ELT (ce_s, rhsc, j, rhsp) {
           DEBUG ("\ncs_process_all_all_constraints loop");
	   DEBUG ("\nlhsp %d offset %llu, rhsp %d offset %llu\n", 
		lhsp->var, lhsp->offset, rhsp->var, rhsp->offset);
//	   print_variable_data (lhsp->var);
//	   DEBUG ("\n");
//	   print_variable_data (rhsp->var);
	
	   cs_process_constraint (new_constraint (*lhsp, *rhsp), bb);
           multi_rhs = true;
       }
       multi_rhs = false;
   }
#if DEBUG_CONTAINER
   DEBUG ("\nAfter: ");
   print_assignment_data ();
#endif
}

/* Given a tree T, return the constraint expression for taking the
   address of it. */
void parser::
cs_get_constraint_for_address_of (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
   struct constraint_expr *c;
   unsigned int i;
   DEBUG ("\ncs_get_constraint_for_address_of");

   cs_get_constraint_for_1 (t, results, true, true, bb, cnode);
   FOR_EACH_VEC_ELT (ce_s, *results, i, c) {
       if (c->type == DEREF)
	   c->type = SCALAR;
       else
	   c->type = ADDRESSOF;
       // Added by Pritam
       // c->pointer_arithmetic = false;
   }
}

/* Given a gimple tree T, return the constraint expression vector for it.  */
void parser::
cs_get_constraint_for (tree t, VEC (ce_s, heap) **results, basic_block bb, struct cgraph_node * cnode)
{
  gcc_assert (VEC_length (ce_s, *results) == 0);
  DEBUG ("\ncs_get_constraint_for\n");
  cs_get_constraint_for_1 (t, results, false, true, bb, cnode);
}

/* Creation function node for DECL, using NAME, and return the index
   of the variable we've created for the function.  */
csvarinfo_t parser::
cs_create_func_info_for (tree decl, const char *name, struct cgraph_node * cnode)
{
   csvarinfo_t vi, prev_vi;
   tree arg;
   unsigned int i;
   bool is_varargs = false;
   unsigned int num_args = count_num_arguments (decl, &is_varargs);
	 //DEBUG ("\nin  cs create func info for : %d",num_args);
   /* Create the variable info.  */
   vi = cs_new_var_info (decl, name, cnode);
   vi->offset = 0;
   vi->size = 1;
   vi->fullsize = num_args + 1;
   vi->may_have_pointers = false;
   if (is_varargs)
       vi->fullsize = ~0;
   cs_insert_vi_for_tree (vi->decl, vi);

   prev_vi = vi;

   /* Set up variables for each argument.  */
   arg = DECL_ARGUMENTS (decl);
   for (i = 1; i < num_args + 1; i++) {
       csvarinfo_t argvi;
       tree argdecl = decl;

       if (arg)
           argdecl = arg;

       argvi = cs_new_var_info (argdecl, alias_get_name (argdecl), cnode);
       argvi->offset = i;
       argvi->size = 1;
       argvi->is_full_var = true;
       argvi->fullsize = vi->fullsize;
       if (arg)
          argvi->may_have_pointers = true; //DEBUG ("\nmay have pointers is true");
	// Avantika puts all the below in the above IF condition, Prashant does not
       gcc_assert (prev_vi->offset < argvi->offset);
       prev_vi->next = argvi;
       prev_vi = argvi;
       if (arg) {
           cs_insert_vi_for_tree (arg, argvi);
           arg = DECL_CHAIN (arg);
       }
   }

   /* Add one representative for all further args.  */
   if (is_varargs) {
       csvarinfo_t argvi;
       const char *newname;
       char *tempname;
       tree decl;

       asprintf (&tempname, "%s.varargs", name);
       newname = ggc_strdup (tempname);
       free (tempname);

       /* CHANGE DUE TO GCC-4.7.2 */
       /* We need sth that can be pointed to for va_start.  */
       decl = build_fake_var_decl (ptr_type_node);

       /* According to gcc-4.6.*
       decl = create_tmp_var_raw (ptr_type_node, name);
       get_var_ann (decl); */

       argvi = cs_new_var_info (decl, newname, cnode);
       argvi->offset = 1 + num_args;
       argvi->size = ~0;
       argvi->is_full_var = true;
       argvi->is_heap_var = true;
       argvi->fullsize = vi->fullsize;
       gcc_assert (prev_vi->offset < argvi->offset);
       prev_vi->next = argvi;
       prev_vi = argvi;
   }

   return vi;
}

/* Find the first varinfo in the same variable as START that overlaps with
   OFFSET.  Return NULL if we can't find one.  */
/* While creating field offset variables, non-pointer member fields are merged.
 * Therefore, if a member field from the merged fields is accessed, we need to
 * find the merged field with which the accessed field overlaps. For this we
 * can use ranges_overlap_p() or cs_first_vi_for_offset().
 */
csvarinfo_t parser::
cs_first_vi_for_offset (csvarinfo_t start, unsigned HOST_WIDE_INT offset)	/* Look into */
{
   DEBUG ("\ncs_first_vi_for_offset (%s(%d), %lld)", start->name, start->id, offset);

   // Added by Prashant
   offset += start->offset;
 
   /* If the offset is outside of the variable, bail out.  */
   if (offset >= start->fullsize)
       return NULL;

   // This can never be true because of Prashant's above statement.
   /* If we cannot reach offset from start, lookup the first field
      and start from there.  */
   if (start->offset > offset)
       start = cs_lookup_vi_for_tree (start->decl);

   while (start) {
      /* We may not find a variable in the field list with the actual
         offset when when we have glommed a structure to a variable.
         In that case, however, offset should still be within the size
         of the variable. */
       if (offset >= start->offset
           && (offset - start->offset) < start->size)
           return start;

       start= start->next;
   }

   return NULL;
}

/* Handle aggregate copies by expanding into copies of the respective
   fields of the structures.  */
void parser::
cs_do_structure_copy (tree lhsop, tree rhsop, basic_block bb, struct cgraph_node * cnode)  /* Look into : Structure variables */
{
   VEC (ce_s, heap) *lhsc = NULL, *rhsc = NULL;

   DEBUG ("\ncs_do_structure_copy ()");
   cs_get_constraint_for (lhsop, &lhsc, bb, cnode);
   cs_get_constraint_for_rhs (rhsop, &rhsc, bb, cnode);

   cs_do_structure_copy (lhsop, lhsc, rhsop, rhsc, bb);
}

void parser::
cs_do_structure_copy (tree lhsop, VEC (ce_s, heap) *lhsc, 
	tree rhsop, VEC (ce_s, heap) *rhsc, 
	basic_block bb)  /* Look into : Structure variables */
{
   struct constraint_expr *lhsp, *rhsp;
   unsigned j;
   lhsp = VEC_index (ce_s, lhsc, 0);
   rhsp = VEC_index (ce_s, rhsc, 0);

   DEBUG ("\nlhs var %d, type %d, offset %ld", lhsp->var, lhsp->type, lhsp->offset);
   DEBUG ("\nrhs var %d, type %d, offset %ld", rhsp->var, rhsp->type, lhsp->offset);

   // Commented by Vini, used by Prashant
//    if (lhsp->type == DEREF)
//       return;
//    if (rhsp->type == DEREF) {
//        gcc_assert (VEC_length (ce_s, rhsc) == 1);
//        rhsp->var = undef_id;
//        rhsp->offset = 0;
//        rhsp->type = ADDRESSOF;
//        cs_process_all_all_constraints (lhsc, rhsc, bb);
//    }

   // Added by Vini
   if (lhsp->type == DEREF || rhsp->type == DEREF)
   {
     if (lhsp->type == DEREF)
       {
         gcc_assert (VEC_length (ce_s, lhsc) == 1);
	 // Why added by Vini? Creates duplicate constraint.
         // cs_process_constraint (new_constraint (*lhsp, *rhsp), bb);
	 // FIXME: *x=y should produce *x.0+32=y.0+32; *x.32+32=y.32+32
         //lhsp->offset = UNKNOWN_OFFSET;
       }
     if (rhsp->type == DEREF)
       {
         gcc_assert (VEC_length (ce_s, rhsc) == 1);
	 // Why added by Vini? Creates duplicate constraint.
         // cs_process_constraint (new_constraint (*lhsp, *rhsp), bb);
	 // FIXME: x=*y should produce x.0+32=*y.0+32; x.32+32=*y.32+32
         //rhsp->offset = UNKNOWN_OFFSET;
       }
     cs_process_all_all_constraints (lhsc, rhsc, bb);
   }

   else if (lhsp->type == SCALAR &&
            (rhsp->type == SCALAR || rhsp->type == ADDRESSOF)) {
       DEBUG ("\nSCALAR = SCALAR");
       HOST_WIDE_INT lhssize, lhsmaxsize, lhsoffset;
       HOST_WIDE_INT rhssize, rhsmaxsize, rhsoffset;
       unsigned k = 0;
       get_ref_base_and_extent (lhsop, &lhsoffset, &lhssize, &lhsmaxsize);
       get_ref_base_and_extent (rhsop, &rhsoffset, &rhssize, &rhsmaxsize);
       DEBUG ("\nVEC_length (ce_s, lhsc) = %d, VEC_length (ce_s, rhsc) = %d", VEC_length (ce_s, lhsc), VEC_length (ce_s, rhsc));
       for (j = 0; VEC_iterate (ce_s, lhsc, j, lhsp);) {
           DEBUG ("\nIterate lhs");
           csvarinfo_t lhsv, rhsv;
           rhsp = VEC_index (ce_s, rhsc, k);
           lhsv = cs_get_varinfo (lhsp->var);
           rhsv = cs_get_varinfo (rhsp->var);
	   DEBUG ("\nlhsv %s, rhsv %s", lhsv->name, rhsv->name);
          if (lhsv->may_have_pointers
               && (lhsv->is_full_var
                  || rhsv->is_full_var
                  || ranges_overlap_p (lhsv->offset + rhsoffset, lhsv->size,
                                       rhsv->offset + lhsoffset, rhsv->size)))
	   {
               DEBUG ("\nSomething... 1");
               cs_process_constraint (new_constraint (*lhsp, *rhsp), bb);
	   }
           if (!rhsv->is_full_var && (lhsv->is_full_var
                  || (lhsv->offset + rhsoffset + lhsv->size
                      > rhsv->offset + lhsoffset + rhsv->size))) {
               DEBUG ("\nSomething... 2");
               ++k;
               if (k >= VEC_length (ce_s, rhsc))
                   break;
           }
           else
	   {
               DEBUG ("\nSomething... 3");
               ++j;
           }
       }
   }
   else
   {
       DEBUG ("\nSomething... 4");
       gcc_unreachable ();	// Calls abort ()
   }

   VEC_free (ce_s, heap, lhsc);
   VEC_free (ce_s, heap, rhsc);
   DEBUG ("\nFinish cs_do_structure_copy ()");
}

void parser::
cs_init_base_vars (struct cgraph_node * cnode)
{
  // csvarinfo_t var_nothing, var_integer, var_undef;
 csvarinfo_t var_nothing, var_readonly, var_stack_deref, var_undef, var_wild_card;

   /* Create a STACK_DEREF variable, for escaped pointer values. */
   var_stack_deref = cs_new_var_info (NULL_TREE, "stack_deref", cnode);
   gcc_assert (var_stack_deref->id == stack_deref);
   var_stack_deref->offset = 0;
   var_stack_deref->size = ~0;
   var_stack_deref->fullsize = ~0;
   var_stack_deref->next = NULL;

   /* Create the READONLY variable, used to represent string constants
      and integer pointers. */
   var_readonly = cs_new_var_info (NULL_TREE, "readonly", cnode);
   gcc_assert (var_readonly->id == readonly_id);
   var_readonly->offset = 0;
   var_readonly->size = ~0;
   var_readonly->fullsize = ~0;
   var_readonly->next = NULL;

   /* Create the NULL variable, used to represent that a variable points
      to NULL.  */
   var_nothing = cs_new_var_info (NULL_TREE, "null", cnode);
   gcc_assert (var_nothing->id == null_id);
   var_nothing->offset = 0;
   var_nothing->size = ~0;
   var_nothing->fullsize = ~0;
   var_nothing->next = NULL;

   /* Create an UNKNOWN variable, for unknown pointer values. */
   var_undef = cs_new_var_info (NULL_TREE, "undef", cnode);
   gcc_assert (var_undef->id == undef_id);
   var_undef->offset = 0;
   var_undef->size = ~0;
   var_undef->fullsize = ~0;
   var_undef->next = NULL;

   /* Create the WILD_CARD variable, used to represent summary locations and wild
   card edges. */
   var_wild_card = cs_new_var_info (NULL_TREE, "wild_card", cnode);
   gcc_assert (var_wild_card->id == wild_card_id);
   var_wild_card->size = ~0;
   var_wild_card->fullsize = ~0;
   var_wild_card->offset = 0;
   var_wild_card->next = NULL;
   // Summary node may not necessarily be heap
   var_wild_card->is_heap_var = false;

   /* Create the INTEGER variable, used to represent that a variable points
     to what an INTEGER "points to".  
   var_integer = cs_new_var_info (NULL_TREE, "integer", cnode);
   gcc_assert (var_integer->id == integer_id);
   var_integer->size = ~0;
   var_integer->fullsize = ~0;
   var_integer->offset = 0;
   var_integer->next = NULL;*/

#if 0
   /* Create the UNIVERSAL variable, used to represent all locations. */
   var_universal = cs_new_var_info (NULL_TREE, "universal", cnode);
   gcc_assert (var_universal->id == universal_id);
   var_universal->size = ~0;
   var_universal->fullsize = ~0;
   var_universal->offset = 0;
   var_universal->next = NULL;
#endif
}

bool parser::
is_pred_of_end_block (basic_block block)
{
	edge e;
	edge_iterator ei;
	FOR_EACH_EDGE (e, ei, block->succs)
	{
		basic_block succ_block = e->dest;
		unsigned int bt = ((block_information *)(succ_block->aux))->get_block_type ();
		if (bt & END_BLOCK)
			return true;
	}
	return false;
}

basic_block parser::
get_single_succ_block (basic_block bb)
{
	int succ_count = 1;
	edge e;
	edge_iterator ei;
	basic_block succ = NULL;
	FOR_EACH_EDGE (e, ei, bb->succs)
	{
		if (succ_count > 1)
		{
			RESULT ("\nError: block has more than one succ");
			return NULL;
		}
		succ_count++;

        	succ = e->dest;
	}
	return succ;
}

basic_block parser::
get_end_block_of_function (struct cgraph_node *node)
{
	// Added by Vini
        struct function * fun = DECL_STRUCT_FUNCTION (node->decl);
        return fun->cfg->x_exit_block_ptr;

  // Returns the end basic block of the function (The end block, i.e the block
  // before EXIT_BLOCK_PTR).

  // bb_worklist bb_list = worklist_of_cnode (node);
  // int i = n_basic_blocks_for_function (DECL_STRUCT_FUNCTION (node->decl)) - NUM_FIXED_BLOCKS;
  // return bb_list[i].bb;


#if 0
	// Returns the end basic block of the function (The end block, i.e the
	// block before EXIT_BLOCK_PTR).
	// test4i.c has "return" in bb9 (which is END_BLOCK). However the below
	// function returns bb7.
	// return EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl))->prev_bb;

	// FIXME: Solution
	// Use block id 1 (i.e. EXIT_BLOCK_PTR_FOR_FUNCTION (...)) as the
	// END_BLOCK. This block (i.e. with id 1) cannot be seen when
	// FOR_EACH_BB is used. But is encountered when ->succs of bb is used.

	// FIXME:
	// This is too inefficient
	struct function * function = DECL_STRUCT_FUNCTION (node->decl);
	basic_block bb;
	FOR_EACH_BB_FN (bb, function)
	{
		if (((block_information *)(bb->aux))->get_block_type () & END_BLOCK)
			return bb;
	}

	// A function may not have any return block if the last statement
	// is exit(...). In this case we choose the previous block of
	// EXIT_BLOCK_PTR  i.e. previous to block id 1.
#if DEBUG_CONTAINER
	const char * function_name = cgraph_node_name (node);
	DEBUG ("\nCannot find end block of function %s", function_name);
#endif
	// FIXME: When there is no return and there are exit() blocks, the
	// following line returns one of the exit() blocks of the function.
	// This way the control flow from other exit() blocks gets missed. 
	bb = EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl))->prev_bb;
	DEBUG ("\nEnd basic block %d", bb->index);
	return bb;

	// Prashant:
	// bb_worklist bb_list = worklist_of_cnode (node);
	// int i = n_basic_blocks_for_function (DECL_STRUCT_FUNCTION (node->decl)) - NUM_FIXED_BLOCKS;
	// return bb_list[i].bb;
#endif
}

basic_block parser::
get_start_block_of_function (struct cgraph_node *node)
{
	// Added by Vini
	struct function * fun = DECL_STRUCT_FUNCTION (node->decl);
	return fun->cfg->x_entry_block_ptr; 

//   return ENTRY_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl))->next_bb;

#if 0
   //return ENTRY_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl));

   basic_block start_block = ENTRY_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (node->decl))->next_bb;
   if (!start_block)
	RESULT ("\nError: Cannot find start block");
#endif
}

void parser::
cs_init_alias_vars (struct cgraph_node * cnode)
{
  // VEC (ce_s, heap) *results = NULL;
  // struct constraint_expr csexpr;
  // This gives segmentation fault if constraint_expr contains list<>.
  // VEC_safe_push (ms_s, heap, results, &csexpr);

   csvarmap = VEC_alloc (csvarinfo_t, heap, 200);
   aliases = VEC_alloc (constraint_t, heap, 200);
   DEBUG ("\ncreate_alloc_pool (constraint)");
   DEBUG ("\ncreate_alloc_pool (csvariable_info)");
   constraint_pool = create_alloc_pool ("Constraint pool", sizeof (struct constraint), 200);
   csvarinfo_pool = create_alloc_pool ("Variable pool", sizeof (struct csvariable_info), 200);
   vi_for_tree = pointer_map_create ();
   cs_init_base_vars (cnode);
   gcc_obstack_init (&fake_var_decl_obstack);
}

tree parser::
cs_get_var (tree t)
{
   if (TREE_CODE (t) == MEM_REF) {
       t = TREE_OPERAND (t, 0);
       return cs_get_var (t);
   }
   return t;
}

/* -------------------------------------------------------------------
   Check whether the given alias is already present in the alias pool.
   -------------------------------------------------------------------*/
/*
bool
check_alias_inclusion (constraint_t t, csvarinfo_t vi, unsigned int *loc)
{
   df_list ai;
   for (ai=vi->constraints_with_vi_as_lhs; ai; ai=ai->next) {
       if (constraint_equal (*t, *VEC_index (constraint_t, aliases, ai->val))) {
           *loc = ai->val;
           return true;
       }
   }
   return false;
}
*/


/**
 * This function checks whether a constraint is already created for a
 * CALL_BLOCK. We erase and re-add constraints in a CALL_BLOCK during points-to
 * analysis depending on the called function. Therefore, we need to fetch an
 * already created constraint.
 */

// Added by Vini
bool parser::
get_constraint_index (constraint_t t, basic_block current_block, unsigned int * index)
{
	unsigned int bt = ((block_information *)(current_block->aux))->get_block_type ();
	if (!(bt & CALL_BLOCK))
	{
		DEBUG ("\nnot call block");
		return false;
	}

	DEBUG ("\nis_constraint_present (call block=%d)", current_block->index);

	list<pair<unsigned int, bool> > call_return_indices =
		 ((block_information *)(current_block->aux))->get_call_return_indices ();

        // Iterate in forward direction for points-to analysis
        list<pair<unsigned int, bool> >::iterator it;
        for (it = call_return_indices.begin (); it != call_return_indices.end (); it++)
        {
                unsigned int id = (*it).first;
                bool is_assignment = (*it).second;
		if (!is_assignment)
			continue;
	        constraint_t present_constr = VEC_index (constraint_t, assignment_data, id);
		if (constraint_equal (*t, *present_constr))
		{
			DEBUG ("\nlhs.var=%d rhs.var=%d present in id=%d", t->lhs.var, t->rhs.var, id);
			*index = id;
			return true;
		}
	}
	DEBUG ("\nlhs.var=%d rhs.var=%d NOT present", t->lhs.var, t->rhs.var);
	return false;
}

/* -----------------------------------------------------------------------------------
   function to append the constraint index to the 'constriants_with_vi_as_lhs' of the 
   varinfo on the LHS of the constraint.
   ----------------------------------------------------------------------------------*/
/*  void
append_constraint_to_varinfo (csvarinfo_t t, int alias_no)
{
         // DEBUG ("\n in append constraint to varinfo: %d",alias_no);

    df_list elt = create_df_constraint (alias_no);
    elt->next = t->constraints_with_vi_as_lhs;
    t->constraints_with_vi_as_lhs = elt;
}*/



/*-------------------------------------------------------------------------
  Insert the constraint t in the alias pool. Update the alias list for the
  current basic block. Also, update the bb_alias_list of variable vi (forming 
  the LHS of the constraint) to reflect the fact that variable vi is the
  lhs of some constraint t.
  ------------------------------------------------------------------------*/
void parser::
insert_alias_in_pool (constraint_t t, csvarinfo_t vi, basic_block bb)
{
     DEBUG ("\nInsert in alias pool : %d,%d",vi->id, t->lhs.var);

    // df_list new_alias;					// Vini: Why commented out? Liveness set
     unsigned int loc;
     // Was set to false by Avantika
     // bool alias_found = check_alias_inclusion (t, vi, &loc);

     // The following works only for CALL_BLOCKs.
     bool alias_found = get_constraint_index (t, bb, &loc);

     if (!alias_found) {
         loc = VEC_length (constraint_t, aliases);
         VEC_safe_push (constraint_t, heap, aliases, t);
	  // Add index if bb is CALL_BLOCK
	 ((block_information *)(bb->aux))->add_to_call_return_indices (loc, true, bb);
         //append_constraint_to_varinfo (vi, loc);		// Vini: Why commented out? Adds to liveness set
     }
     //new_alias = create_df_constraint (loc);			// Vini: Why commented out? Adds to liveness set
     // Avantika has commented out the IF check, but not the ADD function
     // This is the difference in her code between Sep13 and Jan14
     // if (!compute_alias_and_pinfo)
     {
	DEBUG ("\ncompute_alias_and_pinfo != NULL");
        ((block_information *)(bb->aux))->add_to_parsed_data_indices (loc, true, bb);	// Add to constraints (or parsed data) of the block
     }
     //else							// Vini: Why commented out?
     {
         //append_to_fptr_constraints (new_alias);		// Vini: Why commented out?
         // DEBUG ("\nin fptr constraints add");
     }
}



/*-------------------------------------------------------------------------------------
  Function which processes the constraint t, retrieves the lhs and rhs of the pointsto
  constraint, and updates the alias pool. 
  ------------------------------------------------------------------------------------*/
void parser::
cs_process_constraint (constraint_t t, basic_block bb)
{
   DEBUG ("\nin cs process constraint");
   struct constraint_expr rhs = t->rhs;
   struct constraint_expr lhs = t->lhs;

   gcc_assert (rhs.var < VEC_length (csvarinfo_t, csvarmap));
   gcc_assert (lhs.var < VEC_length (csvarinfo_t, csvarmap));

   if (!is_proper_var (lhs.var))
   {
       DEBUG ("\nlhs.var is not proper");
       return;
   }

   // ADDRESSOF on the lhs is invalid.  
   gcc_assert (lhs.type != ADDRESSOF);

   if (check_deref) 
       deref_stmt = (rhs.type == DEREF || lhs.type == DEREF);

   // Avantika has commented out the IF check, but not the INSERT function, Prashant does not
   // This is the difference in her code between Sep13 and Jan14
   // if (!compute_only_pinfo)
       insert_alias_in_pool (t, cs_get_varinfo (lhs.var), bb);

 /*  if (compute_alias_and_pinfo)
	{
	 DEBUG ("\ncomput alias and pinfo");
       //compute_stmt_out_1 (cpinfo, t);
	}
   
   if (compute_only_pinfo)
	{
	DEBUG ("\ncompute only pinfo");
       //compute_stmt_out_2 (cpinfo, t);
	}*/
}

bool parser::
possibly_lhs_deref (gimple stmt)
{
   tree lhsop = gimple_assign_lhs (stmt);

   // Both Avantika and Prashant use this
   //return ((TREE_CODE (lhsop) == MEM_REF) ||
   //		(rhsop && TREE_CODE (rhsop) == MEM_REF));

   return ((TREE_CODE (lhsop) == MEM_REF) ||
   		(TREE_CODE (lhsop) == COMPONENT_REF));
}

bool parser::
possibly_rhs_deref (gimple stmt)
{
   tree rhsop = (gimple_num_ops (stmt) == 2) ? gimple_assign_rhs1 (stmt) : NULL;

   // Both Avantika and Prashant use this
   //return ((TREE_CODE (lhsop) == MEM_REF) ||
   //		(rhsop && TREE_CODE (rhsop) == MEM_REF));

   return ((rhsop && TREE_CODE (rhsop) == MEM_REF) ||
   		(rhsop && TREE_CODE (rhsop) == COMPONENT_REF));
}


/* --------------------------------------------------------------------
   Perform necessary initializations for the callstrings pointsto pass.
   -------------------------------------------------------------------*/

/* CHANGE DUE TO GCC-4.7.2 */

/* Associate node with varinfo DATA. Worker for
   cgraph_for_node_and_aliases.  */
bool parser::
associate_varinfo_to_alias (struct cgraph_node *node, void *data)
{
  if (node->alias || node->thunk.thunk_p)
    cs_insert_vi_for_tree (node->decl, (csvarinfo_t)data);
  return false;
}


void parser::
process_gimple_assign_stmt (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
	DEBUG ("\nprocess_gimple_assign_stmt");
	tree lhsop = gimple_assign_lhs (stmt);
	tree rhsop = (gimple_num_ops (stmt) == 2) ? gimple_assign_rhs1 (stmt) : NULL;

/*
   RESULT ("\nSTATEMENT: ");
   print_gimple_stmt(dump_file,stmt,0,0);
   RESULT ("\n--------lhs--------\n");
   print_node (dump_file, 0, lhsop, 0);
   RESULT ("\n--------rhs--------\n");
   print_node (dump_file, 0, rhsop, 0);

   tree tt;
   RESULT ("\n--------type-lhs--------\n");
   if (tt = reference_alias_ptr_type (lhsop))
      print_node (dump_file, 0, tt, 0);
  if (TREE_CODE (lhsop) == MEM_REF)
  {
    RESULT ("\n----------MEM--------");
    print_node (dump_file, 0, TREE_OPERAND (lhsop, 1), 0);
  }

   if (DECL_P (rhsop))
   {
   RESULT ("\n--------type-rhs--------\n");
   if (tt = reference_alias_ptr_type (rhsop))
      print_node (dump_file, 0, tt, 0);
   }
*/
#if DEBUG_CONTAINER
   RESULT ("\nSTATEMENT: ");
   print_gimple_stmt(dump_file,stmt,0,0);
   HOST_WIDE_INT bitsize = -1;
   HOST_WIDE_INT bitmaxsize = -1;
   HOST_WIDE_INT bitpos;
   get_ref_base_and_extent (lhsop, &bitpos, &bitsize, &bitmaxsize);
   DEBUG ("\n");
   print_gimple_stmt(dump_file,stmt,0,0);
   DEBUG ("\nlhsop bitpos=%lld, bitsize=%lld, bitmaxsize=%lld", bitpos, bitsize, bitmaxsize);
//   DEBUG ("\n--------lhs--------\n");
//   print_node (dump_file, 0, lhsop, 0);
//   DEBUG ("\n--------rhs--------\n");
//   print_node (dump_file, 0, rhsop, 0);
#endif 

   if (rhsop && TREE_CLOBBER_P (rhsop))
	return;

   // FIXME: (field_must_have_pointers (lhsop) || field_must_have_pointers (rhsop)
   // For example, x=*y, here lhsop is int (neither mem_ref, nor pointer_type),
   // If the constraint of such a statement should be stored, use above condition

   if (field_must_have_pointers (lhsop)) 
   {
       DEBUG ("\nmust have pointers lhs");
       VEC(ce_s, heap) *lhsc = NULL;
       VEC(ce_s, heap) *rhsc = NULL;
       if (rhsop && AGGREGATE_TYPE_P (TREE_TYPE (lhsop)))  /* Look into : Structure variables */
       {
        	DEBUG ("\naggregate_type_p");
		cs_do_structure_copy (lhsop, rhsop, bb, cnode); 
       }
       else 
       {
		DEBUG ("\nnot aggregate_type_p");
           cs_get_constraint_for (lhsop, &lhsc, bb, cnode);
           if (gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR)
	   {
		DEBUG ("\nrhs is POINTER_PLUS_EXPR");
                // gimple_assign_rhs2() returns UNKNOWN_OFFSET times the operand value.
                cs_get_constraint_for_ptr_offset (gimple_assign_rhs1 (stmt),
                               gimple_assign_rhs2 (stmt), &rhsc, bb, cnode);
	   }
           // Commented by Prashant
           //else if (code == BIT_AND_EXPR
           //        && TREE_CODE (gimple_assign_rhs2 (t)) == INTEGER_CST)
           //{
              // Aligning a pointer via a BIT_AND_EXPR is offsetting
              //   the pointer.  Handle it by offsetting it by UNKNOWN.
           //   get_constraint_for_ptr_offset (gimple_assign_rhs1 (t), NULL_TREE, &rhsc);
           //}
           else if ((CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (stmt))
                     && !(POINTER_TYPE_P (gimple_expr_type (stmt))
                     && !POINTER_TYPE_P (TREE_TYPE (rhsop))))
                     || gimple_assign_single_p (stmt))
	   {
		DEBUG ("\npointer_type_p ??");

                // cs_get_constraint_for (rhsop, &rhsc, bb, cnode);	// by Prashant
                cs_get_constraint_for_rhs (rhsop, &rhsc, bb, cnode);
#if DEBUG_CONTAINER
		struct constraint_expr *rhsp;
		unsigned j;
                FOR_EACH_VEC_ELT (ce_s, rhsc, j, rhsp) {
	           DEBUG ("\nrhsp %d offset %llu\n", rhsp->var, rhsp->offset);
		}
#endif
	   }
	  // cs_process_all_all_constraints calls
	  // cs_process_constraint calls
	  // insert_alias_in_pool. This function stores constraints in a global
	  // variable: aliases (of type constraint_t).

	  DEBUG ("\nin process_gimple_asgn_stmt\n");
          cs_process_all_all_constraints (lhsc, rhsc, bb);
       }

       // Commented by Prashant
       // If there is a store to a global variable the rhs escapes.
       // ...

       VEC_free (ce_s, heap, rhsc);
       VEC_free (ce_s, heap, lhsc);

#if DEBUG_CONTAINER
	print_assignment_data ();
#endif
   }

   // Constraints for v=*w type of statements is not created (where v is
   // non-pointer). However, w should be made live because w is a pointer. 

   // MEM_REF: These nodes are used to represent the object pointed to by a
   // pointer offset by a constant. The first operand is the pointer being
   // dereferenced; it will always have pointer or reference type. The second
   // operand is a pointer constant. Its type is specifying the type to be used
   // for type-based alias analysis. 
   else
   {
       // Let us say the statement is x->f=y. The control has reached this
       // point if x->f and y are non-pointers. However, generate liveness of
       // x.
       if (lhsop && TREE_CODE (lhsop) == COMPONENT_REF)
       {
	  DEBUG ("\nlhs is COMPONENT_REF");
          lhsop = TREE_OPERAND (lhsop, 0);
       }

       // Generate liveness of lhs
       if (lhsop && TREE_CODE (lhsop) == MEM_REF)
       {
           	DEBUG ("\nGenerate liveness constraint for lhs -- MEM_REF %d, %s(%d) in bb=%d",
   		field_must_have_pointers (lhsop),
		(cs_get_vi_for_tree (cs_get_var (lhsop), bb, cnode))->name,
		(cs_get_vi_for_tree (cs_get_var (lhsop), bb, cnode))->id,
		bb->index);

	    // Added by Vini
	    tree lhsvar = cs_get_var (lhsop);
	    // If lhs has ADDR_EXPR, then also field_must_have_pointers(lhsvar)
	    // returns true. But we do not want to add lhsvar if it has been
	    // used as lhsvar=...;
            if (!field_must_have_pointers (lhsvar) || TREE_CODE (lhsvar) == ADDR_EXPR) 
		return;

	    DEBUG ("\ngenerate liveness lhsvar");
            // generate_liveness_constraint
            ((block_information *)(bb->aux))->add_to_parsed_data_indices 
            	((cs_get_vi_for_tree (lhsvar, bb, cnode))->id, false, bb);	
       }

       // Let us say the statement is x=y->f. The control has reached this
       // point if x and y->f are non-pointers. However, generate liveness of
       // y.
       if (rhsop && TREE_CODE (rhsop) == COMPONENT_REF)
       {
	  DEBUG ("\nrhs is COMPONENT_REF");
          rhsop = TREE_OPERAND (rhsop, 0);
       }

       // Generate liveness of rhs
       if (rhsop && TREE_CODE (rhsop) == MEM_REF)
       {
            DEBUG ("\nGenerate liveness constraint for rhs -- MEM_REF %d, %s(%d) in bb=%d", 
   		field_must_have_pointers (rhsop),
		(cs_get_vi_for_tree (cs_get_var (rhsop), bb, cnode))->name, 
		(cs_get_vi_for_tree (cs_get_var (rhsop), bb, cnode))->id,
		bb->index);

	    // Added by Vini
	    tree rhsvar = cs_get_var (rhsop);
	    // If rhs has ADDR_EXPR, then also field_must_have_pointers(rhsvar)
	    // returns true. But we do not want to add rhsvar if it has been
	    // used as ...=&rhsvar;
            if (!field_must_have_pointers (rhsvar) || TREE_CODE (rhsvar) == ADDR_EXPR) 
		return;

	    DEBUG ("\ngenerate liveness rhsvar");
            // generate_liveness_constraint
            ((block_information *)(bb->aux))->add_to_parsed_data_indices 
            	((cs_get_vi_for_tree (rhsvar, bb, cnode))->id, false, bb);
       }
   }
}


void parser::
process_gimple_condition(gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
 struct constraint_expr *exp;
   unsigned i;

   tree op0 = gimple_cond_lhs (stmt);
   tree op1 = gimple_cond_rhs (stmt);

   if (field_must_have_pointers (op0) && TREE_CODE (op0) != ADDR_EXPR) {
       VEC (ce_s, heap) *results = NULL;
       cs_get_constraint_for (op0, &results, bb, cnode);
       FOR_EACH_VEC_ELT (ce_s, results, i, exp)
	// DEBUG ("\ngenerate liveness for %d",exp->var);
           ((block_information *)(bb->aux))->add_to_parsed_data_indices (exp->var, false, bb);	// generate_liveness_constraint
       VEC_free (ce_s, heap, results);
   }
   if (field_must_have_pointers (op1) && TREE_CODE (op1) != ADDR_EXPR) {
       VEC (ce_s, heap) *results = NULL;
       cs_get_constraint_for (op1, &results, bb, cnode);
       FOR_EACH_VEC_ELT (ce_s, results, i, exp)
	// DEBUG ("\n%d generate liveness for",exp->var);
           ((block_information *)(bb->aux))->add_to_parsed_data_indices (exp->var, false, bb);	// generate_liveness_constraint
       VEC_free (ce_s, heap, results);
   }

}

/* Find out aliases for PHI statements. */

void parser::
process_gimple_phi_stmt (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
   VEC(ce_s, heap) *lhsc = NULL;
   VEC(ce_s, heap) *rhsc = NULL;
   struct constraint_expr *c;
   size_t i;
   unsigned int j;
   DEBUG ("\nin process phi statement");
#if DEBUG_CONTAINER
        print_gimple_stmt(dump_file,stmt,0,0);
#endif

   /* For a phi node, assign all the arguments to the result. */
   cs_get_constraint_for (gimple_phi_result (stmt), &lhsc, bb, cnode);
   DEBUG ("\nthe no of phi args: %d",gimple_phi_num_args(stmt));
   int rhsc_count = 0;
   for (i = 0; i < gimple_phi_num_args (stmt); i++) 
   {
       ++rhsc_count;
       DEBUG ("\nrhsc_count=%d", rhsc_count);
       DEBUG ("\ni=%d loop", i);
       tree strippedrhs = PHI_ARG_DEF (stmt, i);
       STRIP_NOPS (strippedrhs);
       cs_get_constraint_for (strippedrhs, &rhsc, bb, cnode);
       for (j = 0; VEC_iterate (ce_s, lhsc, j, c); j++) 
       {
	   DEBUG ("\nj=%d loop", j);
           struct constraint_expr *c2;
           while (VEC_length (ce_s, rhsc) > 0) 
           {
               DEBUG ("\nrhsc VEC loop");
               c2 = VEC_last (ce_s, rhsc);
               cs_process_constraint (new_constraint (*c, *c2), bb);
               if (rhsc_count >= 2)
		     connect_with_previous_phi (bb);
               VEC_pop (ce_s, rhsc);
               multi_rhs = true;
           }
       }
   }

   initialize_prev_of_first_phi (bb);

   multi_rhs = false;
   VEC_free (ce_s, heap, rhsc);
   VEC_free (ce_s, heap, lhsc);
}

void parser::
connect_with_previous_phi (basic_block block)
{
	DEBUG ("\nconnect_with_previous_phi");

        list<pair<unsigned int, bool> > parsed_data_indices = 
		((block_information *)(block->aux))->get_parsed_data_indices ();

        list<pair<unsigned int, bool> >::reverse_iterator rit;
	rit = parsed_data_indices.rbegin ();
	if (rit == parsed_data_indices.rend ()) return;
        unsigned int last_index = (*rit).first;
        bool is_last_assignment = (*rit).second;
	if (!is_last_assignment) return;
	DEBUG ("\nFetched last_index %d", last_index);
	++rit;	
	if (rit == parsed_data_indices.rend ()) return;
	 unsigned int prev_index = (*rit).first;
        bool is_prev_assignment = (*rit).second;
	if (!is_prev_assignment) return;
	DEBUG ("\nFetched prev_index %d", prev_index);
	
	constraint_t last_assignment = VEC_index (constraint_t, assignment_data, last_index);
	constraint_t prev_assignment = VEC_index (constraint_t, assignment_data, prev_index);
	if (!last_assignment || !prev_assignment)
	{
		RESULT ("\nError: Cannot extract assignment index info");
		return;
	}
	last_assignment->previous_phi = prev_assignment;
	if (prev_assignment)
		DEBUG ("\nSetting previous_phi");

#if DEBUG_CONTAINER
	DEBUG ("\nConnecting %d <- %d", prev_index, last_index);
	DEBUG ("\n");
	print_assignment_data (last_index);
	DEBUG ("\n");
	print_assignment_data (prev_index);
#endif
}

/**
 * PREVIOUS_PHI is set so that it can be indicated that these statements are
 * not to be analyzed in sequence but as if they are in parallel. Since they
 * are in parallel, the pointer information of lhs generated by a previously
 * analyzed phi statement should not be killed by any other phi statement. If
 * there exists a phi statement with the same lhs and rhs, then set
 * previous_phi of the first phi satement, so that no killing is performed in
 * the first phi statement also.
 */

void parser::
initialize_prev_of_first_phi (basic_block block)
{
	DEBUG ("\nconnect_with_previous_phi");

        list<pair<unsigned int, bool> > parsed_data_indices = 
		((block_information *)(block->aux))->get_parsed_data_indices ();

        list<pair<unsigned int, bool> >::iterator it;
	for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
	{
		unsigned int index = it->first;
		bool is_assignment = it->second;
		if (!is_assignment) return;
		constraint_t assignment = VEC_index (constraint_t, assignment_data, index);
		constraint_expr lhs = assignment->lhs;
		constraint_expr rhs = assignment->rhs;
		// Does there exist a phi statement with same lhs and rhs
		if (lhs.var == rhs.var &&
			lhs.type == rhs.type &&
			lhs.offset == rhs.offset)
		{
			// Fetch first phi statement
			it = parsed_data_indices.begin ();
			constraint_t first_assignment = VEC_index (constraint_t, assignment_data, it->first);
			// Set the previous_phi of the first phi statement
			first_assignment->previous_phi = assignment;
			if (assignment)
				DEBUG ("\nSetting previous_phi 2");
			RESULT ("\nSet first previous_phi also, so that no killing happens");
			return;			
		}
	}
}

bool parser::
is_gimple_endblock (gimple t)
{
   return (gimple_code (t) == GIMPLE_RETURN);
}

void parser::
generate_retval_liveness (gimple stmt, basic_block bb, struct cgraph_node * cnode)
{
   DEBUG ("\ngenerate_retval_liveness ()");
   tree retval = gimple_return_retval (stmt);

   if (retval!=NULL_TREE && field_must_have_pointers (retval)) {
       DEBUG ("\nNot pointer type");
       VEC(ce_s, heap) *rhsc = NULL;
       struct constraint_expr *rhs;
       unsigned int i;

       cs_get_constraint_for (retval, &rhsc, bb, cnode);
       FOR_EACH_VEC_ELT (ce_s, rhsc, i, rhs)
       {
          ((block_information *)(bb->aux))->add_to_parsed_data_indices (rhs->var, false, bb);	// generate_liveness_constraint
	  DEBUG ("\nPushed rhs->var %d", rhs->var);
       }
   }
}

/* Iterate over all the PHI nodes of the basic block and 
   calculate alias info for them. */
bool parser::
process_phi_pointers (basic_block bb, struct cgraph_node * cnode)
{
   gimple_stmt_iterator gsi;
   DEBUG ("\nin process phi pointers");

   bool has_phi = false;
   // There could be more than one PHI statements in a block.
   // (test-cases/test60.c). Iterate over all.
   for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi)) {
#if DEBUG_CONTAINER
       DEBUG ("\nprocessing phi:");
       print_gimple_stmt (dump_file, gsi_stmt(gsi), 0,0);
#endif
       gimple phi = gsi_stmt (gsi);
       tree phi_result = gimple_phi_result (phi);
       if (is_gimple_reg (phi_result)) {
           if (field_must_have_pointers (phi_result)) {
               DEBUG ("\nis_gimple_reg and field_must_have_pointers");
               has_phi = true;
               process_gimple_phi_stmt (phi, bb, cnode);
           }
       }
   }
   DEBUG ("\nReturn of phi pointer is %d",has_phi);
   return has_phi;
}


/*--------------------------------------------------------------------
  Returns the called function's decl tree. If it is a direct function 
  call, the TREE_CODE of the returned decl will be FUNCTION_DECL. If 
  it is a call via function pointer, it will be VAR_DECL. 
  -------------------------------------------------------------------*/
tree parser::
get_called_fn_decl (gimple stmt)
{                  
    /* If we can resolve it here, its a simple function call. */
    tree decl = gimple_call_fndecl (stmt);
    /* The call is through function pointer. */
    if (!decl)
        decl = gimple_call_fn (stmt);
    return decl;       
} 

bool parser::
is_function_pointer (basic_block call_site)
{
	// FIXME: check that this a call_site has only one statement.
	gimple_stmt_iterator gsi = gsi_start_bb (call_site);
	gimple statement = gsi_stmt (gsi);

	return gimple_call_fndecl (statement) == NULL;
}

// Create block after stmt

gimple_stmt_iterator parser::
split_bb_at_stmt (basic_block & bb, gimple stmt)
{
	DEBUG ("\n---SPLIT---");
	DEBUG ("\nFirst statement of block %d (before split): ", bb->index);
#if DEBUG_CONTAINER
	if (!gsi_end_p (gsi_start_bb (bb)))
		print_gimple_stmt (dump_file, gsi_stmt (gsi_start_bb (bb)), 0, 0);
#endif
        // Creates a new basic block just after basic block B by splitting
        // everything after specified instruction I.
	edge e = split_block (bb, stmt);
	bb = e->dest;
	DEBUG ("\nFirst statement of block %d (after split): ", bb->index);
#if DEBUG_CONTAINER
	if (!gsi_end_p (gsi_start_bb (bb)))
		print_gimple_stmt (dump_file, gsi_stmt (gsi_start_bb (bb)), 0, 0);
#endif
	DEBUG ("\nInitializing split block %d", bb->index);
	initialize_block_aux (bb);
	return gsi_start_bb (bb);
}

void parser:: 
initialization (void) 
{ 
   DEBUG ("\ninitialization()");

   struct cgraph_node * cnode = NULL; 
  // init_alias_heapvars (); 
   cs_init_alias_vars (cnode); 
   bool is_first_cnode = true;
 
   for (cnode = cgraph_nodes; cnode; cnode = cnode->next) { 
       DEBUG ("\nin loop");
 
       struct cgraph_node *alias; 
       csvarinfo_t vi; 
 
       /* Nodes without a body, and clone nodes are not interesting. */ 
       if (!gimple_has_body_p (cnode->decl) || cnode->clone_of) 
           continue; 

       // The first function is either main () or _GLOBAL__I_6535_0_test<..>.o ()

       DEBUG ("\nin cnode --- %d,%s",cnode->uid,cgraph_node_name(cnode)); 
       /* locating main function. */ 
       //if (strcmp (cgraph_node_name (cnode), "int main()") == 0)
       if (strcmp (IDENTIFIER_POINTER (DECL_NAME (cnode->decl)), "main") == 0)
       {
           main_cnode = cnode; 
           DEBUG ("\nFound main function '%s'", IDENTIFIER_POINTER (DECL_NAME (cnode->decl)));
           DEBUG ("\nFound main function '%s'", cgraph_node_name (cnode));
       }
 
       // Creates csvarinfo_t for this function and its parameters and local variables 
       vi = cs_create_func_info_for (cnode->decl, cgraph_node_name (cnode), cnode); 
 
        /* CHANGE due gcc-4.7.2 */ 
	// Sudakshina introduced this. Avantika uses it.
	// cgraph_for_node_and_aliases (cnode, associate_varinfo_to_alias, vi, true); 
 
       /* Associate the varinfo node with all aliases.   
       for (alias = cnode->same_body; alias; alias = alias->next) 
           cs_insert_vi_for_tree (alias->decl, vi);*/ 

	is_first_cnode = false;
   } 

#if HEAP_TYPE_BASED_NAME
   DEBUG ("\nClear heap_type info");
   heap_type_count = 0;
   heap_type_id.clear ();
#endif
}

/**
 * Global initializations of the form x=&y are not saved in any function. We
 * need to add them to the first block of main function.
 * FIXME: The parsed statements are erased by process_return_value() and
 * process_function_arg() if the first block of main() contains a function
 * call.
 */
// Added by Vini
void parser::
add_global_addressof_initializations ()
{
	DEBUG ("\nadd_global_addressof_initializations()");
	if (!main_cnode)
	{
		RESULT ("\nError: main() not found");
		return;
	}
	push_cfun (DECL_STRUCT_FUNCTION (main_cnode->decl));
	basic_block startbb = get_start_block_of_function (main_cnode);
	basic_block bb = startbb->next_bb;
	// Create an empty block after START_BLOCK
	if (first_stmt (bb))
		split_bb_at_stmt (bb, NULL);
	else
		initialize_block_aux (bb);
	pop_cfun ();

	// Insert global initializations of the form x=&y in BB
	DEBUG ("\nadd_global_addressof_initializations (bb=%d)", bb->index);
	struct varpool_node * global_var;
	for (global_var = varpool_nodes; global_var; global_var = global_var->next)
	{
		if (field_must_have_pointers (global_var->decl))
		{
			csvarinfo_t globvar = cs_get_vi_for_tree (global_var->decl, bb, main_cnode);
			DEBUG ("\nAdded global_var %s(%d)", globvar->name, globvar->id);
		}
	}
}

static void
study_loops ()
{
	DEBUG ("\nnumber_of_loops = %d", number_of_loops ());

	// Studying loops
	loop_iterator li;
	struct loop * loop;
	FOR_EACH_LOOP (li, loop, 0)
	{
		basic_block head = loop->header;
		DEBUG ("\nheader block: %d", head->index);
		basic_block * bbs;
		bbs = get_loop_body (loop);
		for (int i = 0; i < loop->num_nodes; i++)
		{
			basic_block bb = bbs[i];
			DEBUG ("\nbb=%d, ", bb->index);

			gimple_stmt_iterator gsi;
			for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi)) 
			{
				gimple stmt = gsi_stmt (gsi);
				print_gimple_stmt (dump_file, stmt, 0, 0);
			}
		}
		free (bbs);
	}

	// Studying blocks
	basic_block bb;
	FOR_EACH_BB (bb)
	{
		DEBUG ("\nbb=%d", bb->index);
		for (loop = bb->loop_father; loop; loop = loop_outer (loop))
		{
			DEBUG ("\nloop=%d", loop->num);
			if (bb->index == loop->header->index)
			{
				DEBUG ("\nloop %d has header %d", loop->num, bb->index);
			}
		}
	}
}

bool parser::
is_loop_join (basic_block block)
{
	struct loop * loop = block->loop_father;
	if (!loop)
	{
		RESULT ("\nError: loop_optimizer_init() not done");
		return false;
	}
	bool loop_join = block->index == loop->header->index;
	if (loop_join)
		DEBUG ("\nBlock %d is header of loop %d\n", block->index, loop->num);

	return loop_join;
}

void parser::
preprocess_control_flow_graph ()
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif 

	unsigned int function_count = 0;
	unsigned int block_count = 0;	
	count_malloc_calls = 0;

#if UNSOUND == 0
	// Insert constraints corresponding to global initializations of the
	// form x=&y to the block after START_BLOCK of main_cnode.
	add_global_addressof_initializations ();
#endif

	struct cgraph_node * cnode;
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		DEBUG ("\nin loop 2");
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		function_count++;

       		DEBUG ("\nin cnode --- %d,%s",cnode->uid,cgraph_node_name(cnode)); 
		push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));
		// set_cfun (DECL_STRUCT_FUNCTION (cnode->decl));
		// current_function_decl = cnode->decl;

#if LOOP_MERGE_OPTIMIZATION
		// https://gcc.gnu.org/onlinedocs/gccint/Loop-representation.html

		// loop_optimizer_init (0);
		// loop_optimizer_init (LOOPS_MAY_HAVE_MULTIPLE_LATCHES);
		loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
#endif 

#if DEBUG_CONTAINER
                DEBUG ("\nFunction : %s\n", cgraph_node_name (cnode));
		if (!cfun) 
			RESULT ("\nError: cfun is NULL");
		study_loops ();
#endif

		// START_BLOCK
		basic_block startbb = get_start_block_of_function (cnode); 
		DEBUG ("\nBlock %d is set as start block", startbb->index);
		initialize_block_aux (startbb);
		((block_information *)(startbb->aux))->set_block_type (START_BLOCK);

		// END_BLOCK
		basic_block endbb = get_end_block_of_function (cnode); 
		DEBUG ("\nBlock %d is set as end block", endbb->index);
		initialize_block_aux (endbb);
		((block_information *)(endbb->aux))->set_block_type (END_BLOCK);

		DEBUG ("\nstartbb=%d, endbb=%d", startbb->index, endbb->index);

		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
			block_count++;

			DEBUG ("\nBlock %d", current_block->index);

			gimple_stmt_iterator gsi;
			bool has_phi = false;

			// Initialize auxillary info.
			DEBUG ("\nInitializing block");
			initialize_block_aux (current_block);

#if LOOP_MERGE_OPTIMIZATION
			if (is_loop_join (current_block))
				((block_information *)(current_block->aux))->set_loop_join ();
#endif

			DEBUG ("\nprocess_phi_pointers block %d", current_block->index);
			has_phi = process_phi_pointers (current_block, cnode);
			DEBUG ("\nblock %d has_phi=%d", current_block->index, has_phi);

			// Iterate over the statements of current_block.
			for (gsi = gsi_start_bb (current_block); !gsi_end_p (gsi); gsi_next (&gsi)) 
			{
				gimple stmt = gsi_stmt (gsi);
				DEBUG ("\n---------------------------------------\n");
				DEBUG ("\nProcessing statement in block %d: ", current_block->index);
#if DEBUG_CONTAINER
				print_gimple_stmt (dump_file, stmt, 0, 0);
#endif

				// We are assuming that END block has only
				// return statement; therefore, we use IN
				// points-to value, instead of OUT points-to
				// value. Thus, break at boundaries of callbb
				// and returnbb.
				if (is_gimple_call (stmt) || is_gimple_endblock (stmt)) 
				{
					DEBUG ("\nCall or end block");
					gimple_stmt_iterator origgsi = gsi;
					tree decl = NULL;

					// Need not break in case of library routines.
					if (is_gimple_call (stmt)) 
					{
						DEBUG ("\nCall statement");
						// FIXME: Make sure call statement is the only statement 
						// in the CALL block.
						gimple_stmt_iterator origgsi_lib = gsi;
						// Splitting before call stmt (i.e. after prev gsi)
						gsi_prev (&gsi);
						if (!gsi_end_p (gsi))
						{
							DEBUG ("\nsplit 1");
							// splits after gsi
							gsi = split_bb_at_stmt (current_block, gsi_stmt (gsi));
							// This block does not have PHI
							has_phi = false;
						}
						else
						{
							gsi = origgsi_lib;
						}

						// If block is not split after PHI statement, then 
						// check if (has_phi) then split.
						// If there are PHI statements in this block, split.
						// test-cases/test53b.c 
						// fp_1 = PHI (foo, bar); fp_1 ();
						// We want to have only the call statement in a block.
						// However, PHI is not identified as a statement.
						// Therefore, we split the block if there is a PHI
						// statement before the call statement.
						if (has_phi)
						{
							has_phi = false;
							DEBUG ("\nsplit after phi");
							split_bb_at_stmt (current_block, NULL);
							DEBUG ("block %d has_phi=%d", current_block->index, has_phi);
						}

						decl = get_called_fn_decl (stmt);
						if (TREE_CODE (decl) == FUNCTION_DECL) 
						{
							DEBUG ("\nFunction decl");
							if (!DECL_STRUCT_FUNCTION (decl)) 
							{
								// FIXME: lbm benchmark, function MAIN_FINALIZE(), 
								// <bb 6> LBM_freeGrid () wrongly considered 
								// as a library call.
								DEBUG ("\nLibrary call");
								process_library_call (stmt, current_block, cnode);

								// A fresh_heap_node may not be unused (with ap_nodes
								// and ap_unbounded as empty) if incl_edges has an 
								// edge pointing to PNID. To avoid this check, we 
								// split the blocks after each malloc() in misc/parser
								// so that this situation does not arise.

/*
								// A library call is not marked as a call_block
   								if (gimple_call_flags (stmt) & ECF_MALLOC) 
									continue;

								// Split the malloc call into a new current_block 
								// if its not the last stmt.
								// origgsi = gsi;
								gsi = origgsi;
								gsi_next (&gsi);
								// if (!gsi_end_p (gsi)) // This is erroneous. 
								// The following is needed.
								if (!is_gimple_endblock (stmt) && !gsi_end_p (gsi)) 
								{
									DEBUG ("\nSplit after block");
									gsi = origgsi;
									split_block (current_block, gsi_stmt (gsi));
								}
								else 
									gsi = origgsi;
*/			
								// A library call is not marked as a call_block
								continue;
							}
						}
					}

					DEBUG ("\nReached");
					gsi_prev (&gsi);
					if (!gsi_end_p (gsi)) 
					{
						DEBUG ("\nsplit 2");
						// Split before the call/return stmt.
						gsi = split_bb_at_stmt (current_block, gsi_stmt (gsi));
					}

					// Split the call into a new current_block if its not the last stmt.
					// origgsi = gsi;
					gsi = origgsi;
					gsi_next (&gsi);
					// if (!gsi_end_p (gsi)) // This is erroneous. The following is needed.
					if (!is_gimple_endblock (stmt) && !gsi_end_p (gsi)) 
					{
						DEBUG ("\nSplit after block");
						gsi = origgsi;
						split_block (current_block, gsi_stmt (gsi));
					}
					else 
						gsi = origgsi;

					if (is_gimple_call (stmt)) 
					{
#if SPLIT_CALL_INTO_AUX 
						decl = get_called_fn_decl (stmt);
						if (TREE_CODE (decl) == FUNCTION_DECL && DECL_STRUCT_FUNCTION (decl)) 
						{
							((block_information *)(current_block->aux))->set_block_type (CALL_BLOCK); 
							((block_information *)(current_block->aux))->set_block_type (AUX_BLOCK); 
							DEBUG ("\nAUX=%d", current_block->index);
							split_bb_at_stmt (current_block, NULL);
						}
#endif
						DEBUG ("\nCall statement again");

						// Mark call current_block with its properties.
						((block_information *)(current_block->aux))->set_block_type (CALL_BLOCK); 

						DEBUG ("\nSet block type of %d to CALL_BLOCK", current_block->index);
	
						bool fptr_call = (TREE_CODE (decl) != FUNCTION_DECL);

						// Mark the calling function pointer as live.
						if (fptr_call) 
						{
		 					unsigned int var = cs_get_vi_for_tree (decl, current_block, cnode)->id;
							// generate_liveness_constraint
			 				((block_information *)(current_block->aux))->add_to_parsed_data_indices (var, false, current_block);	
						}
						  
						DEBUG ("\nDiscovering the static call argument mapping block=%d", current_block->index);
						// Discover the static call argument mapping.
						map_arguments_at_call (stmt, decl, fptr_call, current_block, cnode); 

						// Generate variable for lhs (received variable)
      						tree lhsop = gimple_call_lhs (stmt);
						if (lhsop && field_must_have_pointers (lhsop)) 
						{
							DEBUG ("\nlhs is pointer");
							VEC(ce_s, heap) *lhsc = NULL;
							cs_get_constraint_for (lhsop, &lhsc, current_block, cnode);
							VEC_free (ce_s, heap, lhsc);
						}
						
#if DEBUG_CONTAINER
						print_assignment_data ();
#endif

						// No need to create RETURN_BLOCK 
						//DEBUG ("\nCreating empty return block"); 
						// Create an empty return block.
						//gsi = split_bb_at_stmt (current_block, gsi_stmt (gsi));
						//((block_information *)(current_block->aux))->set_block_type (RETURN_BLOCK);
						//break;

					}

					if (is_gimple_endblock (stmt)) 
					{
						DEBUG ("\nReturn block");
						generate_retval_liveness (stmt, current_block, cnode);
						((block_information *)(current_block->aux))->set_block_type (RETURN_BLOCK);
					}
				}

				// Inspect other statements for possible pointers.
				else if (is_gimple_assign (stmt)) 
				{
					DEBUG ("\nAssignment statement");

					// FIXME:
					// Without block splitting: lbm runs in 726 seconds,
					// and produces 512252 lines of output.
					// With block splitting: lbm runs in 394 seconds, 
					// and produces 2630260 lines of output.
					// Perhaps the ordering of function calls differs which
					// helps in this case. 

					// Split in case of possible deref statement. 
					// This is required if we want to give each field 
					// in the statement a unique statement id.
#if SPLIT_DEREF || SPLIT_LHS_ONLY_DEREF
#if SPLIT_ALL == 0
					DEBUG ("\nchecking");
					if (possibly_lhs_deref (stmt) 
#if SPLIT_LHS_ONLY_DEREF == 0
						|| possibly_rhs_deref (stmt)
#endif
						) 
#endif
					{
						gimple_stmt_iterator origgsi = gsi;
						gsi_prev (&gsi);
						if (!gsi_end_p (gsi)) 
						{
							DEBUG ("\nStatement before current statement (before split): ");
							#if DEBUG_CONTAINER
							print_gimple_stmt (dump_file, gsi_stmt(gsi), 0, 0);
							#endif
							gsi = split_bb_at_stmt (current_block, gsi_stmt (gsi));
							DEBUG ("\nCurrent statement (after split): ");
							#if DEBUG_CONTAINER
							print_gimple_stmt (dump_file, gsi_stmt(gsi), 0, 0);
							#endif
						}
						else
							gsi = origgsi;
					}
#endif

					check_deref = true; 
					process_gimple_assign_stmt (stmt, current_block, cnode);
					check_deref = false;
				}

				else if (gimple_code (stmt) == GIMPLE_COND) 
				{
					DEBUG ("\nCondition statement");
#if SPLIT_ALL
					gimple_stmt_iterator origgsi = gsi;
					gsi_prev (&gsi);
					if (!gsi_end_p (gsi))
						gsi = split_bb_at_stmt (current_block, gsi_stmt (gsi));
					else
						gsi = origgsi;
#endif
					process_gimple_condition (stmt, current_block, cnode); 
				}

				/*
				// Check if the call/return stmt is the first stmt in the current_block.
				if (gsi_end_p (gsi) || gimple_code (gsi_stmt (gsi)) == GIMPLE_LABEL) 
				{
					DEBUG ("\nLabel statement");
					if (has_phi) 
					{
						gsi = split_bb_at_stmt (current_block, NULL);
						has_phi = false;
					 }
					 else
						gsi = origgsi;
				}
				*/
				else
				{
					DEBUG ("\nWhat is this?");
				}
				DEBUG ("\nNext statement");
				DEBUG ("block %d has_phi=%d", current_block->index, has_phi);
			}

			DEBUG ("\nNext block");
		}

		// if (dump_file)// && !ipacs_time)
  			// gimple_dump_cfg (dump_file, dump_flags);

		// Return block has is_gimple_endblock (stmt) true.
		// If the function does not have a return block, then fake
		// return statement is inserted by gimple.
		// If the function does not have a return block and has exit
		// blocks, then no return statement is inserted.
		// FIXME: In this case, we use EXIT_BLOCK_PTR_FOR_FUNCTION.
		// However, I realized that it fetches only one of the exit()
		// blocks and not the rest. Therefore, evaluation of the
		// control flow paths ending at the rest of the exit() blocks
		// does not happen. For example, in liveness analysis of
		// sjeng.c main function, free_hash() and free_ecache() never
		// get evaluated

		// Prashant: If there was no endblock, mark it.
		// if (!endblock) 
		// {
		//	endblock = EXIT_BLOCK_PTR_FOR_FUNCTION (DECL_STRUCT_FUNCTION (cnode->decl))->prev_bb;
		//	((block_information *)(endblock->aux))->set_block_type (END_BLOCK);
		// }

		// Set the reverse postorder index for all the blocks.
		// rp = XNEWVEC (int, total_curr_blocks);
		// pre_and_rev_post_order_compute (NULL, rp, false);

		// Initialize the cgraph info.
		// initialize_cgraphaux_info (cnode, endblock, rp, total_curr_blocks);
		// free (rp);

#if LOOP_MERGE_OPTIMIZATION
		loop_optimizer_finalize ();
#endif
		pop_cfun();
	}

//	RESULT ("\nfunction_count = %d", function_count);
//	RESULT ("\nblock_count = %d", block_count);
//
//	FILE * stat_file = fopen (STAT_FILE, "a");
//	fprintf (stat_file, "\nfunction_count = %d", function_count);
//	fprintf (stat_file, "\nblock_count = %d", block_count);
//	fclose (stat_file);

	// Required by EXPLICIT_LIVENESS=1 also for extract addr-taken locals
	collect_addr_taken_vars ();

//#if EXPLICIT_LIVENESS
//	addr_taken_locals.clear ();
//	addr_taken_params.clear ();
//	addr_taken_globals.clear ();
//#endif

	collect_uid_to_cnode ();
}

void parser::
collect_addr_taken_vars ()
{
#if DEBUG_CONTAINER
	print_parsed_data ();
#endif
   	struct cgraph_node * cnode = NULL; 
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

                DEBUG ("\nFunction : %s\n", cgraph_node_name (cnode));
		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
			if (!current_block->aux)
				return;
		
			unsigned int bt = ((block_information *)(current_block->aux))->get_block_type ();
			if ((bt & CALL_BLOCK) && !(bt & AUX_BLOCK))
			{
				collect_addr_taken_args (current_block, cnode);
			}
 
		        list<pair<unsigned int, bool> > parsed_data_indices = 
				((block_information *)(current_block->aux))->get_parsed_data_indices ();
		
		        list<pair<unsigned int, bool> >::iterator it;
		        for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
		        {
		                unsigned int index = (*it).first;
		                bool is_assignment = (*it).second;
		                DEBUG ("\nParsed data: index %d, bool %d, block %d, ", 
					index, is_assignment, current_block->index);
		
		                if (is_assignment)
				{
				        constraint_t assignment = VEC_index (constraint_t, assignment_data, index);
					DEBUG ("\nassignment index=%d, addr=%x", index, assignment);
				        constraint_expr lhs = assignment->lhs;
				        constraint_expr rhs = assignment->rhs;
				        csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, variable_data, lhs.var);
				        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, variable_data, rhs.var);
					if (rhs.type == ADDRESSOF)
					{
						DEBUG ("\nADDRESSOF=%s(%d)", rhs_variable->name, rhs_variable->id);
						collect_addr_taken_vars (rhs_variable);
					}
				}
		        }
		
		}

		pop_cfun();
	}
	print_addr_taken_vars ();
}

void parser::
collect_addr_taken_args (basic_block call_site, struct cgraph_node * cnode)
{
	   // FIXME: check that this call_site has only one statement.
	   gimple_stmt_iterator gsi = gsi_start_bb (call_site);
	   gimple stmt = gsi_stmt (gsi);
	
	#if DEBUG_CONTAINER
	   DEBUG ("\nFunction call: ");
	   print_gimple_stmt (dump_file, stmt, 0, 0);
	#endif
	
	   VEC(ce_s, heap) *rhsc = NULL;
	   size_t j;
	
	   /* Iterate call arguments. */
	   for (j = 0; j < gimple_call_num_args (stmt); j++) {
	       struct constraint_expr *rhsp;
	       tree arg = gimple_call_arg (stmt, j);
	       if (field_must_have_pointers (arg)) {
	           cs_get_constraint_for (arg, &rhsc, call_site, cnode);
	           while (VEC_length (ce_s, rhsc) != 0) {
	               rhsp = VEC_last (ce_s, rhsc);
			DEBUG ("\nmapped arguments:");
			DEBUG ("\nrhs var %d, type %d", rhsp->var, rhsp->type);
			if (rhsp->type == ADDRESSOF)
			{
				csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, variable_data, rhsp->var);
				collect_addr_taken_vars (rhs_variable);
				DEBUG ("\nadd to addr_taken_args");
				DEBUG ("\nrhs var %d, type %d", rhsp->var, rhsp->type);
			}
	               VEC_pop (ce_s, rhsc);
	           }
	       }
	   }
	   VEC_free (ce_s, heap, rhsc);
}

void parser::
collect_addr_taken_vars (csvarinfo_t rinfo)
{
	if (!rinfo)
		return;
	if (!rinfo->decl)
		return;
	if (!is_proper_var (rinfo->id))
		return;
	if (rinfo->is_heap_var)
		return;
	if (!cs_lookup_vi_for_tree (rinfo->decl))	// discards main.varargs variable
		return;

	if (rinfo->is_global_var)
	{
		DEBUG ("\nGLOBAL=%s(%d)", rinfo->name, rinfo->id);
		// Add root and its fields as address taken
		for (csvarinfo_t start = rinfo; start; start = start->next)
		{
			addr_taken_globals.insert (start->id);
			start->is_addr_taken = 1;
		}

		if (TREE_CODE (rinfo->decl) == FUNCTION_DECL)
		{
			struct cgraph_node * cnode = get_cgraph_node (rinfo->decl);
			addr_taken_functions.insert (cnode);
			// addr_taken_functions.insert (rinfo->id);
			rinfo->is_addr_taken = 1;
		}
	}

	struct cgraph_node * cnode = rinfo->scoping_function;
	if (!cnode)
		return;
	if (TREE_CODE (rinfo->decl) == PARM_DECL)
	{
		DEBUG ("\nPARAM=%s(%d)", rinfo->name, rinfo->id);
		// Add root and its fields as address taken
		for (csvarinfo_t start = rinfo; start; start = start->next)
		{
			addr_taken_params[cnode].insert (start->id);
			start->is_addr_taken = 1;
		}
			
	}

	DEBUG ("\nLOCAL=%s(%d)", rinfo->name, rinfo->id);
	// Add root and its fields as address taken
	for (csvarinfo_t start = rinfo; start; start = start->next)
	{
		addr_taken_locals[cnode].insert (start->id);
		start->is_addr_taken = 1;
	}
}

void parser::
print_addr_taken_vars ()
{
	map<struct cgraph_node *, set<unsigned int> >::iterator mvi;
	RESULT ("\naddr_taken_LOCALS=funcs=%d", addr_taken_locals.size ());
	for (mvi = addr_taken_locals.begin (); mvi != addr_taken_locals.end (); mvi++)
	{
		struct cgraph_node * cnode = mvi->first;
		const char * function_name = cgraph_node_name (cnode);
		RESULT ("\n\t%s(%d) -> ", function_name, cnode->uid);
		set<unsigned int> vs = mvi->second;	
		set<unsigned int>::iterator vi;
		for (vi = vs.begin (); vi != vs.end (); vi++)
		{
	        	csvarinfo_t var = VEC_index (csvarinfo_t, variable_data, *vi);
			RESULT ("%s(%d),", var->name, var->id);
		}
	}
	RESULT ("\naddr_taken_PARAMS=funcs=%d", addr_taken_params.size ());
	for (mvi = addr_taken_params.begin (); mvi != addr_taken_params.end (); mvi++)
	{
		struct cgraph_node * cnode = mvi->first;
		const char * function_name = cgraph_node_name (cnode);
		RESULT ("\n\t%s(%d) -> ", function_name, cnode->uid);
		set<unsigned int> vs = mvi->second;	
		set<unsigned int>::iterator vi;
		for (vi = vs.begin (); vi != vs.end (); vi++)
		{
	        	csvarinfo_t var = VEC_index (csvarinfo_t, variable_data, *vi);
			RESULT ("%s(%d),", var->name, var->id);
		}
	}
	RESULT ("\naddr_taken_GLOBALS=%d\n\t", addr_taken_globals.size ());
	set<unsigned int>::iterator vi;
	for (vi = addr_taken_globals.begin (); vi != addr_taken_globals.end (); vi++)
	{
        	csvarinfo_t var = VEC_index (csvarinfo_t, variable_data, *vi);
		RESULT ("%s(%d),", var->name, var->id);
	}
	RESULT ("\naddr_taken_FUNCTIONS=%d\n\t", addr_taken_functions.size ());
//	set<struct cgragh_node *>::iterator fi;
//	for (fi = addr_taken_functions.begin (); fi != addr_taken_functions.end (); fi++)
//		RESULT ("%s," cgraph_node_name (*ci));
}

void parser::
print_statistics ()
{
	unsigned int locals_count= 0;
	unsigned int globals_count= 0;
	unsigned int root_heap_typecasts_count = 0;
	unsigned int field_heap_typecasts_count = 0;
	unsigned int max_field_heap_typecasts_count = 0;

	for (int index = 0; index < VEC_length (csvarinfo_t, variable_data); index++)
	{
	        csvarinfo_t variable = VEC_index (csvarinfo_t, variable_data, index);
		if (!variable || !variable->decl)
			continue;
		if (TREE_CODE (variable->decl) == FUNCTION_DECL)
			continue;
		if (variable->is_heap_var)
		{
			if (!variable->decl)
				continue;
			if (!cs_lookup_vi_for_tree (variable->decl))	// discards main.varargs variable
				continue;
			if (!variable->offset)
			{
				DEBUG ("\nroot=%s", variable->name);
				root_heap_typecasts_count++;
				unsigned int fields = 0;
				csvarinfo_t hf;
				for (hf = variable; hf; hf = hf->next)
				{
					DEBUG ("\nfield-next=%s", hf->name);
					fields++;
				}
				if (max_field_heap_typecasts_count < fields)
					max_field_heap_typecasts_count = fields;
		
			}
			DEBUG ("\nfield=%s", variable->name);
			field_heap_typecasts_count++;
		}
		else if (variable->is_global_var)
		{
			DEBUG ("\nglobal=%s(%d)", variable->name, variable->id);
			globals_count++;
		}
		else
		{
			DEBUG ("\nlocal=%s(%d)", variable->name, variable->id);
			locals_count++;
		}
	}

	unsigned int max_root_heap_typecasts_count = 0;
	map<unsigned int, set<tree> >::iterator ati;
	for (ati = alloc_site_typecasts.begin (); ati != alloc_site_typecasts.end (); ati++)
	{
		unsigned int this_count = ati->second.size ();
		DEBUG ("\nalloc-site=%d, typecasts=%d", ati->first, this_count);
		if (max_root_heap_typecasts_count < this_count)
			max_root_heap_typecasts_count = this_count;
	}
	if (!max_root_heap_typecasts_count)
		max_root_heap_typecasts_count = 1;

	RESULT ("\nmalloc_count = %d", count_malloc_calls);
	RESULT ("\nptr_stmt_count = %d", count_ptr_stmts ());
	
	float avg_field_heap_typecasts_count = 0;
	if (root_heap_typecasts_count)
		avg_field_heap_typecasts_count = (float) field_heap_typecasts_count / root_heap_typecasts_count;
	float avg_root_heap_typecasts_count = 0;
	if (count_malloc_calls)
		avg_root_heap_typecasts_count = (float) root_heap_typecasts_count / count_malloc_calls;

	RESULT ("\ntot_locals_count=%d", locals_count);
	RESULT ("\ntot_globals_count=%d", globals_count);
//	RESULT ("\ntot_root_heap_typecasts_count=%d", root_heap_typecasts_count);
//	RESULT ("\navg_root_heap_typecasts_count=%f", avg_root_heap_typecasts_count);
//	RESULT ("\nmax_root_heap_typecasts_count=%d", max_root_heap_typecasts_count);
//	RESULT ("\ntot_field_heap_typecasts_count=%d", field_heap_typecasts_count);
//	RESULT ("\navg_field_heap_typecasts_count=%f", avg_field_heap_typecasts_count);
//	RESULT ("\nmax_field_heap_typecasts_count=%d", max_field_heap_typecasts_count);

	FILE * stat_file = fopen (STAT_FILE, "a");
	fprintf (stat_file, "\nmalloc_count = %d", count_malloc_calls);
	fprintf (stat_file, "\nptr_stmt_count = %d", count_ptr_stmts ());
	fprintf (stat_file, "\ntot_locals_count=%d", locals_count);
	fprintf (stat_file, "\ntot_globals_count=%d", globals_count);
//	fprintf (stat_file, "\ntot_root_heap_typecasts_count=%d", root_heap_typecasts_count);
//	fprintf (stat_file, "\navg_root_heap_typecasts_count=%f", avg_root_heap_typecasts_count);
//	fprintf (stat_file, "\nmax_root_heap_typecasts_count=%d", max_root_heap_typecasts_count);
//	fprintf (stat_file, "\ntot_field_heap_typecasts_count=%d", field_heap_typecasts_count);
//	fprintf (stat_file, "\navg_field_heap_typecasts_count=%f", avg_field_heap_typecasts_count);
//	fprintf (stat_file, "\nmax_field_heap_typecasts_count=%d", max_field_heap_typecasts_count);

	fclose (stat_file);
}

/* ----------------------------------------------------------------
   Restoring the cfg by clearing the aux field of each basic block
   and removing unnecessary (split) blocks.
   ---------------------------------------------------------------*/
void parser::
restore_control_flow_graph ()
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif 

   struct cgraph_node * cnode;
   for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
   {
       if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
           continue;

       push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));
       // current_function_decl = cnode->decl;
       // set_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

       /* Free cgraph node's aux field. */
       if (cnode->aux) {
	   DEBUG ("\nFreeing cnode->aux");
           ggc_free (cnode->aux);
           cnode->aux = NULL;
       }
       /* Free each bb's aux field. */
       basic_block cbb;
       FOR_EACH_BB (cbb) {
           if (cbb->aux) {
	       DEBUG ("\nFreeing block->aux");
               ggc_free (cbb->aux);
	       DEBUG ("\nFreed block->aux");
               cbb->aux = NULL;
           }
       }

       // Added by Vini
	basic_block startbb = get_start_block_of_function (cnode); 
	basic_block endbb = get_end_block_of_function (cnode); 
       if (startbb->aux) {
               DEBUG ("\nFreeing block->aux");
               ggc_free (startbb->aux);
	       DEBUG ("\nFreed block->aux");
               startbb->aux = NULL;
           }
        if (endbb->aux) {
               DEBUG ("\nFreeing block->aux");
               ggc_free (endbb->aux);
	       DEBUG ("\nFreed block->aux");
               endbb->aux = NULL;
           }

       /* Merge bb's if necessary. */
       DEBUG ("\ncleanup_tree_cfg ()");
       cleanup_tree_cfg ();
       /* Free the dominator info. */
       free_dominance_info (CDI_DOMINATORS);
       free_dominance_info (CDI_POST_DOMINATORS);
   
       pop_cfun ();
   }
}

void parser::
initialize_block_aux (basic_block block)
{
	// block->aux = (block_information *) ggc_alloc_cleared_atomic (sizeof (block_information));
	if (block->aux)
	{
		DEBUG ("\nblock=%d already has aux", block->index);
		return;
	}
	block->aux = new block_information ();
	DEBUG ("\nAllocated new aux to block %d", block->index);
}

void parser::
delete_parsed_data (basic_block block)
{
	DEBUG ("\nDeleting parsed data of block %d", block->index);

        list<pair<unsigned int, bool> > parsed_data_indices = 
		((block_information *)(block->aux))->get_parsed_data_indices ();

	// Multiple parsed indices may point to the same offset_sequence. For
	// example, struct node x=y->g; creates parsed assignments: x.0=y->g,
	// x.32=y->g, x.64=y->g... All these have the same rhs (and therefore
	// same offset_sequence). Therefore, first collect all offset_sequence
	// and then delete them.
	set<list<unsigned int> *> set_of_offset_sequence;

        list<pair<unsigned int, bool> >::iterator it;
        for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
        {
                unsigned int index = (*it).first;
                bool is_assignment = (*it).second;
                DEBUG ("\nDelete: Parsed data: index %d, bool %d, block %d, ", 
			index, is_assignment, block->index);

                if (!is_assignment)
			continue;
 
	        constraint_t assignment = VEC_index (constraint_t, assignment_data, index);
		DEBUG ("\nDelete assignment index=%d, addr=%x", index, assignment);
	        constraint_expr lhs = assignment->lhs;
	        constraint_expr rhs = assignment->rhs;
#if DEBUG_CONTAINER
		print_assignment_data (index);
#endif

		DEBUG ("\nGC parsed data");
		if (lhs.offset_sequence)
		{
			DEBUG ("\nDeallocate lhs.offset_sequence(addr=%x)", 
				lhs.offset_sequence);
			set_of_offset_sequence.insert (lhs.offset_sequence);
			lhs.offset_sequence = NULL;
		}
		if (rhs.offset_sequence)
		{
			DEBUG ("\nDeallocate rhs.offset_sequence(addr=%x)", 
				rhs.offset_sequence);
			set_of_offset_sequence.insert (rhs.offset_sequence);
			rhs.offset_sequence = NULL;
		}
	}

#if GC
	set<list<unsigned int> *>::iterator si;
	for (si = set_of_offset_sequence.begin (); si != set_of_offset_sequence.end (); si++)
	{
		DEBUG ("\nDelete offset_sequence=%x", *si);
		if (*si)
			delete *si;
	}
#endif
}

void parser::
delete_block_aux()
{
	DEBUG ("\ndelete_block_aux()");
        struct cgraph_node * cnode;
        for (cnode = cgraph_nodes; cnode; cnode = cnode->next)
        {
                if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
	                continue;
                push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

                basic_block bb;
                FOR_EACH_BB (bb) {
                        if (bb->aux)
                        {
				
				delete_parsed_data (bb);
#if GC
				DEBUG ("\nGC block=%d", bb->index);
                                delete (block_information *) bb->aux;
#endif
                                bb->aux = NULL;
                        }
                }
		
		bb = get_start_block_of_function (cnode); 
                if (bb->aux)
                {
			delete_parsed_data (bb);
#if GC
			DEBUG ("\nGC block=%d", bb->index);
                        delete (block_information *) bb->aux;
#endif
                        bb->aux = NULL;
                }
		bb = get_end_block_of_function (cnode); 
                if (bb->aux)
                {
			delete_parsed_data (bb);
#if GC
			DEBUG ("\nGC block=%d", bb->index);
                        delete (block_information *) bb->aux;
#endif
                        bb->aux = NULL;
                }

                pop_cfun();
        }

	main_cnode = NULL;
}


gimple_stmt_iterator parser::
split_block_at_statement (gimple statement, basic_block block)
{
	edge e = split_block (block, statement);
	block = e->dest;

	// Initialize the newly created basic block
	initialize_block_aux (block);

	return gsi_start_bb (block);
}

set<unsigned int> parser::
get_global_variables ()
{
	set<unsigned int> global_vars;
	get_global_variables (global_vars);
	return global_vars;
}

void parser::
get_global_variables (set<unsigned int> & global_vars)
{
	FUNBEGIN ();

	DEBUG ("\nVariable data:");
	for (unsigned int index = 0; index < VEC_length (csvarinfo_t, variable_data); index++)
	{
		// void* type of heap locations are global_var but we do not
		// want to consider them; therefore, !heap_var() condition is
		// checked.
		if (is_proper_var (index) && global_var (index) && !heap_var (index))
		{
			#if DEBUG_CONTAINER
	        	csvarinfo_t variable = VEC_index (csvarinfo_t, variable_data, index);
        		DEBUG ("\nVariable id %d, name %s, offset %llu", 
				variable->id, variable->name, variable->offset);
			#endif
			global_vars.insert (index);
		}
	}

	RETURN_VOID ();
}

set<unsigned int> parser::
get_global_heap_variables ()
{
	set<unsigned int> global_heap_vars;

	DEBUG ("\nVariable data:");
	for (unsigned int index = 0; index < VEC_length (csvarinfo_t, variable_data); index++)
	{
	        csvarinfo_t variable = VEC_index (csvarinfo_t, variable_data, index);
		if (is_proper_var (index) && (global_var (index) || heap_var (index)))
		{
        		DEBUG ("\nVariable id %d, name %s, offset %llu", 
				variable->id, variable->name, variable->offset);
			global_heap_vars.insert (index);
		}
	}

	return global_heap_vars;
}

set<unsigned int> parser::
get_global_named_pointers ()
{
	set<unsigned int> global_vars;
	get_global_named_pointers (global_vars);
	return global_vars;
}

void parser::
get_global_named_pointers (set<unsigned int> & global_vars)
{
	DEBUG ("\nget_global_named_variables ()");

	for (unsigned int index = 0; index < VEC_length (csvarinfo_t, variable_data); index++)
	{
		if (!global_var (index))
			continue;

	        csvarinfo_t gvar = VEC_index (csvarinfo_t, variable_data, index);
        	DEBUG ("\nVariable id %d, name %s, offset %llu", 
			gvar->id, gvar->name, gvar->offset);

		if (!is_proper_var (gvar->id))
			continue;

		if (gvar && gvar->decl && TREE_CODE (gvar->decl) == FUNCTION_DECL)
			continue;
	
		if (gvar->is_heap_var)
			continue;

		if (!field_must_have_pointers (gvar->decl))
			continue;

		global_vars.insert (index);
	}
}

set<unsigned int> parser::
get_function_arguments (basic_block call_site, struct cgraph_node * src_function)
{
   // FIXME: check that this a call_site has only one statement.
   gimple_stmt_iterator gsi = gsi_start_bb (call_site);
   gimple call_stmt = gsi_stmt (gsi);
#if DEBUG_CONTAINER
   DEBUG ("\ncall_stmt: ");
   print_gimple_stmt (dump_file, call_stmt, 0, 0);
   DEBUG ("\ngimple_call_num_args = %d", gimple_call_num_args (call_stmt));
#endif
   set<unsigned int> args;
   for (int j = 0; j < gimple_call_num_args (call_stmt); j++) {
       tree arg = gimple_call_arg (call_stmt, j);
       if (field_must_have_pointers (arg)) {
               VEC (ce_s, heap) *results = NULL;
               cs_get_constraint_for (arg, &results, call_site, src_function);
       	       struct constraint_expr *exp;
               unsigned i;
               FOR_EACH_VEC_ELT (ce_s, results, i, exp)
	       {
	           DEBUG ("\narg_info %d", exp->var);
		   args.insert (exp->var);
	       }
               VEC_free (ce_s, heap, results);
       }
   }
   return args;
}

set<unsigned int> parser::
get_function_parameters (struct cgraph_node * function)
{
	set<unsigned int> function_parameters;
	get_function_parameters (function, function_parameters);
	return function_parameters;
}

void parser::
get_function_parameters (struct cgraph_node * function,
	set<unsigned int> & function_parameters)
{
	FUNBEGIN ();

	tree args;
	DEBUG ("\nParameters: ");
	for (args = DECL_ARGUMENTS (function->decl); args; args = TREE_CHAIN (args))
	{
#if DEBUG_CONTAINER
		const char * function_name = cgraph_node_name (function);
		DEBUG ("\n%s arg: ", function_name);
		print_node_brief (dump_file, "", args, 0);
#endif
		if (TREE_CODE(args) != PARM_DECL || is_global_var (args))
		{
			RESULT ("\nError: argument is not PARM_DECL");
			continue;
		}

		unsigned int aid = get_tree_index (args);
		if (aid)
			function_parameters.insert (aid);
	}

	RETURN_VOID ();
}

set<unsigned int> parser::
get_local_variables (struct cgraph_node * function)
{
	set<unsigned int> local_variables;
	get_local_variables (function, local_variables);
	return local_variables;
}

void parser::
get_local_variables (struct cgraph_node * function,
	set<unsigned int> & local_variables)
{
	FUNBEGIN ();

#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif

	// FIXME: Pathetic coding here:
	for (int index = 0; index < VEC_length (csvarinfo_t, variable_data); index++)
	{
		csvarinfo_t variable = cs_get_varinfo (index);
		struct cgraph_node * cnode = variable->scoping_function;
		if (cnode && function == cnode && variable->decl 
			// Can this ever be the case?
			&& TREE_CODE(variable->decl) != PARM_DECL
			// Can this ever be the case?
			&& !variable->is_global_var
			&& cs_lookup_vi_for_tree (variable->decl))	// discards main.varargs variable
			local_variables.insert (variable->id);
#if DEBUG_CONTAINER
		const char * function_name = NULL;
		if (cnode)
			function_name = cgraph_node_name (cnode);
		DEBUG ("\nLocal variable id %d, name %s, offset %llu, scoping function %s", 
			variable->id, variable->name, variable->offset, function_name);
#endif
	}

	RETURN_VOID ();

#if 0
	// FIXME: Pathetic coding here:

	// BUG: FOR_EACH_LOCAL_DECL returns only z.0+32 tree out of
	// {z.0+32,z.32+32,z.64+32}.

	set<unsigned int> local_variables;
	tree fn = function->decl;
	unsigned u;
	tree var;
	DEBUG ("\nParser local variables: ");
	FOR_EACH_LOCAL_DECL (DECL_STRUCT_FUNCTION (fn), u, var)
	{
		local_variables.insert (get_tree_index (var));
#if DEBUG_CONTAINER
		DEBUG ("\n");
		print_node_brief (dump_file, "", var, 0);
#endif
	}
	DEBUG ("\ndone");

	return local_variables;
#endif
}

/**
 * This function inserts all non-temporary, non-parameter, non-global
 * pointer variables of CURRENT_FUNCTION.
 */

set<unsigned int> parser::
get_local_non_temp_pointers (struct cgraph_node * current_function)
{
	DEBUG ("\nget_local_non_temp_pointers");
	DEBUG ("\nlocal_non_temp_pointers");

	set<unsigned int> local_non_temp_pointers;
	for (int index = 0; index < VEC_length (csvarinfo_t, variable_data); index++)
	{
		csvarinfo_t variable = cs_get_varinfo (index);
		struct cgraph_node * cnode = variable->scoping_function;
		if (cnode && current_function == cnode 
			&& variable->decl 
			&& !DECL_ARTIFICIAL (variable->decl)
			&& TREE_CODE(variable->decl) != PARM_DECL
			&& !variable->is_global_var
			&& field_must_have_pointers (variable->decl)
			&& cs_lookup_vi_for_tree (variable->decl))	// discards main.varargs variable
		{
			local_non_temp_pointers.insert (variable->id);
#if DEBUG_CONTAINER
			const char * function_name = NULL;
			if (cnode)
				function_name = cgraph_node_name (cnode);
			DEBUG ("\nVariable id %d, name %s, offset %llu, scoping function %s", 
				variable->id, variable->name, variable->offset, function_name);
#endif
		}
	}
	return local_non_temp_pointers;
}

unsigned int parser::
get_tree_index (tree v)
{
	//FIXME: Pathetic coding here:

	for (int index = 0; index < VEC_length (csvarinfo_t, variable_data); index++)
	{
	        csvarinfo_t variable = VEC_index (csvarinfo_t, variable_data, index);
		if (variable->decl == v)
		{
#if DEBUG_CONTAINER
			DEBUG ("\nVariable id %d, name %s, offset %llu", 
				variable->id, variable->name, variable->offset);
#endif
			return variable->id;
		}
	}
	return 0;
}

void parser::
get_loop_use_sites (set<unsigned int> & recursive_fns)
{
	struct cgraph_node * cnode = NULL; 
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		// https://gcc.gnu.org/onlinedocs/gccint/Loop-representation.html
		// loop_optimizer_init (0);
		// loop_optimizer_init (LOOPS_MAY_HAVE_MULTIPLE_LATCHES);
		loop_optimizer_init (AVOID_CFG_MODIFICATIONS);

#if DEBUG_CONTAINER
                DEBUG ("\nFunction : %s\n", cgraph_node_name (cnode));
		if (!cfun) 
			RESULT ("\nError: cfun is NULL");
		study_loops ();
#endif

                DEBUG ("\nFunction : %s\n", cgraph_node_name (cnode));
		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
			if (!current_block->aux)
				return;
		
		        list<pair<unsigned int, bool> > parsed_data_indices = 
				((block_information *)(current_block->aux))->get_parsed_data_indices ();
		
		        list<pair<unsigned int, bool> >::iterator it;
		        for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
		        {
		                unsigned int index = (*it).first;
		                bool is_assignment = (*it).second;
		                DEBUG ("\nParsed data: index %d, bool %d, block %d, ", 
					index, is_assignment, current_block->index);
		
		                if (is_assignment)
				{
				        constraint_t assignment = VEC_index (constraint_t, assignment_data, index);
					DEBUG ("\nassignment index=%d, addr=%x", index, assignment);
				        constraint_expr rhs = assignment->rhs;
				        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, variable_data, rhs.var);
					if (rhs.type == DEREF)
					{
						DEBUG ("\nUSE_SITE=%s(%d)", rhs_variable->name, rhs_variable->id);
						unsigned int fid = rhs_variable->scoping_function->uid;
						if (current_block->loop_father && current_block->loop_father->num)
						{
							RESULT ("\nSite=%d in loop", index);
							print_assignment_data (index);
							loop_use_sites.insert (index);
						}
						else if (recursive_fns.find (fid) != recursive_fns.end ())
						{
							RESULT ("\nSite=%d in recursion", index);
							print_assignment_data (index);
							loop_use_sites.insert (index);
						}
					}
				}
		        }
		
		}

		loop_optimizer_finalize ();

		pop_cfun();
	}
}

void parser::
handle_unknown_offset (constraint_expr & e)
{
	// if (e.offset == UNKNOWN_OFFSET)	
	//	RESULT ("\nError: offset = UNKNOWN_OFFSET");
	// else
	//	DEBUG ("\noffset = %llu", e.offset);

	// FIXME: all UNKNOWN_OFFSET are not getting recognized. For example,
	// hmmer, function regatom(), bb 18, D.20045_38 = D.20044_37 + -2;
	// rhs.offset=2*UNKNOWN_OFFSET-192.

	// FIXME: bzip2, function sendMTFValues, D.4498_1348 = &s_59(D)->len[t_13][0];
	// The offset is UNKNOWN_OFFSET but pointer_arithmetic=0.

#if 0
	// In case of pointer arithmetic, offset is an integral multiple of
	// UNKNOWN_OFFSET.
	if (e.offset && e.offset % UNKNOWN_OFFSET == 0)
	{
	        csvarinfo_t variable = VEC_index (csvarinfo_t, variable_data, e.var);
		RESULT ("\ne.var=%s(%d), e.type=%d, e.ptr_arith=%d, e.offset=unknown_offset", 
			variable->name, e.var, e.type, e.pointer_arithmetic);
	}
#endif
	if (e.pointer_arithmetic)
	{
	        csvarinfo_t variable = VEC_index (csvarinfo_t, variable_data, e.var);
		RESULT ("\ne.var=%s(%d), e.type=%d, e.ptr_arith=%d, e.offset=unknown_offset", 
			variable->name, e.var, e.type, e.pointer_arithmetic);
	}
}

void parser::
save_heap_location (gimple stmt, unsigned int heapvar)
{
	if (!stmt) return;
	if (!gimple_has_location (stmt)) return;
	expanded_location xloc = expand_location (gimple_location (stmt));
	heap_location[heapvar] = xloc;
}

void parser::
print_block_statements (basic_block block)
{
	FUNBEGIN ();

	RESULT ("\n");
	gimple_stmt_iterator gsi;
	for (gsi = gsi_start_bb (block); !gsi_end_p (gsi); gsi_next (&gsi))
		if (dump_file)
			print_gimple_stmt (dump_file, gsi_stmt (gsi), 0, 0);

	RETURN_VOID ();
}

bool parser::
print_source_location (basic_block block)
{
	if (!block) return false;
	gimple_stmt_iterator gsi = gsi_start_bb (block);
	if (gsi_end_p (gsi)) return false;
	gimple stmt = gsi_stmt (gsi);
	if (!stmt) return false;
	if (!gimple_has_location (stmt)) return false;
	expanded_location xloc = expand_location (gimple_location (stmt));
	INFO ("\n\nFile %s, Line %d", xloc.file, xloc.line);
	INFO ("\n");
	for (gsi = gsi_start_bb (block); !gsi_end_p (gsi); gsi_next (&gsi))
		print_gimple_stmt (dump_file, gsi_stmt (gsi), 0, 0);

	return true;
}

void parser::
print_heap_location (csvarinfo_t variable)
{
	expanded_location xloc = heap_location[variable->id];
	INFO (" -- File %s Line %d", xloc.file, xloc.line);
}

void parser::
print_variable_data ()
{
	INFO ("\n\nVARIABLES\n=========\n");
	DEBUG ("\nVariable data:");
	DEBUG ("\npassed addr of program.variable_data=%x", variable_data);
	for (int index = 0; index < VEC_length (csvarinfo_t, variable_data); index++)
	{
	        csvarinfo_t variable = VEC_index (csvarinfo_t, variable_data, index);
		const char * function_name = NULL;
		if (variable && variable->scoping_function)
			function_name = cgraph_node_name (variable->scoping_function);
        	DEBUG ("\nVariable id %d, name %s, offset %llu, function %s", 
			variable->id, variable->name, variable->offset, function_name);
        	INFO ("\n%s(%d)", variable->name, variable->id);
		if (variable->is_heap_var)
			print_heap_location (variable);
		else if (variable->decl)
			INFO (" -- File %s Line %d", 
				DECL_SOURCE_FILE (variable->decl), DECL_SOURCE_LINE (variable->decl));
	}
	INFO ("\n");
}

void parser::
print_assignment_data ()
{
	DEBUG ("\nAssignment data:");
	for (int index = 0; index < VEC_length (constraint_t, assignment_data); index++)
	{
	        constraint_t assignment = VEC_index (constraint_t, assignment_data, index);
        	constraint_expr lhs = assignment->lhs;
	        constraint_expr rhs = assignment->rhs;
        	csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, variable_data, lhs.var);
	        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, variable_data, rhs.var);
	        RESULT ("\nLHS: variable id %d, ptr_arith=%d, offset %llu(", 
        	        lhs.var, lhs.pointer_arithmetic, lhs.offset);
		list<unsigned int>::iterator ofi;
		if (lhs.offset_sequence)
			for (ofi = lhs.offset_sequence->begin (); ofi != lhs.offset_sequence->end (); ofi++)
				RESULT ("%d,", *ofi);
	        RESULT ("), type %d, name %s", 
        	        lhs.type, lhs_variable->name);

		RESULT (" RHS: variable id %d, ptr_arith=%d, offset %llu(",
	                rhs.var, rhs.pointer_arithmetic, rhs.offset);
		if (rhs.offset_sequence)
			for (ofi = rhs.offset_sequence->begin (); ofi != rhs.offset_sequence->end (); ofi++)
				RESULT ("%d,", *ofi);
		RESULT ("), type %d, name %s",
	                rhs.type, rhs_variable->name);

		RESULT (", previous_phi=%d", assignment->previous_phi != NULL);
	}
}

void parser::
print_variable_data (int index)
{
        csvarinfo_t variable = VEC_index (csvarinfo_t, variable_data, index);
        RESULT ("Variable id %d, name %s, offset %llu", variable->id, variable->name, variable->offset);

	DEBUG ("\nNext field in structure:");
	csvarinfo_t vi;
	for (vi = variable; vi; vi = vi->next)
		RESULT ("\nVar id %d, name %s, offset %llu", vi->id, vi->name, vi->offset); 
}

void parser::
print_assignment_data (int index)
{
        constraint_t assignment = VEC_index (constraint_t, assignment_data, index);
	DEBUG ("\nassignment index=%d, addr=%x", index, assignment);
        constraint_expr lhs = assignment->lhs;
        constraint_expr rhs = assignment->rhs;
        csvarinfo_t lhs_variable = VEC_index (csvarinfo_t, variable_data, lhs.var);
        csvarinfo_t rhs_variable = VEC_index (csvarinfo_t, variable_data, rhs.var);
        RESULT ("\nLHS: variable id %d, ptr_arith=%d, offset %llu(",
                lhs.var, lhs.pointer_arithmetic, lhs.offset);
	list<unsigned int>::iterator ofi;
	if (lhs.offset_sequence)
		for (ofi = lhs.offset_sequence->begin (); ofi != lhs.offset_sequence->end (); ofi++)
			RESULT ("%d,", *ofi);
	RESULT ("), type %d, name %s, RHS: variable id %d, ptr_arith=%d, offset %llu(",
		lhs.type, lhs_variable->name, 
                rhs.var, rhs.pointer_arithmetic, rhs.offset);
	if (rhs.offset_sequence)
		for (ofi = rhs.offset_sequence->begin (); ofi != rhs.offset_sequence->end (); ofi++)
			RESULT ("%d,", *ofi);
	RESULT ("), type %d, name %s",
                rhs.type, rhs_variable->name);
		
	RESULT (", previous_phi=%d", assignment->previous_phi != NULL);
}

void parser::
print_parsed_data (basic_block current_block)
{
	DEBUG ("\nPrinting parsed data of block %d", current_block->index);

	if (!current_block->aux)
		return;

        list<pair<unsigned int, bool> > parsed_data_indices = 
		((block_information *)(current_block->aux))->get_parsed_data_indices ();

        list<pair<unsigned int, bool> >::iterator it;
        for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
        {
                unsigned int index = (*it).first;
                bool is_assignment = (*it).second;
                RESULT ("\nParsed data: index %d, bool %d, block %d, ", 
			index, is_assignment, current_block->index);

                if (is_assignment)
                        print_assignment_data (index);
                else
                        print_variable_data (index);
        }
}

void parser::
print_parsed_data ()
{
	DEBUG ("\nprint_parsed_data ()");
	DEBUG ("\nUNKNOWN_OFFSET %llu", UNKNOWN_OFFSET);

   	struct cgraph_node * cnode = NULL; 
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

                RESULT ("\nFunction : %s\n", cgraph_node_name (cnode));

		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
			unsigned int bt = ((block_information *)(current_block->aux))->get_block_type ();
			RESULT ("\nBLOCK=%d, BLOCK_TYPE=%d", current_block->index, bt);
			print_block_statements (current_block);
			print_parsed_data (current_block);
		}

		pop_cfun();
	}
}

unsigned int parser::
count_ptr_stmts ()
{
	unsigned int ptr_stmt_count = 0;

   	struct cgraph_node * cnode = NULL; 
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
			if (!current_block->aux)
				continue;
        
			list<pair<unsigned int, bool> > parsed_data_indices = 
				((block_information *)(current_block->aux))->get_parsed_data_indices ();

		        list<pair<unsigned int, bool> >::iterator it;
		        for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
		        {
		                bool is_assignment = (*it).second;
		                if (is_assignment)
					ptr_stmt_count++;				
			}
		}

		pop_cfun();
	}

	return ptr_stmt_count;
}

#if HEAP_TYPE_BASED_NAME
void parser::
print_heap_type_id ()
{
	map<tree, unsigned int>::iterator hi;
	for (hi = heap_type_id.begin (); hi != heap_type_id.end (); hi++)
	{
		tree t = hi->first;
		unsigned int hid = hi->second;
		RESULT ("\nHEAP id=%d ->\n\t", hid);
		print_node (dump_file, 0, t, 0);
	}
}
#endif

void parser::
print_heap_to_alloc_site ()
{
	DEBUG ("\nheap_to_alloc_sites=");
	map<unsigned int, unsigned int>::iterator hsi;
	for (hsi = heap_to_alloc_site.begin (); hsi != heap_to_alloc_site.end (); hsi++)
	{
		csvarinfo_t hvar = VEC_index (csvarinfo_t, variable_data, hsi->first); 
		DEBUG ("(%s(%d),%d),", hvar->name, hvar->id, hsi->second);
	}
}

void parser::
print_alloc_site_typecasts ()
{
	DEBUG ("\nprint_alloc_site_typecasts ()");
	map<unsigned int, set<tree> >::iterator hi;
	for (hi = alloc_site_typecasts.begin (); hi != alloc_site_typecasts.end (); hi++)
	{
		unsigned int as = hi->first;
		set<tree> types = hi->second;
		set<tree>::iterator ti;	
		for (ti = types.begin (); ti != types.end (); ti++)
		{
			csvarinfo_t type_varinfo = cs_lookup_vi_for_tree (*ti);
			if (!type_varinfo)
			{
				RESULT ("\nError: Typecaste of alloc_site=%d not found", as);
				continue;
			}	
			DEBUG ("\nTypecaste of alloc_site=%d is in %s(%d)",
				as, type_varinfo->name, type_varinfo->id);
		}
	}
	DEBUG ("\nprint_alloc_site_typecasts () done");
}

bool parser::
is_cfg_ptr_asgn_empty (struct cgraph_node * cnode)
{
	unsigned int cnid = cnode->uid;
	return ptr_asgn_empty_cfg.find (cnid) != ptr_asgn_empty_cfg.end ();
}

/*
 * FIXME: If all called functions are ptr_asgn_empty, then mark THIS function
 * also ptr_asgn_empty.
 */

void parser::
is_cfg_ptr_asgn_empty ()
{
   	struct cgraph_node * cnode = NULL; 
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		bool empty = true;

                DEBUG ("\nFunction : %s\n", cgraph_node_name (cnode));
		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
			if (!current_block->aux)
				continue;

                	DEBUG ("\nBlock : %d\n", current_block->index);
		
			unsigned int bt = ((block_information *)(current_block->aux))->get_block_type ();
			if ((bt & CALL_BLOCK) && !(bt & AUX_BLOCK))
			{
				empty = false;
				break;
			}

		        list<pair<unsigned int, bool> > parsed_data_indices = 
				((block_information *)(current_block->aux))->get_parsed_data_indices ();
		
		        list<pair<unsigned int, bool> >::iterator it;
		        for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
		        {
		                unsigned int index = (*it).first;
		                bool is_assignment = (*it).second;
		                DEBUG ("\nParsed data: index %d, bool %d, block %d, ", 
					index, is_assignment, current_block->index);
		
		                if (is_assignment)
				{
					empty = false;
					break;
				}

		        }
			if (!empty)
				break;
		}
                RESULT ("\nFunction : %s, empty=%d", cgraph_node_name (cnode), empty);
		if (empty)
			ptr_asgn_empty_cfg.insert (cnode->uid);

		pop_cfun();
	}
}

void parser::
print_original_cfg ()
{
#if DEBUG_CONTAINER
	FUNCTION_NAME ();
#endif 

   	struct cgraph_node * cnode = NULL; 
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

#if DEBUG_CONTAINER
		DEBUG ("\nFunction : %s\n", cgraph_node_name (cnode));
#endif
		int n = 1;
		basic_block current_block;
		FOR_EACH_BB (current_block) 
		{
			DEBUG ("\nBlock : %d\n", current_block->index);
			gimple_stmt_iterator gsi;
#if DEBUG_CONTAINER
			for (gsi = gsi_start_bb (current_block); !gsi_end_p (gsi); gsi_next (&gsi))
			{
				DEBUG ("%d: ", n++);
				print_gimple_stmt (dump_file, gsi_stmt (gsi), 0, 0);
			}
#endif
		}

		pop_cfun();
	}
}

void parser::
collect_uid_to_cnode ()
{
        for (struct cgraph_node * node = cgraph_nodes; node; node = node->next)
        {
                if (gimple_has_body_p (node->decl))
                {
                        tree decl = node->decl;
                        uid_to_cnode [DECL_PT_UID (decl)] = node;
                }
        }
}

/** This function prints the points-to pairs computed by -fipa-pta pass.
 * Therefore, the test file should be executed with -O3 -fipa-pta option.
 */

void parser::
print_original_gcc_points_to_pairs ()
{
	RESULT ("\n\nGCC points-to pairs\n\n");

	struct cgraph_node * cnode;
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next) 
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

		current_function_decl = cnode->decl;
		dump_alias_info (dump_file);
		current_function_decl = NULL;

		pop_cfun();
	}
}

/** This function prints the points-to pairs computed by -fipa-pta pass.
 * Therefore, the test file should be executed with -O3 -fipa-pta option.
 */

void parser::
print_gcc_fn_pointees ()
{
	collect_uid_to_cnode ();

	DEBUG ("\n\nprint_gcc_points_to_pairs\n");

	struct cgraph_node * cnode;
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next)
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));
		DEBUG ("\nFunction %s", cgraph_node_name (cnode));
		DEBUG ("\nnum_ssa_names=%d", num_ssa_names);

		// if (cfun->gimple_df->ipa_pta)
		// {
		//      DEBUG ("\ndump_alias_info ()");
		//      dump_alias_info (dump_file);
		// }

		// for (size_t i = 1; i < num_ssa_names; i++)
		// {
		//	tree ptr = ssa_name (i);
		//	if (ptr == NULL_TREE || SSA_NAME_IN_FREE_LIST (ptr))
		//	{
		//		DEBUG ("\nNULL_TREE or SSA_NAME_IN_FREE_LIST");
		//		continue;
		//	}

		//	print_gcc_points_to_pairs (ptr);
		// }

		basic_block bb;
		FOR_EACH_BB (bb)
		{
			for (gimple_stmt_iterator gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next (&gsi))
			{
				gimple stmt = gsi_stmt(gsi);

				if (gimple_code (stmt) == GIMPLE_CALL)
				{
					/* If we can resolve it here, its a simple function call. */
					tree decl = gimple_call_fndecl (stmt);
					/* The call is through function pointer. */
					if (!decl)
					{
						#if DEBUG_CONTAINER
						print_gimple_stmt (dump_file, stmt, 0, 0);
						#endif
	
						decl = gimple_call_fn (stmt);
						#if DEBUG_CONTAINER
						print_generic_expr (dump_file, decl, 0);
						#endif

						set<struct cgraph_node *> fn_pointees;
						get_gcc_fn_pointees (decl, fn_pointees);
				 	}
				}
			}
		}

		pop_cfun();
	}
}

/** This function is defined in dump_alias_info () of gcc/tree-ssa-alias.c.
 */

void parser::
get_gcc_fn_pointees (tree ptr, set<struct cgraph_node *> & fn_pointees)
{
	DEBUG ("\nprint_gcc_points_to_pairs()");

	// tree var = SSA_NAME_VAR (ptr);
	// tree decl_name = DECL_NAME (var);
	// if (decl_name)
	//      DEBUG ("\n%s->", IDENTIFIER_POINTER (decl_name));

	DEBUG ("\n");
	#if DEBUG_CONTAINER
	print_generic_expr (dump_file, ptr, 0);
	#endif
	// bool is_fp = false;
	// if (TREE_TYPE (ptr)
	//	&& TREE_CODE (TREE_TYPE (ptr)) == POINTER_TYPE
	//	&& TREE_CODE (TREE_TYPE (TREE_TYPE (ptr))) == FUNCTION_TYPE)
	// {
	//	is_fp = true;
	//	DEBUG ("(fp)");
	// }
	DEBUG (" -> ");

	// dump_points_to_info_for (dump_file, ptr);
	// Following prints same as above.

	struct ptr_info_def * pi = SSA_NAME_PTR_INFO (ptr);
	if (!pi)
	{
		DEBUG ("SSA not found, ");
		return;
	}

	struct pt_solution * pt = &(pi->pt);

	if (pt->anything)
	{
		RESULT ("\nGCC function pointee: Anything");
		fn_pointees.insert (addr_taken_functions.begin (), addr_taken_functions.end ());
		return;
	}

	if (pt->nonlocal)
		DEBUG ("non-local, ");

	if (pt->escaped)
		DEBUG ("escaped, ");

	if (pt->ipa_escaped)
		DEBUG ("unit escaped, ");

	if (pt->null)
		DEBUG ("NULL, ");

	if (pt->vars)
	{
		DEBUG ("\npt->vars");
		bitmap pointees = pt->vars;
		int cnt = bitmap_count_bits (pointees);

		// dump_decl_set (dump_file, pt->vars);

		// Loop over all bits set in pointee, starting
		// with 0 and setting rhsbit to the bit number
		bitmap_iterator bi;
		unsigned int rhsbit;
		EXECUTE_IF_SET_IN_BITMAP (pointees, 0, rhsbit, bi)
		{
			DEBUG ("\nin EXECUTE_IF_SET_IN_BITMAP\n");
			struct cgraph_node * fn_cnode = uid_to_cnode[rhsbit];
			if (fn_cnode) // True for global vars
			{
				DEBUG (" %s", IDENTIFIER_POINTER (DECL_NAME (fn_cnode->decl)));
	
   				csvarinfo_t fi = cs_lookup_vi_for_tree (fn_cnode->decl);
				if (fi)
					DEBUG ("(%d)", fi->id);
				fn_pointees.insert (fn_cnode);
				// print_node (dump_file, "", uid_to_cnode[rhsbit], 0);
			}
			// tree var = referenced_var_lookup (cfun, rhsbit);
			// if (var)
			//	print_generic_expr (dump_file, var, 0);
			else
			{
				// This is reported when the pointee is
				// non-function pointer when it is
				// reported as a temporary. E.g. test63.c
				// D.2363 points to fn and arr. arr is
				// reported as D.2355.
				RESULT ("\nError: gcc function pointee of ");
				print_generic_expr (dump_file, ptr, 0);
				RESULT (" is temp = D.%u", rhsbit);
			}
			DEBUG (", ");
		}

		// if (pt->vars_contains_global)
		//	DEBUG ("global, ");
	}

	else
		DEBUG ("NIL, ");
}

bool parser::
is_in_scope (unsigned int var,
	struct cgraph_node * cnode)
{
	csvarinfo_t varinfo = program.cs_get_varinfo (var);

	if (varinfo->is_global_var)
		return true;

	if (varinfo->scoping_function == cnode)
		return true;

	DEBUG ("\n function=%s, var=%s(%d)", 
		cgraph_node_name (cnode), varinfo->name, var);
	return false;
}


struct cgraph_node * parser:: 
get_cgraph_node (const char * function_name)
{
	// FIXME: Find direct function for this
	struct cgraph_node * cnode;
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next)
		if (strcmp (cgraph_node_name (cnode), function_name) == 0)
			return cnode;

	return NULL;
}

struct cgraph_node * parser::
get_cgraph_node (unsigned int fid)
{
	// FIXME: Find direct function for this
	struct cgraph_node * cnode;
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next)
		if (cnode->uid == fid)
			return cnode;

	return NULL;
}

struct function * parser::
get_struct_function (tree decl)
{
	if (!decl)
		return NULL;
	return DECL_STRUCT_FUNCTION (decl);
}

tree parser::
get_tree (struct cgraph_node * cnode)
{
	if (!cnode)
		return NULL;
	return cnode->decl;
}

tree parser::
get_tree (struct function * func)
{
	if (!func)
		return NULL;
	return func->decl;
}

struct cgraph_node * parser::
get_cgraph_node (tree decl)
{
	return cgraph_get_node (decl);
}

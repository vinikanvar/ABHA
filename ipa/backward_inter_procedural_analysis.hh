
/*******************************************************************************
  * The data structures here are a refactoring of those in the paper:
  * Rohan Padhye and Uday P. Khedker. Interprocedural data flow analysis in soot
  * using value contexts. In Proceedings of the 2nd ACM SIGPLAN International
  * Workshop on State Of the Art in Java Program Analysis, SOAP ’13, pages 31
  * –36, New York, NY, USA, 2013. ACM.
*******************************************************************************/  

/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef BACKWARD_INTER_PROCEDURAL_ANALYSIS
#define BACKWARD_INTER_PROCEDURAL_ANALYSIS

#include "../misc/debug.hh"
#include "../misc/block_information.hh"
#include "../ipa/context.hh"
#include "../ipa/inter_procedural_analysis.hh"

typedef unsigned int context_index; 

template <class value_type, class dept_value_type>
class backward_inter_procedural_analysis: public inter_procedural_analysis<value_type, dept_value_type>
{

public:

        using inter_procedural_analysis<value_type, dept_value_type>::is_value_context;
        using inter_procedural_analysis<value_type, dept_value_type>::dependent_analysis;
        using inter_procedural_analysis<value_type, dept_value_type>::get_dependent_context;
        using inter_procedural_analysis<value_type, dept_value_type>::get_context_enums;
        using inter_procedural_analysis<value_type, dept_value_type>::get_dest_of_dept_context;
        using inter_procedural_analysis<value_type, dept_value_type>::get_context;
        using inter_procedural_analysis<value_type, dept_value_type>::get_function_context;
        using inter_procedural_analysis<value_type, dept_value_type>::is_recursively_called;
        using inter_procedural_analysis<value_type, dept_value_type>::is_context_in_worklist;
        using inter_procedural_analysis<value_type, dept_value_type>::add_context_to_worklist;
	using inter_procedural_analysis<value_type, dept_value_type>::update_context_worklist;
        using inter_procedural_analysis<value_type, dept_value_type>::add_dependent_context_to_worklist;
        using inter_procedural_analysis<value_type, dept_value_type>::get_block_of_function;
        using inter_procedural_analysis<value_type, dept_value_type>::get_context_enums_size;
        using inter_procedural_analysis<value_type, dept_value_type>::initial_value;
        using inter_procedural_analysis<value_type, dept_value_type>::boundary_value;
        using inter_procedural_analysis<value_type, dept_value_type>::add_new_context;
        using inter_procedural_analysis<value_type, dept_value_type>::delete_local_variables;
        using inter_procedural_analysis<value_type, dept_value_type>::print_context_worklist;
        using inter_procedural_analysis<value_type, dept_value_type>::print_program_contexts;

	backward_inter_procedural_analysis (bool is_val_context);
	context<value_type, dept_value_type> * get_same_dest_context (struct cgraph_node * dest_function, value_type & value, context<dept_value_type, value_type> * dept_context);
	void set_boundary_value (context<value_type, dept_value_type> * new_context, value_type * boundary_value);
	void add_adjacent_blocks_to_worklist (context<value_type, dept_value_type> * current_context, basic_block current_block);
	virtual bool process_parsed_data (context<value_type, dept_value_type> * current_context, basic_block current_block, value_type * calling_value, bool to_kill = true) = 0;
	virtual void process_call_statement (context<value_type, dept_value_type> * src_context, basic_block call_site) = 0;
	value_type * process_destination_context (context<value_type, dept_value_type> & src_context, basic_block call_site, struct cgraph_node * dest_function, value_type * calling_value);
	value_type * process_existing_dest_context (context<value_type, dept_value_type> & src_context, basic_block call_site, struct cgraph_node * dest_function, context<value_type, dept_value_type> & existing_dest_context);
	void process_new_dest_context (context<value_type, dept_value_type> & src_context, basic_block call_site, struct cgraph_node * dest_function, value_type & calling_value, context<dept_value_type, value_type> * dest_dept_context);
	value_type * process_destination_context (struct cgraph_node * dest_function, value_type * calling_value);
	value_type * get_function_value (struct cgraph_node * dest_function);
	bool analyze_block (context<value_type, dept_value_type> * current_context, basic_block current_block);
	void compute_in (context<value_type, dept_value_type> * current_context, basic_block current_block);
	bool compute_out_single_succ (context<value_type, dept_value_type> * current_context, basic_block current_block);
	void compute_out_multiple_succ (context<value_type, dept_value_type> * current_context, basic_block current_block);
	void compute_out (context<value_type, dept_value_type> * current_context, basic_block current_block);
	void copy_out_to_in (context<value_type, dept_value_type> * current_context, basic_block current_block);
	virtual void print_value (value_type & v) = 0;
	void set_block_order (basic_block block, int rev_post_order);
};

#endif

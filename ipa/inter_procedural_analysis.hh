
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

#ifndef INTER_PROCEDURAL_ANALYSIS
#define INTER_PROCEDURAL_ANALYSIS

#include "../misc/debug.hh"
#include "../misc/block_information.hh"
#include "../ipa/context.hh"

/** Each cgraph_node (function) will be given a unique number */
typedef unsigned int function_index; 
typedef unsigned int context_index; 

template <class value_type, class dept_value_type>
class inter_procedural_analysis
{
	// Worklist of contexts to be analyzed
	// This needs to be a stack, and not an unordered set, because in case
	// of a function call, we want to push the called context on the
	// CONTEXT_WORKLIST, postpone the processing of the current function,
	// and take up the blocks of the called context.
	stack<context<value_type, dept_value_type> *> context_worklist;

	// Set of all the contexts
	context_enums<value_type, dept_value_type> program_contexts;

	// Map from each function to its contexts
	map<function_index, context_enums<value_type, dept_value_type> > function_contexts_map;

public:
	// True if IPA is based on value context approach. False if it is based on functional approach.
	bool is_value_context;
	
private:

	context<value_type, dept_value_type> * get_context_from_worklist ();
	
protected:

	inter_procedural_analysis<dept_value_type, value_type> * dependent_analysis;

	basic_block get_block_of_function (struct cgraph_node * cnode, block_index bid);
	context<value_type, dept_value_type> * get_context (context_index cid);

	void print_context_worklist ();
	virtual void print_analysis_statistics (map<function_index, context_enums<value_type, dept_value_type> > & function_contexts) = 0;
	virtual void print_bypassing_analysis_statistics (map<function_index, context_enums<value_type, dept_value_type> > & function_contexts);


	void update_context_worklist (context<value_type, dept_value_type> & src_context, context<value_type, dept_value_type> & existing_dest_context, struct cgraph_node * dest_function);
	context<value_type, dept_value_type> * add_new_context (struct cgraph_node * cnode, value_type * boundary_value, context<value_type, dept_value_type> * source_context, basic_block call_site, context<dept_value_type, value_type> * dependent_context);
	virtual void set_boundary_value (context<value_type, dept_value_type> * new_context, value_type * boundary_value) = 0;
	virtual void add_adjacent_blocks_to_worklist (context<value_type, dept_value_type> * current_context, basic_block current_block) = 0;

	// Functions to be defined by client's analysis

	virtual value_type * boundary_value () = 0;
	virtual value_type * initial_value () = 0;
	void initialize_block_worklist (context<value_type, dept_value_type> * current_context);
	virtual bool analyze_block (context<value_type, dept_value_type> * current_context, basic_block current_block) = 0;

	// Functions to be defined by data flow value classes

	// virtual void increment_reference_count ();
	// virtual void decrement_reference_count ();
	// virtual bool is_value_same (value_type & v);
	// virtual value_type * copy_value (bool is_loop_merge);
	// virtual void copy_value (value_type & v, bool is_loop_merge);
	// virtual void clean ();
public:

	virtual bool process_assignment_statement (value_type & value, context<value_type, dept_value_type> * current_context, basic_block current_block, unsigned int assignment_data_index, bool to_kill = true) = 0;
	virtual set<struct cgraph_node *> get_called_functions (context<value_type, dept_value_type> & src_context, basic_block call_site, tree function_pointer) = 0;
	set<struct cgraph_node *> get_called_functions (context<value_type, dept_value_type> & src_context, basic_block call_site);			
	bool get_is_value_context ();
	template <class dest_value_type, class dest_dept_value_type> void get_dept_context (context<value_type, dept_value_type> * src_context, context<dest_dept_value_type, dest_value_type> ** dept_context);
	context<dept_value_type, value_type> * get_dependent_context (context<value_type, dept_value_type> * curr_context);
	context<dept_value_type, value_type> * get_dest_of_dept_context (context<value_type, dept_value_type> * src_context, basic_block call_site, struct cgraph_node * dest_function);
	context<value_type, dept_value_type> * get_function_context (struct cgraph_node * function);
	context<dept_value_type, value_type> * get_function_dependent_context (struct cgraph_node * function);
	context_enums<value_type, dept_value_type> get_context_enums (unsigned int function_uid);
	unsigned int get_context_enums_size (unsigned int function_uid);
	bool is_context_in_worklist (context<value_type, dept_value_type> * new_context);
	void add_context_to_worklist (context<value_type, dept_value_type> * new_context);
	bool is_recursively_called (struct cgraph_node * function, context<value_type, dept_value_type> & current_context, set<context_index> & visited_contexts);
	bool is_reachable_context_unprocessed (context<value_type, dept_value_type> & curr_context, set<context_index> & reachable_contexts);
	void set_function_contexts_map (function_index fid, context_index cid, context<value_type, dept_value_type> & c);
	void set_program_context (context_index cid, context<value_type, dept_value_type> & c);
	void set_dependent_analysis (inter_procedural_analysis<dept_value_type, value_type> * dept_analysis);
	void get_source_contexts (context<value_type, dept_value_type> & con, set<context<value_type, dept_value_type> *> & source_contexts);
	void get_destination_contexts (context<value_type, dept_value_type> & con, map<pair<block_index, function_index>, context<value_type, dept_value_type> *> & destination_contexts);
	inter_procedural_analysis<dept_value_type, value_type> * get_dependent_analysis ();
	void add_dependent_context_to_worklist (context<value_type, dept_value_type> * current_context, basic_block current_block);
	virtual void delete_local_variables (struct cgraph_node * src_function, struct cgraph_node * dest_function, value_type & out_value, void * info) = 0;
	void check_and_delete_local_variables (context<value_type, dept_value_type> & src_context, struct cgraph_node * called_function, value_type & value, void * info);
	void check_and_delete_local_variables (struct cgraph_node * src_function, struct cgraph_node * called_function, value_type & value, void * info);
	virtual void free_context_analysis_values (context<value_type, dept_value_type> & curr_context);
	void free_context_values (context<value_type, dept_value_type> & curr_context);
	void free_context_values ();
	inter_procedural_analysis ();
	~inter_procedural_analysis ();
	void delete_contexts ();
	void analyze_program ();
	value_type * get_analyzed_value (struct cgraph_node * start_function);
	void create_start_context (struct cgraph_node * start_function, value_type * start_value);
	void create_all_contexts ();
	void analyze_context_worklist ();
	void set_blocks_order ();
	map<context_index, int> get_call_chain_lengths (int inf);
	void get_call_chain_lengths (set<context<value_type, dept_value_type> *> & contexts, map<context_index, int> & call_chain_len, int inf);
	virtual void set_block_order (basic_block block, int rev_post_order) = 0;
	bool is_one_context_per_function ();

	template <class dest_value_type, class dest_dept_value_type> void meet_over_valid_paths (inter_procedural_analysis<dest_value_type, dest_dept_value_type> & dest_analysis);
	template <class dest_value_type, class dest_dept_value_type> void create_unique_function_contexts (map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts);
	template <class dest_value_type, class dest_dept_value_type> void save_unique_function_contexts (map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts);

	void accumulate_contexts (bool caller_to_callee);
	context<value_type, dept_value_type> * get_context_from_info_worklist ();
	void add_dest_contexts_to_worklist (context<value_type, dept_value_type> & curr_context);
	virtual bool caller_to_callee_info (context<value_type, dept_value_type> & con);
	virtual void copy_context_value (void * src_con, void * dest_con);
	virtual bool callee_to_caller_info (context<value_type, dept_value_type> & con);
	virtual void store_context_info (context<value_type, dept_value_type> & con);
	void store_contexts_info ();

	void delete_context_aux_info ();
	virtual void delete_aux_info (void * aux_info);
	virtual void print_aux_info (void * aux_info);

	void find_recursive_functions (set<function_index> & recursive_fns);

	void print_program_contexts ();
	void print_statistics ();
	void print_bypassing_statistics ();
	void print_functions_blocks ();
};

#endif

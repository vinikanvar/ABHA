
/************************
 * @author Vini Kanvar
************************/

/* Liveness analysis of [KMR12] using simple (i.e. without UNDEF/JUNK)
 * points-to graphs */

#include "../common.hh"

#ifndef LIVENESS_ANALYSIS_SIMPLE
#define LIVENESS_ANALYSIS_SIMPLE

#include "../misc/debug.hh"
#include "../misc/block_information.hh"
#include "../misc/parser.hh"
#include "../ipa/context.hh"
#include "../ipa/backward_inter_procedural_analysis.hh"
#include "../dfv/side_effects.hh"

#define OPEN_FST_FILE "/home/vini/Work/Education/GCC/Installations/new-hra/out_graph"

#define K_LIMIT 3

class liveness_analysis_simple : public backward_inter_procedural_analysis<variables, PT_VALUE_TYPE>
{
public:
	using inter_procedural_analysis<variables, PT_VALUE_TYPE>::get_called_functions;
	using inter_procedural_analysis<variables, PT_VALUE_TYPE>::delete_context_aux_info;

private:

	set<struct cgraph_node *> get_called_functions (context<variables, PT_VALUE_TYPE> & src_context, basic_block call_site, tree function_pointer);
	void process_return_value (context<variables, PT_VALUE_TYPE> * src_context, basic_block call_site, variables * value, struct cgraph_node * called_function, bool to_kill);

	void process_function_arguments (context<variables, PT_VALUE_TYPE> * src_context, basic_block call_site, variables * value, struct cgraph_node * called_function);
	variables * initial_value ();
	variables * boundary_value ();
	void process_call_statement (context<variables, PT_VALUE_TYPE> * src_context, basic_block call_site);
	void initialize_in_value (context<variables, PT_VALUE_TYPE> * src_context, basic_block call_site);

	bool process_parsed_data (context<variables, PT_VALUE_TYPE> * current_context, basic_block current_block, variables * calling_value, bool to_kill = true);
	void over_approximate_call_statement (variables & value, context<variables, PT_VALUE_TYPE> & src_context, basic_block call_site);
	bool process_assignment_statement (variables & value, context<variables, PT_VALUE_TYPE> * current_context, basic_block current_block, unsigned int assignment_data_index, bool to_kill = true);
	bool process_use_statement (variables & value, context<variables, PT_VALUE_TYPE> * current_context, basic_block current_block, unsigned int variable_index);

public:
	
	liveness_analysis_simple (bool is_val_context);
	~liveness_analysis_simple ();
	void delete_aux_info (void * aux_info);
	void insert_parameters (struct cgraph_node * src_function, variables & params);
	void insert_global_pointers (variables & globals);
	variables * extract_arg_ret_glob_reachable_value (struct cgraph_node * src_function, basic_block call_site, struct cgraph_node * called_function, variables & value_out);

	void delete_local_variables (struct cgraph_node * src_function, struct cgraph_node * dest_function, variables & value, void * info);
	void collect_function_par_defs ();
	void store_context_info (context<variables, unlabeled_edges> & current_context);

	void print_value (variables & vars);
	void print_analysis_statistics (map<function_index, context_enums<variables, PT_VALUE_TYPE> > & function_contexts);
	void preprocess_and_parse_program ();
};

#endif


/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef VARIABLES
#define VARIABLES

#include "../misc/debug.hh"
#include "../misc/parser.hh"

//typedef HOST_WIDE_INT variable_id;
typedef unsigned int variable_id;
typedef unsigned int label;

class variables
{
	// Count of the number of program points which reference to this data
	// flow value.
	unsigned int reference_count;

	// Important block of caller are not passed to callee because
	// otherwise more than one context per function will get created.
	// Let IBin and IBout be data flow values. IBin=(IBout AND kill) OR
	// gen. IBout= OR IBin. Initialization = false.
	// See dfv/side_effects
	bool important_block;

	// See dfv/side_effects
	set<variable_id> callees_global_defs;
	set<variable_id> callees_global_uses;
	set<variable_id> function_param_defs;

public:

	// Variables that will be explicitly used in indirect/direct callees
	// and will be used by caller. (for killing dead variables)
	set<variable_id> live_vars;

	variables ();
	~variables ();

	void increment_reference_count ();
	void decrement_reference_count ();

	set<variable_id> get_live_vars ();
	set<variable_id> get_callees_global_defs ();
	set<variable_id> get_callees_global_uses ();
	set<variable_id> get_function_param_defs ();
	void clean ();
	bool is_empty ();
	bool is_element (variable_id v);
	bool is_element (variable_id v, label offset);
	void insert_addr_taken_globals ();
	void insert_addr_taken_locals (struct cgraph_node * cnode);
	void insert_addr_taken_params (struct cgraph_node * cnode);
	void insert_live_var (variable_id v);
	void insert_selective_live_var (variable_id v);
	void insert_selective_function_param_def (variable_id v);
	void insert_selective_callees_global_def (variable_id v);
	void insert_selective_callees_global_use (variable_id v);
	void insert_addr_taken_locals (variable_id v, label offset, struct cgraph_node * cnode);
	void insert_live_vars (set<variable_id> & vars);
	void insert_live_vars (variables & gen_vars);
	void delete_live_var (variable_id v);
	void erase_function_param_defs ();
	void delete_callees_global_def (variable_id v);
	void delete_callees_global_use (variable_id v);
	void delete_live_vars (variables & del_vars);
	void delete_live_vars (set<variable_id> & del_vars);
	bool is_important_block ();
	void gen_important_block ();
	void kill_important_block ();
	void transfer_important_block (variables & dest_value);

	bool is_live (label var);
	void clear_live_vars ();

	void extract_arg_ret_glob_reachable_live_vars (variables & arg_ret_glob_reachable_value, struct cgraph_node * called_function);
	set<variable_id> get_dead_variables (set<variable_id> local_live_vars);
	variables * copy_value (bool is_loop_merge);
        void copy_value (variables & vars, bool is_loop_merge);
	bool is_value_same (variables & vars);
	void print_value (const char * file);
};

#endif

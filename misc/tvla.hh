
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef TVLA 
#define TVLA 

#include "../misc/debug.hh"
#include "../misc/parser.hh"
#include "../misc/block_information.hh"

class tvla
{
	set<string> program_pvar;
	set<string> program_dsel;
	set<string> program_args;
	set<string> program_params;
	set<string> program_recs;

public:
	void replace_char (string & s);
	void collect_tvp_pvars ();
	void insert_tvp_pvars (list<csvarinfo_t> & src, set<string> & dest);
	void insert_tvp_pvar (csvarinfo_t src, set<string> & dest);
	void print_tvp_file ();
	void print_tvp_assignments ();
	void print_tvp_pvar ();
	void print_tvp_pvar (csvarinfo_t var);
	void print_tvp_list (list<csvarinfo_t> & vars);
	void print_tvp_set (set<string> & vars);
	void print_tvp_dsel (unsigned int offset);
	void print_tvp_empty ();
	void print_tvp_malloc (constraint_expr lhs);
	void print_tvp_copy_var (constraint_expr lhs, constraint_expr rhs);
	void print_tvp_get_sel (constraint_expr lhs, constraint_expr rhs);
	void print_tvp_set_sel (constraint_expr lhs, constraint_expr rhs);
	void print_tvp_ff (constraint_expr lhs, constraint_expr rhs);
	void print_tvp_ff (int index);
	void print_tvp_block_ff (cgraph_node * cnode, basic_block current_block);
	void print_tvp_block_start (cgraph_node * cnode, basic_block current_block);
	void print_tvp_block_end (cgraph_node * cnode, basic_block current_block);
	void print_tvp_call (cgraph_node * calling_function, basic_block call_site);
	void print_tvp_function_start (cgraph_node * cnode);
	void print_tvp_params_args (cgraph_node * calling_function, basic_block call_site, cgraph_node * called_function, list<csvarinfo_t> & params, list<csvarinfo_t> & args);
	void print_tvp_rec (cgraph_node * calling_function, basic_block call_site, cgraph_node * called_function, list<csvarinfo_t> & params, list<csvarinfo_t> & args, list<csvarinfo_t> & rec, list<csvarinfo_t> & ret);
	void print_tvp_rec_ret (cgraph_node * calling_function, basic_block call_site, cgraph_node * called_function, list<csvarinfo_t> & params, list<csvarinfo_t> & args, list<csvarinfo_t> & rec, list<csvarinfo_t> & ret);
	void print_tvp_merge_rec (cgraph_node * calling_function, basic_block call_site, cgraph_node * called_function, list<csvarinfo_t> & params, list<csvarinfo_t> & args, list<csvarinfo_t> & rec, list<csvarinfo_t> & ret);
	void get_tvp_pairs (basic_block call_site, list<csvarinfo_t> & lhs, list<csvarinfo_t> & rhs);
	
};

extern tvla tvla_io;

#endif

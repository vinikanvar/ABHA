
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

#ifndef VALUE_CONTEXT
#define VALUE_CONTEXT

#include "../misc/block_information.hh"
#include "../dfv/variables.hh"
#include "../dfv/deterministic_graph.hh"
#include "../dfv/non_deterministic_graph.hh"
#include "../dfv/pt_node_set.hh"
#include "../dfv/unlabeled_edges.hh"
#include "../dfv/side_effects.hh"

// Each basic block will be given a number unique in the function
typedef unsigned int block_index;		
typedef unsigned int function_index;
typedef unsigned int context_index;

template <class value_type, class dept_value_type>
class context;

// Works with -std=c++0x
template <class value_type, class dept_value_type>
using context_enums = map<context_index, context<value_type, dept_value_type> *>;

// FIXME: This ordering using ORDER field of block increased the time on
// benchmarks. Try without any ordering. Or change GET_BLOCK_FROM_WORKLIST()
// which would return a block if reverse_post_order[i] is in worklist. The best
// solution is to maintain a list of block-worklist; check that the block has
// not already been inserted in the worklist using find() method in
// algorithm.h.
// OR maintain the following vectors:
// (a) reverse_post_order i.e. key is order
// (b) inverse of reverse_post_order i.e. key is basic block id
// (c) bit vector where key is order and value denotes whether or not the basic
// block is in worklist. Then pick the basic block with earliest index. 

struct basic_block_order
{
	// The ORDER field of block is set by FORWARD_INTER_PROCEDURAL_ANALYSIS
	// or BACKWARD_INTER_PROCEDURAL_ANALYSIS to reverse-post order or post
	// order, respectively.
	bool operator()(basic_block n, basic_block m)
	{
		// If n < m return true in FORWARD analysis
		// If n > m return true in BACKWARD analysis
		// if (n->index < m->index)
		int n_order = ((block_information *)(n->aux))->get_block_order ();
		int m_order = ((block_information *)(m->aux))->get_block_order ();
		if (n_order < m_order)
			return true;
		return false;
	}
};

// Enumeration based Functional Approach

template <class value_type, class dept_value_type>
class context
{
	// Index to uniquely identify a value context in a whole program analysis.
	context_index context_id;

	// Function in which this context exists
	struct cgraph_node * function;

	// CALL STRINGS APPROACH
	// Set of contexts, which call this value context.
	// Note that these edges are not deterministic: (a) the same context 
	// can call THIS context through multiple call-sites; (b) the same pair 
	// (function, call-site) can call THIS context through multple source 
	// context.
	// This is required to add the adjacent blocks (i.e. source context)
	// in the worklist.
	set<pair<context_index, block_index> > source_contexts;

	// Each context has outgoing edges, which are deterministic 
	// on the pair (call-site, destination/called function). 
	// This is required to determine the DEPENDENT_CONTEXT. 
	map<pair<block_index, function_index>, context<value_type, dept_value_type> *> destination_contexts;

	// Contexts on which this context is dependent on. This is used
	// in dependent analysis, like liveness analysis, which is dependent
	// on another analysis, like alias analysis.
	context<dept_value_type, value_type> * dependent_context;

	// In and out data flow values of each basic_block
	map<block_index, value_type *> blocks_in_value;
	map<block_index, value_type *> blocks_out_value;

	// Intra-procedural worklist of basic_blocks. The worklist is ordered
	// by the reverse-post-order (in a forward analysis) or post-order (in
	// a backward analysis) of the control flow graph.
	vector<basic_block> block_worklist;

	// Pointer to the data flow value at in of start basic_block
	// value_type * start_value;
	basic_block start_block;
	
	// Pointer to the data flow value at out of end basic_block
	// value_type * end_value;
	basic_block end_block;

	// True if data flow value of the end node has been computed.
	bool is_summary_created;

	// Any auxiliary information can be saved here.
	void * aux_info;

private:
	void build_block_worklist ();
	void print_block_stmts (basic_block block);

public:

	context (struct cgraph_node * fn, basic_block start_bb, basic_block end_bb, context * source_context, basic_block call_site, context<dept_value_type, value_type> * dept_context);
	~context ();

	static unsigned int number_of_contexts;

	bool add_block_to_worklist (basic_block block);
	void add_source_context (context<value_type, dept_value_type> * source_context, basic_block call_site);
	void add_destination_context (basic_block call_site, context<value_type, dept_value_type> * destination_context);
	void erase_source_context (context<value_type, dept_value_type> *, block_index bid);
	map<block_index, value_type *> get_blocks_in_value ();
	map<block_index, value_type *> get_blocks_out_value ();
	set<pair<context_index, block_index> > get_source_contexts ();
	map<pair<block_index, function_index>, context<value_type, dept_value_type> *> get_destination_contexts ();
	context<value_type, dept_value_type> * get_destination_context (basic_block call_site, struct cgraph_node * cnode);
	context<value_type, dept_value_type> * get_reusable_dest_context (basic_block call_site, struct cgraph_node * dest_function);
	context<dept_value_type, value_type> * get_dependent_context ();
	basic_block get_block_from_worklist ();
	int get_max_call_chain_len (map<context_index, int> & call_chain_len, int inf);
	void get_destination_contexts (set<context<value_type, dept_value_type> *> & dest_contexts);

	bool is_caller_context (context_index called_context, set<pair<context_index, block_index> > & caller_contexts, set<context_index> & visited_contexts);
	bool is_source_context_empty (function_index main_id);
	basic_block get_first_block_from_worklist ();
	basic_block get_first_intra_block_from_worklist ();
	bool is_context_partially_processed ();
	bool is_block_worklist_empty ();
	bool is_block_in_worklist (basic_block block);
	unsigned int get_context_id ();
	value_type * get_in_value (basic_block block);
	value_type * get_out_value (basic_block block);
	void set_in_value (basic_block block, value_type * value);
	void set_out_value (basic_block block, value_type * value);
	void copy_in_value (block_index bid, value_type * value);
	void copy_out_value (block_index bid, value_type * value);
	void set_source_contexts (context_index src_cid, block_index src_bid);
	void set_destination_contexts (pair<block_index, function_index> & p, context<value_type, dept_value_type> & dest_context);
	bool is_start_value_same (value_type & value);
	bool is_end_value_same (value_type & value);
	bool is_dept_context_same (context<dept_value_type, value_type> * dept_context);
	basic_block get_start_block ();
	basic_block get_end_block ();
	struct cgraph_node * get_function ();
	basic_block get_basic_block (struct cgraph_node * cnode, block_index bid);

	template <class dest_value_type, class dest_dept_value_type> void copy_context (context_enums<value_type, dept_value_type> & orig_program_contexts, map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts);
	template <class dest_value_type, class dest_dept_value_type> void copy_source_contexts (context<dest_value_type, dest_dept_value_type> & uc, context_enums<value_type, dept_value_type> & orig_program_contexts, map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts);
	template <class dest_value_type, class dest_dept_value_type> void copy_destination_contexts (context<dest_value_type, dest_dept_value_type> & uc, context_enums<value_type, dept_value_type> & orig_program_contexts, map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts);
	template <class dest_value_type, class dest_dept_value_type> context<dest_value_type, dest_dept_value_type> * get_unique_context (context_index orig_cid, context_enums<value_type, dept_value_type> & orig_program_contexts, map<function_index, context<dest_value_type, dest_dept_value_type> *> & unique_function_contexts);

	template <class dest_value_type, class dest_dept_value_type> void copy_blocks_in_value (context<dest_value_type, dest_dept_value_type> & unique_context);
	template <class dest_value_type, class dest_dept_value_type> void copy_blocks_out_value (context<dest_value_type, dest_dept_value_type> & unique_context);

	void * get_aux_info ();
	void * get_dest_aux_info (basic_block call_site, struct cgraph_node * dest_function);
	void set_aux_info (void * info);

	void find_recursive_functions (map<context_index, set<context_index> > & callers, set<function_index> & recursive_fns);
	bool add_callers (context_index new_caller, map<context_index, set<context_index> > & callers, set<function_index> & recursive_fns);

	void print_context ();
};

#endif

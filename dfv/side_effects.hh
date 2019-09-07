
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef SIDE_EFFECTS
#define SIDE_EFFECTS 

#include "../misc/debug.hh"
#include "../misc/parser.hh"

typedef unsigned int variable_id;
typedef unsigned int function_id;
typedef unsigned int block_index;		

class side_effects 
{
	bool is_unimp_blocks_ready;

	// A block is an important block and should be added to worklist only
	// if it is on a noreturn path (i.e. not ended by exit()), or otherwise
	// along the cfp to exit(), it contains a statement which may genrate
	// new points-to information.

	map<function_id, set<block_index> > unimportant_blocks;

	// Side effect analysis (for bypassing points-to info)
	// Global variables that will be explicitly defined and used in
	// indirect/direct callees. We perform def/use for only globals needed
	// for bypassing globals. For locals, we perform param reachability
	// based bypassing. This is over-approx only if the function does not
	// have a use of param.

	// upwards exposed uses
	map<function_id, set<variable_id> > callees_global_uses;

        // Since we do not perform strong updates on pta, the only edge
        // killing is due to def in the callee. So, pass only def edges.
        // Bypass global_uses. These hold true at all program points of the
        // callee.

        // Side effect analysis (for bypassing in next round -- e.g.
	// liveness_analysis_deterministic/non_deterministic). Since we do not
	// perform strong updates on live paths, we need to pass only def
	// rooted paths to the callee. We can bypass global_uses rooted paths.

	map<function_id, set<variable_id> > callees_global_defs;

        // Collect params that are directly defined in each function (not
        // considering the defs in the callees of the function). We need to
        // pass points-to edges rooted at these variables and
        // callees_global_defs flow-sensitively in the function because they
        // get killed; we can memoize the rest because the rest are only used
        // in the function --- they are never killed in weak updates.

        // We have considered params so that a param's pta that arrives is
        // passed into the function flow-senstively only if the param has a def
        // again in the function body (and not as par:=arg).

        // This is different from Hakajoo Oh in the sense that they pass
        // directly accessed vars, whereas we pass only directly def vars.

	map<function_id, set<variable_id> > function_param_defs;

        // Globals and locals of all functions that are possibly dereferenced
        // on the lhs, explitly or implicitly. This is used to decide whether
        // or not to bypass a live path to this context. This is not upwards
        // exposed; otherwise, we need to transfer lhs to rhs. eg.
        // x=y;x->f=.... Here x->f is def-deref but not upwards exposed.

        // These are the variables (local and global) which are dereferenced in
	// lhs of a statement and their rhs is non-null. The paths that contain
	// this dereferenced link should be passed to the callee and not
	// bypassed. This is necessary so that points-to analysis retains link
	// aliases of lhs and so that in the next round of liveness analysis
	// (liveness_analysis_deterministic/non_deterministic) that uses
	// points-to analysis, live link alias can be computed at each program
	// point.

        // This is collected so that link aliases that are dereferenced on
        // lhs are not bypassed by allocation_site_based_analysis. However,
        // h264ref generates too many contexts and does not terminate. Or
        // may be creation of in_edge_list on-the-fly is too inefficient
        // and we should create it whenever out_edge_list is updated.

        map<function_id, set<variable_id> > callees_lhs_derefs;

public:

	side_effects ();
	bool get_is_unimp_blocks_ready ();
	void set_is_unimp_blocks_ready ();

	set<variable_id> * get_callees_global_defs (struct cgraph_node * func);
	set<variable_id> * get_callees_global_uses (struct cgraph_node * func);
	set<variable_id> * get_callees_lhs_derefs (struct cgraph_node * func);
	set<variable_id> * get_function_param_defs (struct cgraph_node * func);

	bool is_block_unimportant (struct cgraph_node * func, block_index bid);
	void add_unimportant_blocks (struct cgraph_node * func, set<block_index> & blocks);
	void add_callees_lhs_derefs (struct cgraph_node * func, set<variable_id> & vars);
	void add_callees_global_defs (struct cgraph_node * func, set<variable_id> & vars);
	void add_callees_global_uses (struct cgraph_node * func, set<variable_id> & vars);
	void add_function_param_defs (struct cgraph_node * func, set<variable_id> & vars);

	void print_side_effects ();
};

extern side_effects function_side_effects;

#endif

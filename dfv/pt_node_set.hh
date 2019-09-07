
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef PT_NODE_SET
#define PT_NODE_SET

#include "../misc/debug.hh"
#include "../dfv/pt_fi_graph.hh"

typedef unsigned int pt_node_index;

class pt_node_set
{
public:
	set<pt_node_index> pt_nodes;

        // Count of the number of program points which reference to this data
        // flow value.
        unsigned int reference_count;

public:

	pt_node_set ();
	~pt_node_set ();

	void increment_reference_count ();
	void decrement_reference_count ();
	bool is_element (pt_node_index pt_nid);
	bool is_value_same (pt_node_set & ptn);
	pt_node_set * copy_value (bool is_loop_merge);
        void copy_value (pt_node_set & g, bool is_loop_merge);
	void gen (pt_node_index pnid);
	void gen (set<pt_node_index> & ngen);
	void kill (set<pt_node_index> & nkill);
	void clean ();
	void get_graph_statistics (unsigned int & max_num_nodes, float & max_avg_out_edges, set<pt_node_index> & program_pointers, map<label, set<label> > & program_root_aliases, set<set<list<int> > > & program_aliases, map<label, set<label> > & program_reachable_roots, bool print);
	void print_value (FILE * file);
};

#endif

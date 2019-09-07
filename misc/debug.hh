
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef DEBUG_HEADER
#define DEBUG_HEADER

#define FUNCTION_NAME() {\
	fprintf (dump_file, "\nFunction %s\n=======================================\n", __FUNCTION__); \
	fflush (dump_file); \
}

// Added by Suryansh Kumar
class statistics
{
public:
	double time;
	unsigned int calls;
	statistics ();
	void print ();
	bool first_call();
};

extern class statistics get_arg_glob_connected_nodes_stats;
extern class statistics extract_arg_glob_connected_graph_stats;
extern class statistics clean_useless_nodes_stats;
extern class statistics clean_disconnected_nodes_stats;
extern class statistics delete_local_variables_stats;
extern class statistics get_reachable_nodes_stats;
extern class statistics get_dead_graph_variables_stats;
extern class statistics delete_dead_pointers_stats;
extern class statistics process_assignment_statement_stats;
extern class statistics initialize_block_worklist_stats;
extern class statistics merge_graph_stats;
extern class statistics clean_unreachable_nodes_stats;
extern class statistics clean_stats;
extern class statistics copy_value_stats;
extern class statistics is_value_same_stats;
extern class statistics print_value_stats;
extern class statistics is_node_property_same_stats;
extern class statistics transfer_in_edges_stats;
extern class statistics transfer_out_edges_stats;
extern class statistics forward_get_same_dest_context_stats;
extern class statistics forward_process_call_statement_stats;
extern class statistics backward_get_same_dest_context_stats;
extern class statistics backward_process_call_statement_stats;
extern class statistics in_out_value_differ_stats;
extern class statistics delete_local_variables_stats;

void start_timer (struct timeval &start);
void stop_timer (struct timeval start, class statistics &stats);
void print_time_statistics ();

void merge_map (map<list<unsigned int>, set<list<unsigned int> > > & src, map<list<unsigned int>, set<list<unsigned int> > > & dest);
void merge_set (set<list<unsigned int> > & src, set<list<unsigned int> > & dest);
void merge_set (set<unsigned int> & src, set<unsigned int> & dest);

void count_map_size (const map<list<unsigned int>, set<list<unsigned int> > > & m, unsigned int & num_aliases, unsigned int & num_aps);
void count_map_size (const map<list<unsigned int>, list<list<unsigned int> > > & m, unsigned int & num_aliases, unsigned int & num_aps);

void print_memory_statistics ();

#endif

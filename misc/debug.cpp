
/************************
 * @author Vini Kanvar
************************/

#include "debug.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

statistics::
statistics ()
{
	time = 0.0;
	calls = 0;
}

void statistics::
print ()
{
	RESULT (" %f / %u\n", time, calls);
}

bool statistics::
first_call()
{
	if (calls == 0)
		return true;

	return false;
}

void start_timer(struct timeval &start)
{
	gettimeofday(&start,NULL);
} 

void stop_timer(struct timeval start, class statistics & stats)
{
	float t;
	struct timeval stop;
	gettimeofday (&stop, NULL);

	if (stats.first_call ())
	{	
		time_t ti = time(NULL);
		struct tm tm= *localtime(&ti);
			
		DEBUG ("\nFirst call of function : %d-%d-%d %d:%d:%d\n", 
			tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday, tm.tm_hour, tm.tm_min, tm.tm_sec);
	}
	t = (double) (stop.tv_usec - start.tv_usec) / 1000000 + (double) (stop.tv_sec - start.tv_sec);

	stats.time += t;
	stats.calls++;
}

void print_time_statistics ()
{	
	RESULT ("\n\n\n\t\t\t\t\tTime(s)\t Calls\n");

	RESULT ("merge_graph(): \t\t\t\t");
	merge_graph_stats.print ();

	RESULT ("clean_unreachable_nodes(): \t\t");
	clean_unreachable_nodes_stats.print();

	RESULT ("clean():\t\t\t\t");
	clean_stats.print();
	
	RESULT ("copy_value():\t\t\t\t");
	copy_value_stats.print();

	RESULT ("is_value_same():\t\t\t");
	is_value_same_stats.print();

	RESULT ("print_value():\t\t\t\t");
	print_value_stats.print();

	RESULT ("is_node_property_same():\t\t");
	is_node_property_same_stats.print();
	
	RESULT ("transfer_in_edges():\t\t\t");
	transfer_in_edges_stats.print();

	RESULT ("transfer_out_edges():\t\t\t");
	transfer_out_edges_stats.print();

	RESULT ("forward_get_same_dest_context():\t");
	forward_get_same_dest_context_stats.print();

	RESULT ("forward_process_call_statement():\t");
	forward_process_call_statement_stats.print();

	RESULT ("backward_get_same_dest_context():\t");
	backward_get_same_dest_context_stats.print();

	RESULT ("backward_process_call_statement():\t");
	backward_process_call_statement_stats.print();

	RESULT ("in_out_value_differ():\t\t\t");
	in_out_value_differ_stats.print();

	RESULT ("delete_local_variables():\t\t");
	delete_local_variables_stats.print();

	RESULT ("get_arg_glob_connected_nodes():\t\t");
        get_arg_glob_connected_nodes_stats.print();

	RESULT ("extract_arg_glob_connected_graph():\t");
	extract_arg_glob_connected_graph_stats.print();

	RESULT ("clean_useless_nodes():\t\t\t");
	clean_useless_nodes_stats.print();

	RESULT ("clean_disconnected_nodes():\t\t");
	clean_disconnected_nodes_stats.print();

	RESULT ("delete_local_variables():\t\t");
	delete_local_variables_stats.print();

	RESULT ("get_dead_graph_variables():\t\t");
	get_dead_graph_variables_stats.print();

	RESULT ("delete_dead_pointers():\t\t\t");
	delete_dead_pointers_stats.print();

	RESULT ("process_assignment_statement():\t\t");
	process_assignment_statement_stats.print();

	RESULT ("initialize_block_worklist():\t\t");
	initialize_block_worklist_stats.print();

	 RESULT ("\n\n\n");
        merge_graph_stats.print ();

        clean_unreachable_nodes_stats.print();

        clean_stats.print();

        copy_value_stats.print();

        is_value_same_stats.print();

        print_value_stats.print();

        is_node_property_same_stats.print();

        transfer_in_edges_stats.print();

        transfer_out_edges_stats.print();

        forward_get_same_dest_context_stats.print();

        forward_process_call_statement_stats.print();
	
        backward_get_same_dest_context_stats.print();

        backward_process_call_statement_stats.print();

        in_out_value_differ_stats.print();

        delete_local_variables_stats.print();

        get_arg_glob_connected_nodes_stats.print();

        extract_arg_glob_connected_graph_stats.print();

        clean_useless_nodes_stats.print();

        clean_disconnected_nodes_stats.print();

        delete_local_variables_stats.print();

        get_dead_graph_variables_stats.print();

        delete_dead_pointers_stats.print();
	
        process_assignment_statement_stats.print();

        initialize_block_worklist_stats.print();

}

void 
merge_map (map<list<unsigned int>, set<list<unsigned int> > > & src,
	map<list<unsigned int>, set<list<unsigned int> > > & dest)
{
	// If you try to insert a key/value pair into a map that already holds
	// that key, then the old value will be kept and the new one will be
	// discarded. For that reason, if you write
	// Amap2.insert(Amap1.begin(), Amap1.end());
	// In some circumstances you might not copy everything over as
	// intended, because duplicate keys won't copy.

	// The following has the same problem with duplicate keys.
	// copy (src.begin (), src.end (), inserter (dest, dest.end ()));

	// The definition below takes 356 seconds on ALLOC_BASED,L=1,hmmer.
	map<list<unsigned int>, set<list<unsigned int> > >::iterator si;
	for (si = src.begin (); si != src.end (); si++)
	{
		list<unsigned int> ap = si->first;
		set<list<unsigned int> > aps = si->second;
		dest[ap].insert (aps.begin (), aps.end ());
	}

#if 0
	// The definition below takes 373 seconds on ALLOC_BASED,L=1,hmmer.
	map<list<unsigned int>, set<list<unsigned int> > >::iterator destItr = dest.begin();
	map<list<unsigned int>, set<list<unsigned int> > >::iterator srcItr = src.begin();

	while (destItr != dest.end() && srcItr != src.end()) 
	{
		// If the src value is less than the dest value, then insert it
		// into the dest map and skip past it. 
		if (srcItr->first < destItr->first) 
		{
			dest.insert (destItr, *srcItr); // Use destItr as a hint.
			++srcItr;
		}
		// Otherwise, if the values are equal, add the src value
		// and move both iterators forward.
		else if (srcItr->first == destItr->first) 
		{
			// destItr->second = srcItr->second;
			set<list<unsigned int> > src_vals = srcItr->second;
			merge_set (src_vals, dest[destItr->first]);
			++destItr; ++srcItr;
		}
		// Otherwise the src value is bigger, so skip past the dest value.
		else
			++destItr;

	}

	// At this point we've exhausted one of the two ranges.  Add what's
	// left of the src values to the dest map, since we know there are no
	// duplicates there.
	dest.insert(srcItr, src.end());
#endif
}

void 
merge_set (set<list<unsigned int> > & src, 
	set<list<unsigned int> > & dest)
{
	dest.insert (src.begin (), src.end ());

//	set<list<unsigned int> >::iterator pos = dest.begin ();
//	set<list<unsigned int> >::iterator si;
//	for (si = src.begin (); si != src.end (); si++)
//		pos = dest.insert (pos, *si);
}

void 
merge_set (set<unsigned int> & src, 
	set<unsigned int> & dest)
{
	dest.insert (src.begin (), src.end ());

//	set<unsigned int>::iterator pos = dest.begin ();
//	set<unsigned int>::iterator si;
//	for (si = src.begin (); si != src.end (); si++)
//		pos = dest.insert (pos, *si);
}

void
count_map_size (const map<list<unsigned int>, set<list<unsigned int> > > & m,
	unsigned int & num_aliases,
	unsigned int & num_aps)
{
	map<list<unsigned int>, set<list<unsigned int> > >::const_iterator psi;
	for (psi = m.begin (); psi != m.end (); psi++)
	{
		num_aliases += psi->second.size () - 1;	// Removing psi->first because value includes key
		if (psi->second.size () - 1)
			num_aps++;
	}
}

void
count_map_size (const map<list<unsigned int>, list<list<unsigned int> > > & m,
	unsigned int & num_aliases,
	unsigned int & num_aps)
{
	map<list<unsigned int>, list<list<unsigned int> > >::const_iterator psi;
	for (psi = m.begin (); psi != m.end (); psi++)
	{
		num_aliases += psi->second.size ();		// Value does not include key
		if (psi->second.size ())
			num_aps++;
	}
}

void
print_memory_statistics ()
{
	struct sysinfo info;

	if (sysinfo(&info) != 0)
		RESULT ("Error: sysinfo: error reading system statistics");

	// RESULT ("\nUptime: %ld:%ld:%ld", info.uptime/3600, info.uptime%3600/60, info.uptime%60);
	RESULT ("\nTotal RAM: %ld MB", info.totalram/1024/1024);
	RESULT ("\nFree RAM: %ld B", (info.freeram));
	// RESULT ("\nFree RAM: %ld kB", (info.freeram)/1024);
	// RESULT ("\nFree RAM: %ld MB", (info.freeram)/1024/1024);
	// RESULT ("\nProcess count: %d", info.procs);
	// RESULT ("\nPage size: %ld bytes", sysconf(_SC_PAGESIZE));

	FILE * stat_file = fopen (STAT_FILE, "a");
	// fprintf (stat_file, "\nUptime: %ld:%ld:%ld", info.uptime/3600, info.uptime%3600/60, info.uptime%60);
	fprintf (stat_file, "\nTotal RAM: %ld MB", info.totalram/1024/1024);
	fprintf (stat_file, "\nFree RAM: %ld B", (info.freeram));
	// fprintf (stat_file, "\nFree RAM: %ld kB", (info.freeram)/1024);
	// fprintf (stat_file, "\nFree RAM: %ld MB", (info.freeram)/1024/1024);
	// fprintf (stat_file, "\nProcess count: %d", info.procs);
	// fprintf (stat_file, "\nPage size: %ld bytes", sysconf(_SC_PAGESIZE));
	fclose (stat_file);
}

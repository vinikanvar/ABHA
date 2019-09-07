
/************************
 * @author Vini Kanvar
************************/

#include "pt_node_set.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

pt_node_set::
pt_node_set ()
{
	reference_count = 0;
}

pt_node_set::
~pt_node_set ()
{
}


void pt_node_set::
increment_reference_count ()
{
	reference_count++;
}

void  pt_node_set::
decrement_reference_count ()
{
	if (!reference_count)
	{
		RESULT ("\nError: reference count of pt_node_set was already 0");
		return;
	}

	reference_count--;
	DEBUG ("\nCount = %d (after decr) of pt_node_set", reference_count);
	if (!reference_count)
	{
#if GC
		DEBUG ("\nGC pt_node_set");
		delete this;
#endif
	}
}

bool pt_node_set::
is_element (pt_node_index pt_nid)
{
	return pt_nodes.find (pt_nid) != pt_nodes.end ();
}

/**
 * This function checks if THIS pt_node_set is same as the parameter pt_node_set.
 */

bool pt_node_set:: 
is_value_same (pt_node_set & ptn)
{
	FUNBEGIN ();

	// If address of THIS and g is same, return true;
	if (this == &ptn)
	{
		DEBUG ("\nOptimum is_value_same()");
		RETURN (true);
		// return true;
	}

	// This is not an error. pt-node=n1 may be monotonically weaker than
	// pt-node=n2 if the set of access paths represented by n1 is a
	// superset of those of n2.
	if (pt_nodes.size () > ptn.pt_nodes.size ())
		DEBUG ("\nValue decreased");

	RETURN (pt_nodes == ptn.pt_nodes);
	// return (pt_nodes == ptn.pt_nodes);
}

/**
 * This function creates a copy of THIS pt_node_set.
 */

pt_node_set * pt_node_set::
copy_value (bool is_loop_merge)
{
	pt_node_set * copy_ptn = new pt_node_set ();
	copy_ptn->copy_value (*this, is_loop_merge);
	return copy_ptn;
}

/**
 * This function copies PTN to THIS pt_node_set.
 */

void pt_node_set::  
copy_value (pt_node_set & ptn, bool is_loop_merge)
{
	pt_nodes.insert (ptn.pt_nodes.begin (), ptn.pt_nodes.end ());
}

void pt_node_set::
gen (pt_node_index pnid)
{
	pt_nodes.insert (pnid);
}

void pt_node_set::
gen (set<pt_node_index> & ngen)
{
	// pt_nodes.insert (ngen.begin (), ngen.end ());
	merge_set (ngen, pt_nodes);
}

void pt_node_set::
kill (set<pt_node_index> & nkill)
{
	set<pt_node_index>::iterator ni;
	for (ni = nkill.begin (); ni != nkill.end (); ni++)
		pt_nodes.erase (*ni);
}

void pt_node_set::  
clean ()
{
}

void pt_node_set::
get_graph_statistics (unsigned int & max_num_nodes,
	float & max_avg_out_edges,
	set<pt_node_index> & program_pointers,
	map<label, set<label> > & program_root_aliases,
	set<set<list<int> > > & program_aliases,
	map<label, set<label> > & program_reachable_roots,
	bool print)
{
#if 0
	// Node-edge information
	get_nodes_edges (max_num_nodes, max_avg_out_edges, print);
#endif

	// Points-to pair information
	program_pointers.insert (pt_nodes.begin (), pt_nodes.end ());

#if 0
	// Alias information

	set<set<list<int> > > set_of_aliases;
	get_aliases (set_of_aliases, program_aliases);
	if (print)
	{
		DEBUG ("\nOur graph:");
		print_aliases (set_of_aliases);
	}
	// DEBUG ("\nOur compact graph:");
	// pt_node_set * compact_g = get_compact_graph ();
	// compact_g->print_aliases (set_of_aliases, program_aliases);

	// Root alias information

	map<label, set<label> > root_aliases;
	get_root_aliases (root_aliases, program_root_aliases);
	if (print)
		print_root_aliases (root_aliases);

	// Compaction may introduce spurious root_aliases information. For
	// example, if {x=&y;z=&y;} else {x=&y;w=&y;} our graph =
	// {(x,n1)(y,n2)(y,n3)(z,n4)(w,n5)(n1,*,n2),(n1,*.n3)(n4,*,n2)(n5,*,n3)}.
	// Here w and z are not reachable from each other. However, after
	// compaction, i.e. after merging n2 and n3 which have the same name y,
	// we spuriously get that w and z are reachable.

	// map<label, set<label> > compact_root_aliases;
	// compact_g->print_root_aliases (compact_root_aliases);

	// Reachability

	map<label, set<label> > reachable_roots;
	get_reachable_roots (reachable_roots, program_reachable_roots);
	if (print)
		print_reachable_roots (reachable_roots);
#endif
}

void pt_node_set::
print_value (FILE * file)
{
	DEBUG ("\npt_nodes=");
	set<pt_node_index>::iterator ni;
	for (ni = pt_nodes.begin (); ni != pt_nodes.end (); ni++)
	{
		RESULT ("%d,", *ni);
	}
}

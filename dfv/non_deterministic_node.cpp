
/************************
 * @author Vini Kanvar
************************/

#include "non_deterministic_node.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

// We assume that node index 0 does not exist
unsigned int non_deterministic_node::
number_of_nodes = 1;

non_deterministic_node::
non_deterministic_node (map<label_site_pair, non_deterministic_node *> & nodes)
{
	DEBUG ("\nnew non_deterministic_node ()");
	node_id = number_of_nodes;
	site_pair sp = make_pair (0,0);
	in_edge_label = 0;
	nodes[make_pair (in_edge_label, sp)] = this;
#if DEBUG_CONTAINER
	DEBUG ("\ndest=%d=l=%d,sp=", node_id, in_edge_label);
	non_deterministic_node::print_site_pair (sp);
#endif
	number_of_nodes++;
}

non_deterministic_node::
non_deterministic_node (site_pair & sp, label l,
	map<label_site_pair, non_deterministic_node *> & nodes)
{
	node_id = number_of_nodes;
	nodes[make_pair (l, sp)] = this;
	number_of_nodes++;

	alloc_desc_site_pair = sp;
	in_edge_label = l;

#if DEBUG_CONTAINER
	DEBUG ("\ndest=%d=l=%d,sp=", node_id, in_edge_label);
	non_deterministic_node::print_site_pair (sp);
#endif
}

non_deterministic_node::
~non_deterministic_node ()
{
	DEBUG ("\nDelete this node=%x (id=%d)", this, node_id);
}

/**
 * This function creates a copy of THIS node to a new node or an already
 * existing empty node in DEST_GRAPH_NODES.
 */

non_deterministic_node * non_deterministic_node::
new_copy_node (map<label_site_pair, non_deterministic_node *> & dest_graph_nodes)
{
	non_deterministic_node * g_n = NULL;
	label_site_pair ls = get_label_site_pair ();
	if (dest_graph_nodes.find (ls) != dest_graph_nodes.end ())
	{
		g_n = dest_graph_nodes[ls];
		if (g_n->get_in_edge_label () != in_edge_label)
		{
			RESULT ("\nError: in-edge f=%d of src=%d /= f=%d of dest=%d",
				in_edge_label, node_id, g_n->get_in_edge_label (), g_n->get_node_id ()); 
		}
		if (g_n->is_out_edge ())
		{
			RESULT ("\nError: new_copy_node() is meant for empty nodes. Node=%d not empty", 
				g_n->node_id);
		}
	}
	else
		g_n = new non_deterministic_node (alloc_desc_site_pair, in_edge_label, dest_graph_nodes);

	g_n->in_nodes.insert (in_nodes.begin (), in_nodes.end ());

	map<label, set<label_site_pair> >::iterator outei;
	for (outei = out_edge_list.begin (); outei != out_edge_list.end (); outei++)
	{
		label l = outei->first;
		set<label_site_pair> lsp = outei->second;
		g_n->out_edge_list[l].insert (lsp.begin (), lsp.end ());
	}
	return g_n;
}

node_index non_deterministic_node::
get_node_id ()
{
	return node_id;
}

site_pair non_deterministic_node::
get_alloc_desc_site_pair ()
{
	return alloc_desc_site_pair;
}

set<label_site_pair> non_deterministic_node::
get_in_nodes ()
{
	return in_nodes;
}

label non_deterministic_node::
get_in_edge_label ()
{
	return in_edge_label;
}

label_site_pair non_deterministic_node::
get_label_site_pair ()
{
	return make_pair (in_edge_label, alloc_desc_site_pair);
}

map<label, set<label_site_pair> > non_deterministic_node::
get_out_edge_list ()
{
	return out_edge_list;
}

map<label, set<label_site_pair> > * non_deterministic_node::
get_out_edge_list_pointer ()
{
	return &out_edge_list;
}

void non_deterministic_node::
get_out_nodes (set<label_site_pair> & out_nodes)
{
	map<label, set<label_site_pair> >::iterator outei;
	for (outei = out_edge_list.begin (); outei != out_edge_list.end (); outei++)
	{
		set<label_site_pair> outls = outei->second;
		out_nodes.insert (outls.begin (), outls.end ());
	}
}

void non_deterministic_node::
get_out_edge_labels (set<label> & out_edge_labels)
{
	map<label, set<label_site_pair> >::iterator outei;
	for (outei = out_edge_list.begin (); outei != out_edge_list.end (); outei++)
	{
		label l = outei->first;
		out_edge_labels.insert (l);
	}
}

/**
 * This function returns the label_site of the destination node of THIS
 * node via L. It returns empty label_site if a destination node via L
 * does not exist.
 */

set<label_site_pair> non_deterministic_node::
get_destination_nodes (label l)
{
	set<label_site_pair> lsp;

        if (out_edge_list.find (l) == out_edge_list.end ())
        {
                DEBUG ("=NULL");
                return lsp;
        }

        DEBUG ("=not-NULL");
        lsp = out_edge_list[l];

	return lsp;
}

bool non_deterministic_node::
is_in_nodes ()
{
	return !in_nodes.empty ();
}

bool non_deterministic_node::
is_in_node (label_site_pair lsp)
{
	return (in_nodes.find (lsp) != in_nodes.end ());
}

bool non_deterministic_node::
is_alloc_site (site s)
{
	return (alloc_desc_site_pair.first == s);
}

bool non_deterministic_node::
is_desc_site (site s)
{
	return (alloc_desc_site_pair.second == s);
}

bool non_deterministic_node::
is_out_edge (label l, site_pair & sp)
{
	if (out_edge_list.find (l) == out_edge_list.end ())
		return false;
	set<label_site_pair> out_lsps = out_edge_list[l];
	if (out_lsps.find (make_pair (l, sp)) != out_lsps.end ())
		return true;
	return false;
}

bool non_deterministic_node::
is_out_edge ()
{
	return out_edge_list.size ();
}

bool non_deterministic_node::
is_stack_node ()
{
	return (!in_edge_label && alloc_desc_site_pair == make_pair (0,0));
}

bool non_deterministic_node::
is_node_same (non_deterministic_node & g_n)
{
	if (in_edge_label != g_n.in_edge_label)
		return false;

	if (alloc_desc_site_pair != g_n.alloc_desc_site_pair)
		return false;

	if (in_nodes != g_n.in_nodes)
		return false;

	if (out_edge_list.size () != g_n.out_edge_list.size ())
		return false;

	map<label, set<label_site_pair> >::iterator outei;
	for (outei = out_edge_list.begin (); outei != out_edge_list.end (); outei++)
	{
		label l = outei->first;
		set<label_site_pair> out_lsps = outei->second;
		set<label_site_pair>::iterator out_lspsi;
		for (out_lspsi = out_lsps.begin (); out_lspsi != out_lsps.end (); out_lspsi++)
		{
			label_site_pair out_lsp = *out_lspsi;
			site_pair sp = out_lsp.second;
			if (!g_n.is_out_edge (l, sp))
				return false;
		}
	}

	return true;
}

void non_deterministic_node::
set_alloc_site (site s)
{
	alloc_desc_site_pair.first = s;
}

void non_deterministic_node::
set_desc_site (site s)
{
	alloc_desc_site_pair.second = s;
}

/**
 * This function inserts an edge from THIS node to DEST node via L. 
 */

void non_deterministic_node::
insert_edge (label l, non_deterministic_node & dest)
{
	DEBUG ("\ninsert_edge start: %d->f=%d->%d", node_id, l, dest.node_id);

	label_site_pair this_ls = get_label_site_pair ();
	label_site_pair dest_ls = dest.get_label_site_pair ();
	out_edge_list[l].insert (dest_ls);
	dest.in_nodes.insert (this_ls);
#if DEBUG_CONTAINER
	if (is_stack_node ())
	{
		csvarinfo_t var = program.cs_get_varinfo (l);
		DEBUG ("\ninsert_edge: %d->%s(%d)->%d", node_id, var->name, l, dest.node_id);
	}
	else
		DEBUG ("\ninsert_edge: %d->%d->%d", node_id, l, dest.node_id);
#endif
}

/**
 * This function deletes edge from THIS node to DEST node via L. It does not
 * delete the DEST node even if it is unreachable. 
 */

void non_deterministic_node::
temp_delete_edge (label l, non_deterministic_node & dest)
{
	DEBUG ("\ndelete_edge (l=%d,dest=%d)", l, dest.node_id);
	// check that l == in_edge_label
	if (l != dest.in_edge_label)
	{
		// This is not an error
		DEBUG ("\ndelete_edge(): l=%d /= in_edge_label=%d of dest=%d", 
			l, dest.in_edge_label, dest.node_id);
		return;
	}

	if (out_edge_list.find (l) == out_edge_list.end ())
	{
		// This is not an error
		DEBUG ("\ndelete_edge(): THIS node=%d does not have an out-edge on l=%d", 
			node_id, l);
		return;
	}

	label_site_pair this_ls = get_label_site_pair ();
	DEBUG ("\nthis_ls=%d,%d,%d", this_ls.first, this_ls.second.first, this_ls.second.second);
	label_site_pair dest_ls = dest.get_label_site_pair ();
	DEBUG ("\ndest_ls=%d,%d,%d", dest_ls.first, dest_ls.second.first, dest_ls.second.second);
	out_edge_list[l].erase (dest_ls);
	if (out_edge_list[l].empty ())
		out_edge_list.erase (l);
	dest.in_nodes.erase (this_ls);
#if DEBUG_CONTAINER
	DEBUG ("\ndest.in_nodes=");
	set<label_site_pair>::iterator ii;
	for (ii = dest.in_nodes.begin (); ii != dest.in_nodes.end (); ii++)
	{
		label_site_pair lsp = *ii;
		DEBUG ("<%d,%d,%d>,", lsp.first, lsp.second.first, lsp.second.second);
	}
	
	if (is_stack_node ())
	{
		csvarinfo_t var = program.cs_get_varinfo (l);
		DEBUG ("\ndelete_edge: %d->%s(%d)->%d", node_id, var->name, l, dest.node_id);
	}
	else
		DEBUG ("\ndelete_edge: %d->%d->%d", node_id, l, dest.node_id);
#endif
	
}

void non_deterministic_node::
replace_in_nodes (label_site_pair & old_lsp, label_site_pair & new_lsp)
{
	in_nodes.erase (old_lsp);
	in_nodes.insert (new_lsp);
}

void non_deterministic_node::
get_node_stats (unsigned int & edge_count,	
	unsigned int & use_sites_count,
	set<site> & unique_use_sites)
{
	map<label, set<label_site_pair> >::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		set<label_site_pair> * out_nodes = &(ei->second);
		edge_count += out_nodes->size ();
	}
}

bool non_deterministic_node::
is_node_okay (non_deterministic_node & stack)
{
	bool okay = true;
	if (alloc_desc_site_pair.first == DISCONNECTED_LINK || alloc_desc_site_pair.second == DISCONNECTED_LINK)
	{
		RESULT ("\nError: Graph still has DISCONNECTED_LINK on node=%d", node_id);
		okay = false;
	}
	if (alloc_desc_site_pair.first && alloc_desc_site_pair.second)
	{
		RESULT ("\nError: both alloc-site=%d and use-site=%d are non-zero",
			alloc_desc_site_pair.first, alloc_desc_site_pair.second);
		okay = false;
	}
	// Check that if stack is the in-node, then it is the only in-node
	if (is_in_node (stack.get_label_site_pair ()))
	{
		if (in_nodes.size () > 1)
		{
			RESULT ("\nError: node=%n from stack has more than one in-nodes", node_id);
			okay = false;
		}
		// Check that if in-edge from stack has desc_site = label in-edge 
		if (alloc_desc_site_pair.second)
		{
			if (in_edge_label != (alloc_desc_site_pair.second * ROOT_LINK))
			{
				RESULT ("\nError: desc_site=%d is not same as root label=%d",
					alloc_desc_site_pair.second, node_id);
				okay = false;
			}
		}
	}

	return okay;
}

bool non_deterministic_node::
is_out_node_okay (label out_edge_label, non_deterministic_node & out_n)
{
	bool okay = true;

	if (out_n.in_edge_label != out_edge_label)
	{
		RESULT ("\nError: out_edge_label=%d /= out_n.in_edge_label(id)=%d of out-node=%d", 
			out_edge_label, out_n.in_edge_label, out_n.node_id);
		okay = false;
	}

	// Check that out_n.in_nodes contains THIS node
	label_site_pair this_lsp = get_label_site_pair ();
	if (!out_n.is_in_node (this_lsp))
	{
		RESULT ("\nError: out_n=%d does not contain this node=%d as in_nodes",
			out_n.node_id, node_id);
		okay = false;
	}

	return okay;
}

bool non_deterministic_node::
is_in_node_okay (non_deterministic_node & in_n)
{
	bool okay = true;

	if (in_n.out_edge_list.find (in_edge_label) == in_n.out_edge_list.end ())
	{
		RESULT ("\nError: in_node=%d does not have in_edge_label=%d for this node=%d",
			in_n.node_id, in_edge_label, node_id);
		okay = false;
	}
	// Check that out-nodes of in-n contains THIS node
	set<label_site_pair> in_n_out_nodes = in_n.out_edge_list[in_edge_label];
	label_site_pair this_lsp = get_label_site_pair ();
	if (in_n_out_nodes.find (this_lsp) == in_n_out_nodes.end ())
	{
		RESULT ("\nError: out-nodes of in_node=%d does not contain this node=%d",
			in_n.node_id, node_id);
		okay = false;
	}

	return okay; 
}

void non_deterministic_node::
print_site_pair (site_pair & sp)
{
	RESULT ("<%d,%d>", sp.first, sp.second);
}

void non_deterministic_node::
print_in_edge_list (map<label_site_pair, non_deterministic_node *> & nodes)
{
	DEBUG ("\nIn-edge=f=%d,In-nodes=", in_edge_label);
	set<label_site_pair>::iterator lspi;
	for (lspi = in_nodes.begin (); lspi != in_nodes.end (); lspi++)
	{
		non_deterministic_node * n = nodes[*lspi];
		if (!n)
		{
			label_site_pair lsp = *lspi;
			RESULT ("\nError: node label=%d, alloc_site=%d, use_site=%d not found",
				lsp.first, lsp.second.first, lsp.second.second);
		}
		DEBUG ("%d,", n->node_id);
	}
	DEBUG ("\nDone in-edges");
}

void non_deterministic_node::
print_out_edge_list (map<label_site_pair, non_deterministic_node *> & nodes)
{
	DEBUG ("\nprint_out_edge_list()");
	map<label, set<label_site_pair> >::iterator outei;
	for (outei = out_edge_list.begin (); outei != out_edge_list.end (); outei++)
	{
		label l = outei->first;
		set<label_site_pair> out_lsps = outei->second;
		set<label_site_pair>::iterator outni;
		for (outni = out_lsps.begin (); outni != out_lsps.end (); outni++)
		{
			label_site_pair out_ls = *outni;
			non_deterministic_node * out_n = nodes[out_ls];
			if (is_stack_node ())
			{
				csvarinfo_t var = program.cs_get_varinfo (l);
				RESULT ("\n\t%d{", node_id);
				print_site_pair (alloc_desc_site_pair);
				if (var->is_global_var)
				{
					RESULT ("}-># %s(%d)->%d{", var->name, l, out_n->node_id);
				}
				else
				{
					RESULT ("}->%s(%d)->%d{", var->name, l, out_n->node_id);
				}
				print_site_pair (out_n->alloc_desc_site_pair);
				RESULT ("}");
			}
			else
			{
				RESULT ("\n\t%d{,", node_id);
				print_site_pair (alloc_desc_site_pair);
				RESULT ("}->%d->%d{", l, out_n->node_id);
				print_site_pair (out_n->alloc_desc_site_pair);
				RESULT ("}");
			}
		}
	}	
	DEBUG ("\nDone out-edges");
}

void non_deterministic_node::
print_node (map<label_site_pair, non_deterministic_node *> & nodes)
{
#if DEBUG_CONTAINER
	DEBUG ("\nNode=%d(", node_id);
	print_site_pair (alloc_desc_site_pair);
	DEBUG (")");
	print_in_edge_list (nodes);
#endif
	print_out_edge_list (nodes);
	DEBUG ("\nDone node");
}

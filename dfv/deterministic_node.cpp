
/************************
 * @author Vini Kanvar
************************/

#include "deterministic_node.hh"

#define DEBUG_CONTAINER 0
//#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
#define DEBUG(...)

// We assume that node index 0 does not exist
unsigned int deterministic_node::
number_of_nodes = 1;

deterministic_node::
deterministic_node (map<label_sites, deterministic_node *> & nodes)
{
	DEBUG ("\nnew deterministic_node ()");
	node_id = number_of_nodes;
	sites ss;
	in_edge_label = 0;
	nodes[make_pair (in_edge_label, ss)] = this;
#if DEBUG_CONTAINER
	DEBUG ("\ndest=%d=l=%d,ss=", node_id, in_edge_label);
	deterministic_node::print_sites (ss);
#endif
	number_of_nodes++;
}

deterministic_node::
deterministic_node (sites & ss, label l,
	map<label_sites, deterministic_node *> & nodes)
{
	node_id = number_of_nodes;
	nodes[make_pair (l, ss)] = this;
	number_of_nodes++;

	desc_sites = ss;
	in_edge_label = l;

#if DEBUG_CONTAINER
	DEBUG ("\ndest=%d=l=%d,ss=", node_id, in_edge_label);
	deterministic_node::print_sites (ss);
#endif
}

deterministic_node::
~deterministic_node ()
{
	DEBUG ("\nDelete this node=%x (id=%d)", this, node_id);
}

/**
 * This function creates a copy of THIS node to a new node or an already
 * existing empty node in DEST_GRAPH_NODES.
 */

deterministic_node * deterministic_node::
new_copy_node (map<label_sites, deterministic_node *> & dest_graph_nodes)
{
	deterministic_node * g_n = NULL;
	label_sites ls = get_label_sites ();
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
		g_n = new deterministic_node (desc_sites, in_edge_label, dest_graph_nodes);

	g_n->in_nodes.insert (in_nodes.begin (), in_nodes.end ());

	map<label, label_sites>::iterator outei;
	for (outei = out_edge_list.begin (); outei != out_edge_list.end (); outei++)
	{
		label l = outei->first;
		label_sites lss = outei->second;
		g_n->out_edge_list[l] = lss;
	}
	return g_n;
}

node_index deterministic_node::
get_node_id ()
{
	return node_id;
}

sites deterministic_node::
get_desc_sites ()
{
	return desc_sites;
}

set<label_sites> deterministic_node::
get_in_nodes ()
{
	return in_nodes;
}

label deterministic_node::
get_in_edge_label ()
{
	return in_edge_label;
}

label_sites deterministic_node::
get_label_sites ()
{
	return make_pair (in_edge_label, desc_sites);
}

map<label, label_sites> deterministic_node::
get_out_edge_list ()
{
	return out_edge_list;
}

map<label, label_sites> * deterministic_node::
get_out_edge_list_pointer ()
{
	return &out_edge_list;
}

void deterministic_node::
get_out_nodes (set<label_sites> & out_nodes)
{
	map<label, label_sites>::iterator outei;
	for (outei = out_edge_list.begin (); outei != out_edge_list.end (); outei++)
	{
		label_sites outls = outei->second;
		out_nodes.insert (outls);
	}
}

void deterministic_node::
get_out_edge_labels (set<label> & out_edge_labels)
{
	map<label, label_sites>::iterator outei;
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

label_sites deterministic_node::
get_destination_node (label l)
{
	label_sites lss;

        if (out_edge_list.find (l) == out_edge_list.end ())
        {
                DEBUG ("=NULL");
                return lss;
        }

        DEBUG ("=not-NULL");
        lss = out_edge_list[l];

#if DEBUG_CONTAINER
        DEBUG ("\ndest=l=%d,ss=", lss.first);
        deterministic_node::print_sites (lss.second);
#endif

	return lss;
}

bool deterministic_node::
is_in_nodes ()
{
	return !in_nodes.empty ();
}

bool deterministic_node::
is_in_node (label_sites & lss)
{
	return (in_nodes.find (lss) != in_nodes.end ());
}

bool deterministic_node::
is_desc_site (site s)
{
	return (desc_sites.find (s) != desc_sites.end ());
}

bool deterministic_node::
is_out_edge (label l, sites & ss)
{
	if (out_edge_list.find (l) == out_edge_list.end ())
		return false;
	sites this_ss = out_edge_list[l].second;
	if (ss != this_ss)
		return false;
	return true;
}

bool deterministic_node::
is_out_edge ()
{
	return out_edge_list.size ();
}

bool deterministic_node::
is_stack_node ()
{
	return (!in_edge_label && desc_sites.empty ());
}

bool deterministic_node::
is_node_same (deterministic_node & g_n)
{
	if (in_edge_label != g_n.in_edge_label)
		return false;

	if (desc_sites != g_n.desc_sites)
		return false;

	if (in_nodes != g_n.in_nodes)
		return false;

	if (out_edge_list.size () != g_n.out_edge_list.size ())
		return false;

	map<label, label_sites>::iterator outei;
	for (outei = out_edge_list.begin (); outei != out_edge_list.end (); outei++)
	{
		label l = outei->first;
		sites ss = outei->second.second;
		if (!g_n.is_out_edge (l, ss))
			return false;
	}

	return true;
}

void deterministic_node::
insert_desc_site (site s)
{
	desc_sites.insert (s);
}

/**
 * This function inserts an edge from THIS node to DEST node via L. It assumes
 * that THIS node does not already have an out-edge via L, and the
 * IN_EDGE_LABEL of DEST is L.
 */

void deterministic_node::
insert_edge (label l, deterministic_node & dest)
{
	DEBUG ("\ninsert_edge start: %d->f=%d->%d", node_id, l, dest.node_id);
	// check that l == in_edge_label
	if (l != dest.in_edge_label)
	{
		RESULT ("\nError: insert_edge(): l=%d /= in_edge_label=%d of dest=%d", 
			l, dest.in_edge_label, dest.node_id);
		return;
	}

	if (out_edge_list.find (l) != out_edge_list.end ())
	{
		RESULT ("\nError: insert_edge(): THIS node=%d already has out-edge on l=%d", 
			node_id, l);
		return;
	}

	label_sites this_ls = get_label_sites ();
	label_sites dest_ls = dest.get_label_sites ();
	out_edge_list[l] = dest_ls;
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

void deterministic_node::
temp_delete_edge (label l, deterministic_node & dest)
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

	label_sites this_ls = get_label_sites ();
	out_edge_list.erase (l);
	dest.in_nodes.erase (this_ls);
#if DEBUG_CONTAINER
	DEBUG ("\nin_nodes of dest=%d", dest.node_id);
	set<label_sites>::iterator ii;
	for (ii = dest.in_nodes.begin (); ii != dest.in_nodes.end (); ii++)
	{
		sites ss = ii->second;
		print_sites (ss);
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

void deterministic_node::
replace_in_nodes (label_sites & old_ls, label_sites & new_ls)
{
	in_nodes.erase (old_ls);
	in_nodes.insert (new_ls);
}

void deterministic_node::
get_node_stats (unsigned int & edge_count,
	unsigned int & use_sites_count,
	set<site> & unique_use_sites)
{
	map<label, label_sites>::iterator ei;
	for (ei = out_edge_list.begin (); ei != out_edge_list.end (); ei++)
	{
		edge_count++;
	}

	use_sites_count += desc_sites.size ();
	unique_use_sites.insert (desc_sites.begin (), desc_sites.end ());
}

bool deterministic_node::
is_node_okay (deterministic_node & stack)
{
	bool okay = false;

	if (desc_sites.find (DISCONNECTED_LINK) != desc_sites.end ())
        {
                RESULT ("\nError: Graph still has DISCONNECTED_LINK on node=%d", node_id);
                okay = false;
        }
	// Check that if stack is the in-node, then it is the only in-node
	label_sites lss = stack.get_label_sites ();
	if (is_in_node (lss))
	{
		if (in_nodes.size () > 1)
		{
                        RESULT ("\nError: node=%n from stack has more than one in-nodes", node_id);
                        okay = false;
		}
                // Check that if in-edge from stack has desc_site = label in-edge 
		if (desc_sites.size () > 1)
		{
			RESULT ("\nError: desc_sites>1 of node=%d from root node", node_id);
			okay = false;
		}
		site s = *(desc_sites.begin ()); 
                if (in_edge_label != (s * ROOT_LINK))
                {
                        RESULT ("\nError: desc_site=%d is not same as root label=%d",
                                s, node_id);
                        okay = false;
                }
	}

	return okay;
}

bool deterministic_node::
is_out_node_okay (label out_edge_label, deterministic_node & out_n)
{
	bool okay = true;

	if (out_n.in_edge_label != out_edge_label)
        {
                RESULT ("\nError: out_edge_label=%d /= out_n.in_edge_label(id)=%d of out-node=%d",
                        out_edge_label, out_n.in_edge_label, out_n.node_id);
                okay = false;
        }

        // Check that out_n.in_nodes contains THIS node
        label_sites this_lss = get_label_sites ();
        if (!out_n.is_in_node (this_lss))
        {
                RESULT ("\nError: out_n=%d does not contain this node=%d as in_nodes",
                        out_n.node_id, node_id);
                okay = false;
        }

	return okay;
}

bool deterministic_node::
is_in_node_okay (deterministic_node & in_n)
{
	bool okay = true;
	
        if (in_n.out_edge_list.find (in_edge_label) == in_n.out_edge_list.end ())
        {
                RESULT ("\nError: in_node=%d does not have in_edge_label=%d for this node=%d",
                        in_n.node_id, in_edge_label, node_id);
                okay = false;
        }
        // Check that out-nodes of in-n contains THIS node
	label_sites in_n_out_node = in_n.out_edge_list[in_edge_label];
	if (in_n_out_node != get_label_sites ())
        {
                RESULT ("\nError: out-nodes of in_node=%d is not this node=%d",
                        in_n.node_id, node_id);
                okay = false;
        }

	return okay;
}

void deterministic_node::
print_sites (sites & ss)
{
	sites::iterator ssi;
	for (ssi = ss.begin (); ssi != ss.end (); ssi++)
		RESULT ("%d,", *ssi);
}

void deterministic_node::
print_in_edge_list (map<label_sites, deterministic_node *> & nodes)
{
	DEBUG ("\nIn-edge=f=%d,In-nodes=", in_edge_label);
	set<label_sites>::iterator lssi;
	for (lssi = in_nodes.begin (); lssi != in_nodes.end (); lssi++)
	{
		deterministic_node * n = nodes[*lssi];
		DEBUG ("%d,", n->node_id);
	}
	DEBUG ("\nDone in-edges");
}

void deterministic_node::
print_out_edge_list (map<label_sites, deterministic_node *> & nodes)
{
	DEBUG ("\nprint_out_edge_list()");
	map<label, label_sites>::iterator outei;
	for (outei = out_edge_list.begin (); outei != out_edge_list.end (); outei++)
	{
		label l = outei->first;
		label_sites out_ls = outei->second;
		deterministic_node * out_n = nodes[out_ls];
		if (is_stack_node ())
		{
			csvarinfo_t var = program.cs_get_varinfo (l);
			RESULT ("\n\t%d{,", node_id);
			print_sites (desc_sites);
			if (var->is_global_var)
			{
				RESULT ("}-># %s(%d)->%d{,", var->name, l, out_n->node_id);
			}
			else
			{
				RESULT ("}->%s(%d)->%d{", var->name, l, out_n->node_id);
			}
			print_sites (out_n->desc_sites);
			RESULT ("}");
		}
		else
		{
			RESULT ("\n\t%d{", node_id);
			print_sites (desc_sites);
			RESULT ("}->%d->%d{", l, out_n->node_id);
			print_sites (out_n->desc_sites);
			RESULT ("}");
		}
	}	
	DEBUG ("\nDone out-edges");
}

void deterministic_node::
print_node (map<label_sites, deterministic_node *> & nodes)
{
#if DEBUG_CONTAINER
	DEBUG ("\nNode=%d(", node_id);
	print_sites (desc_sites);
	DEBUG (")");
	print_in_edge_list (nodes);
#endif
	print_out_edge_list (nodes);
	DEBUG ("\nDone node");
}

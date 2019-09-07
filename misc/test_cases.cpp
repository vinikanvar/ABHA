
/************************
 * @author Vini Kanvar
************************/

#include "test_cases.hh"

#define DEBUG_CONTAINER 1
#define DEBUG(...) fprintf (dump_file, __VA_ARGS__); fflush (dump_file);
//#define DEBUG(...)

#if 0
void test_deterministic_node ()
{
/*
	liveness_analysis la;
	la.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");

	basic_block_def bb0, bb1, bb2, bb3, bb4, bb5, bb6;
	bb0.index = 0;
	bb1.index = 1;
	bb2.index = 2;
	bb3.index = 3;
	bb4.index = 4;
	bb5.index = 5;
	bb6.index = 6;
        map<pair_of_nodes, deterministic_node *> deterministic_nodes; 
        deterministic_node * root1 = new deterministic_node (&bb0, &bb1); 
        deterministic_node * dest12 = new deterministic_node (&bb0, &bb2); 
        deterministic_node * dest13= new deterministic_node (&bb0, &bb2); 
        deterministic_node * dest14= new deterministic_node (&bb0, &bb4); 
        deterministic_node * dest15= new deterministic_node (&bb0, &bb5); 
        deterministic_node * dest16= new deterministic_node (&bb0, &bb6); 
        deterministic_nodes.clear (); 
        root1->insert_edge (100, dest12, deterministic_nodes); 
        deterministic_nodes.clear (); 
        dest12->insert_edge (100, dest13, deterministic_nodes); 
        deterministic_nodes.clear (); 
        dest13->insert_edge (200, dest16, deterministic_nodes); 
        deterministic_nodes.clear (); 
        dest16->insert_edge (100, dest13, deterministic_nodes); 
        deterministic_nodes.clear (); 
        dest14->insert_edge (100, dest15, deterministic_nodes); 
        dest13->insert_must_alias (dest14); 
        root1->print_graph (NULL, NULL); 
	DEBUG ("\n\n");
	root1->summarize (100);
        root1->print_graph (NULL, NULL); 

	DEBUG ("\n\n");
	deterministic_node * copy = root1->copy_graph ();
        dest12->insert_may_alias (dest13); 
	copy->print_graph (NULL, NULL);

	if (root1->is_graph_same (*copy))
		DEBUG ("\nsame");
	else
		DEBUG ("\nnot same");
*/
}

void test1_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node n1;
	g.nodes[n1.get_node_id ()] = &n1;
	g.stack->insert_edge (ASTERISK, n1);
	non_deterministic_basic_node::initialize_junk_node ();
	g.print_value (NULL);

	DEBUG ("\n\nAfter merging stack node:");
	g.merge_child_nodes (*(g.stack));
	g.print_value (NULL);
}

void test2_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node n1, n2;
	g.nodes[n1.get_node_id ()] = &n1;
	g.nodes[n2.get_node_id ()] = &n2;
	g.stack->insert_edge (13, n1);
	g.stack->insert_edge (13, n2);
	non_deterministic_basic_node::initialize_junk_node ();
	non_deterministic_basic_node * junk = non_deterministic_basic_node::get_junk_node ();
	n1.insert_edge (ASTERISK, *junk);
	n2.insert_edge (ASTERISK, *junk);
	g.print_value (NULL);

	DEBUG ("\n\nAfter merging stack node:");
	g.merge_child_nodes (*(g.stack));
	g.print_value (NULL);
}

void test3_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node n1, n2;
	non_deterministic_basic_node::initialize_junk_node ();
	non_deterministic_basic_node * junk = non_deterministic_basic_node::get_junk_node ();
	g.stack->insert_edge (ASTERISK, *junk);
	g.stack->insert_edge (ASTERISK, *junk);
	g.print_value (NULL);

	DEBUG ("\n\nAfter merging stack node:");
	g.merge_child_nodes (*(g.stack));
	g.print_value (NULL);
}

void test4_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node n1, n2, n3, n4, n5;
	g.nodes[n1.get_node_id ()] = &n1;
	g.nodes[n2.get_node_id ()] = &n2;
	g.nodes[n3.get_node_id ()] = &n3;
	g.nodes[n4.get_node_id ()] = &n4;
	g.nodes[n5.get_node_id ()] = &n5;
	g.stack->insert_edge (13, n1);
	g.stack->insert_edge (13, n2);
//	g.stack->insert_edge (17, n4);	// test with and without this line
	n1.insert_edge (ASTERISK, n3);
	n2.insert_edge (ASTERISK, n4);
	non_deterministic_basic_node::initialize_junk_node ();
	non_deterministic_basic_node * junk = non_deterministic_basic_node::get_junk_node ();
	n3.insert_edge (ASTERISK, *junk);
	n4.insert_edge (ASTERISK, *junk);
	g.print_value (NULL);

	DEBUG ("\n\nAfter merging stack node:");
	g.merge_child_nodes (*(g.stack));
	g.print_value (NULL);
}

void test5_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node n1, n2, n3, n4, n5;
	g.nodes[n1.get_node_id ()] = &n1;
	g.nodes[n2.get_node_id ()] = &n2;
	g.nodes[n3.get_node_id ()] = &n3;
	g.nodes[n4.get_node_id ()] = &n4;
	g.nodes[n5.get_node_id ()] = &n5;
	g.stack->insert_edge (13, n1);
	g.stack->insert_edge (13, n2);
	g.stack->insert_edge (17, n1);
	n1.insert_edge (ASTERISK, n3);
	n2.insert_edge (ASTERISK, n4);
	non_deterministic_basic_node::initialize_junk_node ();
	non_deterministic_basic_node * junk = non_deterministic_basic_node::get_junk_node ();
	n3.insert_edge (ASTERISK, *junk);
	n4.insert_edge (ASTERISK, *junk);
	g.print_value (NULL);

	DEBUG ("\n\nAfter merging stack node:");
	g.merge_child_nodes (*(g.stack));
	g.print_value (NULL);
}

void test6_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11;
	g.nodes[n1.get_node_id ()] = &n1;
	g.nodes[n2.get_node_id ()] = &n2;
	g.nodes[n3.get_node_id ()] = &n3;
	g.nodes[n4.get_node_id ()] = &n4;
	g.nodes[n5.get_node_id ()] = &n5;
	g.nodes[n6.get_node_id ()] = &n6;
	g.nodes[n7.get_node_id ()] = &n7;
	g.nodes[n8.get_node_id ()] = &n8;
	g.nodes[n9.get_node_id ()] = &n9;
	g.nodes[n10.get_node_id ()] = &n10;
	g.nodes[n11.get_node_id ()] = &n11;
	g.stack->insert_edge (13, n1);
	g.stack->insert_edge (13, n2);
	g.stack->insert_edge (13, n3);
	n1.insert_edge (ASTERISK, n4);
	n1.insert_edge (ASTERISK, n5);
	n2.insert_edge (ASTERISK, n4);
	n2.insert_edge (ASTERISK, n5);
	n2.insert_edge (ASTERISK, n6);
	n2.insert_edge (ASTERISK, n7);
	n3.insert_edge (ASTERISK, n4);
	n3.insert_edge (ASTERISK, n5);
	n3.insert_edge (ASTERISK, n7);

	n4.insert_edge (14, n8);
	n5.insert_edge (15, n9);
	n6.insert_edge (16, n10);
	n7.insert_edge (17, n11);
	non_deterministic_basic_node::initialize_junk_node ();
	non_deterministic_basic_node * junk = non_deterministic_basic_node::get_junk_node ();
	g.print_value (NULL);

//	DEBUG ("\n\nAfter merging stack node:");
//	g.merge_child_nodes (*(g.stack));
//	g.print_value (NULL);

	DEBUG ("\n\nAfter merging sibling nodes of %d:", n4.get_node_id ());
	g.merge_with_sibling_nodes (n4);
	g.print_value (NULL);
}

void test7_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n2 = new non_deterministic_basic_node;
	g.nodes[n1->get_node_id ()] = n1;
	g.nodes[n2->get_node_id ()] = n2;
	non_deterministic_basic_node::initialize_junk_node ();
	g.print_value (NULL);

	DEBUG ("\n\ndeleting unreachable nodes:");
	g.clean ();
	g.print_value (NULL);
}

void test8_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n2 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n3 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n4 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n5 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n6 = new non_deterministic_basic_node;
	g.nodes[n1->get_node_id ()] = n1;
	g.nodes[n2->get_node_id ()] = n2;
	g.nodes[n3->get_node_id ()] = n3;
	g.nodes[n4->get_node_id ()] = n4;
	g.nodes[n5->get_node_id ()] = n5;
	g.nodes[n6->get_node_id ()] = n6;
	non_deterministic_basic_node::initialize_junk_node ();
	g.stack->insert_edge (6, *n1);
	n1->insert_edge (ASTERISK, *n2);
	n1->insert_edge (ASTERISK, *n3);
	n2->insert_edge (ASTERISK, *n4);
	n3->insert_edge (ASTERISK, *n4);
	n5->insert_edge (ASTERISK, *n3);
	n6->insert_edge (ASTERISK, *n5);
	g.print_value (NULL);

	DEBUG ("\n\ndeleting unreachable nodes:");
	g.clean ();
	g.print_value (NULL);
}

void test9_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g1;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n2 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n3 = new non_deterministic_basic_node;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	non_deterministic_basic_node::initialize_junk_node ();
	g1.stack->insert_edge (6, *n1);
	g1.stack->insert_edge (7, *n2);
	n1->insert_edge (ASTERISK, *n3);
	n2->insert_edge (ASTERISK, *n3);
	g1.print_value (NULL);

	non_deterministic_basic_graph g2;
	non_deterministic_basic_node * n4 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n5 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n6 = new non_deterministic_basic_node;
	g2.nodes[n4->get_node_id ()] = n4;
	g2.nodes[n5->get_node_id ()] = n5;
	g2.nodes[n6->get_node_id ()] = n6;
	non_deterministic_basic_node::initialize_junk_node ();
	g2.stack->insert_edge (6, *n4);
	g2.stack->insert_edge (8, *n5);	 // TRY WITH : g2.stack->insert_edge (7, *n5);	
	n4->insert_edge (ASTERISK, *n6);
	n5->insert_edge (ASTERISK, *n6);
	g2.print_value (NULL);

	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");

	DEBUG ("\n\ncopy_value()");
	g1.copy_value (g2, false);
	g1.print_value (NULL);
}

void test10_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g1;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n2 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n3 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n4 = new non_deterministic_basic_node;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	non_deterministic_basic_node::initialize_junk_node ();
	g1.stack->insert_edge (6, *n1);
	g1.stack->insert_edge (7, *n2);
	g1.stack->insert_edge (8, *n3);
	n1->insert_edge (ASTERISK, *n4);
	n2->insert_edge (ASTERISK, *n4);
	n3->insert_edge (ASTERISK, *n4);
	g1.print_value (NULL);

	non_deterministic_basic_graph g2;
	non_deterministic_basic_node * n5 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n6 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n7 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n8 = new non_deterministic_basic_node;
	g2.nodes[n5->get_node_id ()] = n5;
	g2.nodes[n6->get_node_id ()] = n6;
	g2.nodes[n7->get_node_id ()] = n7;
	g2.nodes[n8->get_node_id ()] = n8;
	non_deterministic_basic_node::initialize_junk_node ();
	g2.stack->insert_edge (6, *n5);
	g2.stack->insert_edge (7, *n6);
	g2.stack->insert_edge (9, *n7); 	// TRY WITH : g2.stack->insert_edge (8, *n7);
	n5->insert_edge (ASTERISK, *n8);
	n6->insert_edge (ASTERISK, *n8);
	n7->insert_edge (ASTERISK, *n8);
	g2.print_value (NULL);

	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");

	DEBUG ("\n\ncopy_value()");
	g1.copy_value (g2, false);
	g1.print_value (NULL);
}

void test11_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g1;
	non_deterministic_basic_node::initialize_junk_node ();
	g1.print_value (NULL);

	non_deterministic_basic_graph g2;
	g2.print_value (NULL);

	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");

	DEBUG ("\n\ncopy_value()");
	g1.copy_value (g2, false);
	g1.print_value (NULL);
}

void test12_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g1;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	g1.nodes[n1->get_node_id ()] = n1;
	non_deterministic_basic_node::initialize_junk_node ();
	g1.stack->insert_edge (6, *n1);
	n1->insert_edge (ASTERISK, *non_deterministic_basic_node::get_junk_node ());
	g1.print_value (NULL);

	non_deterministic_basic_graph g2;
	g2.print_value (NULL);

	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");

	DEBUG ("\n\ncopy_value()");
	g1.copy_value (g2, false);
	g1.print_value (NULL);
}

void test13_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g1;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n2 = new non_deterministic_basic_node;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	non_deterministic_basic_node::initialize_junk_node ();
	g1.stack->insert_edge (6, *n1);
	g1.stack->insert_edge (7, *n1);		// TRY WITH g1.stack->insert_edge (7, *n2);
	n1->insert_edge (ASTERISK, *n2);
	g1.print_value (NULL);

	non_deterministic_basic_graph g2;
	non_deterministic_basic_node * n3 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n4 = new non_deterministic_basic_node;
	g2.nodes[n3->get_node_id ()] = n3;
	g2.nodes[n4->get_node_id ()] = n4;
	non_deterministic_basic_node::initialize_junk_node ();
	g2.stack->insert_edge (6, *n3);
	g2.stack->insert_edge (7, *n3);		// TRY WITH : g2.stack->insert_edge (7, *n4);
	n3->insert_edge (ASTERISK, *n4);
	g2.print_value (NULL);

	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");

	DEBUG ("\n\ncopy_value()");
	g1.copy_value (g2, false);
	g1.print_value (NULL);
}

void test14_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g1;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n2 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n3 = new non_deterministic_basic_node;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	non_deterministic_basic_node::initialize_junk_node ();
	g1.stack->insert_edge (6, *n1);
	g1.stack->insert_edge (7, *n2);
	n1->insert_edge (ASTERISK, *n3);
	n3->insert_edge (ASTERISK, *n2);
	g1.print_value (NULL);

	non_deterministic_basic_graph g2;
	non_deterministic_basic_node * n4 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n5 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n6 = new non_deterministic_basic_node;
	g2.nodes[n4->get_node_id ()] = n4;
	g2.nodes[n5->get_node_id ()] = n5;
	g2.nodes[n6->get_node_id ()] = n6;
	non_deterministic_basic_node::initialize_junk_node ();
	g2.stack->insert_edge (6, *n4);
	g2.stack->insert_edge (7, *n5);
	n4->insert_edge (ASTERISK, *n6);
	n6->insert_edge (ASTERISK, *n5);
	g2.print_value (NULL);

	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");

	DEBUG ("\n\ncopy_value()");
	g1.copy_value (g2, false);
	g1.print_value (NULL);
}

void test15_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g1;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n2 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n3 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n4 = new non_deterministic_basic_node;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	non_deterministic_basic_node::initialize_junk_node ();
	g1.stack->insert_edge (6, *n1);
	g1.stack->insert_edge (7, *n2);
	n1->insert_edge (ASTERISK, *n3);
	n3->insert_edge (ASTERISK, *n4);
	n1->insert_edge (ASTERISK, *n4);
	n4->insert_edge (ASTERISK, *n2);
	g1.print_value (NULL);

	non_deterministic_basic_graph g2;
	non_deterministic_basic_node * n5 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n6 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n7 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n8 = new non_deterministic_basic_node;
	g2.nodes[n5->get_node_id ()] = n5;
	g2.nodes[n6->get_node_id ()] = n6;
	g2.nodes[n7->get_node_id ()] = n7;
	g2.nodes[n8->get_node_id ()] = n8;
	non_deterministic_basic_node::initialize_junk_node ();
	g2.stack->insert_edge (6, *n5);
	g2.stack->insert_edge (7, *n6);
	n5->insert_edge (ASTERISK, *n7);
	n7->insert_edge (ASTERISK, *n8);
	n5->insert_edge (ASTERISK, *n8);
	n8->insert_edge (ASTERISK, *n6);
	g2.print_value (NULL);

	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");

	DEBUG ("\n\ncopy_value()");
	g1.copy_value (g2, false);
	g1.print_value (NULL);
}

void test16_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g1;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n2 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n3 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n4 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n5 = new non_deterministic_basic_node;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	non_deterministic_basic_node::initialize_junk_node ();
	g1.stack->insert_edge (6, *n1);
	g1.stack->insert_edge (7, *n2);
	n1->insert_edge (ASTERISK, *n3);
	n3->insert_edge (ASTERISK, *n4);
	n1->insert_edge (ASTERISK, *n4);
	n4->insert_edge (ASTERISK, *n2);
	n4->insert_edge (ASTERISK, *n5);
	n5->insert_edge (ASTERISK, *n2);
	g1.print_value (NULL);

	non_deterministic_basic_graph g2;
	non_deterministic_basic_node * n6 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n7 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n8 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n9 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n10 = new non_deterministic_basic_node;
	g2.nodes[n6->get_node_id ()] = n6;
	g2.nodes[n7->get_node_id ()] = n7;
	g2.nodes[n8->get_node_id ()] = n8;
	g2.nodes[n9->get_node_id ()] = n9;
	g2.nodes[n10->get_node_id ()] = n10;
	non_deterministic_basic_node::initialize_junk_node ();
	g2.stack->insert_edge (6, *n6);
	g2.stack->insert_edge (7, *n7);
	n6->insert_edge (ASTERISK, *n8);
	n8->insert_edge (ASTERISK, *n9);
	n6->insert_edge (ASTERISK, *n9);
	n9->insert_edge (ASTERISK, *n7);
	n9->insert_edge (ASTERISK, *n10);
	n10->insert_edge (ASTERISK, *n7);
	g2.print_value (NULL);

	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");

	DEBUG ("\n\ncopy_value()");
	g1.copy_value (g2, false);
	g1.print_value (NULL);
}

void test17_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	g.nodes[n1->get_node_id ()] = n1;
	non_deterministic_basic_node::initialize_junk_node ();
	g.stack->insert_edge (13, *n1);
	g.print_value (NULL);

	set<unsigned int> function_par;
	function_par.insert (15);
	DEBUG ("\n\nget_arg_glob_connected_nodes(): ");
	function_par = g.get_arg_glob_connected_nodes (function_par);
	set<unsigned int>::iterator si;
	for (si = function_par.begin (); si != function_par.end (); si++)
	{
		DEBUG ("%d, ", *si);
	}
	g.print_value (NULL);

	DEBUG ("\n\nextract_arg_glob_connected_graph()");
	non_deterministic_basic_graph * g1 = g.extract_arg_glob_connected_graph (function_par);
	DEBUG ("\nLeft over:\n");
	g.print_value (NULL);
	DEBUG ("\nExtracted\n");
	g1->print_value (NULL);

	set<unsigned int> lv;
	DEBUG ("\n\ndelete_local_variables");
	lv.insert (13);
	g.delete_local_variables (lv);
	g.print_value (NULL);
}

void test18_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n2 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n3 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n4 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n5 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n6 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n7 = new non_deterministic_basic_node;
	g.nodes[n1->get_node_id ()] = n1;
	g.nodes[n2->get_node_id ()] = n2;
	g.nodes[n3->get_node_id ()] = n3;
	g.nodes[n4->get_node_id ()] = n4;
	g.nodes[n5->get_node_id ()] = n5;
	g.nodes[n6->get_node_id ()] = n6;
	g.nodes[n7->get_node_id ()] = n7;
	non_deterministic_basic_node::initialize_junk_node ();
	g.stack->insert_edge (13, *n1);
	g.stack->insert_edge (15, *n2);
	g.stack->insert_edge (17, *n3);
	n1->insert_edge (ASTERISK, *n4);
	n4->insert_edge (ASTERISK, *n7);
	n2->insert_edge (ASTERISK, *n5);
//	n2->insert_edge (ASTERISK, *n6);
	n3->insert_edge (ASTERISK, *n6);
	n5->insert_edge (ASTERISK, *n7);
	g.print_value (NULL);

	set<unsigned int> function_par;
	function_par.insert (15);
	DEBUG ("\n\nget_arg_glob_connected_nodes()");
	function_par = g.get_arg_glob_connected_nodes (function_par);
	set<unsigned int>::iterator si;
	for (si = function_par.begin (); si != function_par.end (); si++)
	{
		DEBUG ("%d, ", *si);
	}

	g.print_value (NULL);

	DEBUG ("\n\nextract_arg_glob_connected_graph()");
	non_deterministic_basic_graph * g1 = g.extract_arg_glob_connected_graph (function_par);
	DEBUG ("\nLeft over:\n");
	g.print_value (NULL);
	DEBUG ("\nExtracted\n");
	g1->print_value (NULL);

	set<unsigned int> lv;
	DEBUG ("\n\ndelete_local_variables");
	lv.insert (13);
	g1->delete_local_variables (lv);
	g1->print_value (NULL);
}

void test19_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n2 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n3 = new non_deterministic_basic_node;
	g.nodes[n1->get_node_id ()] = n1;
	g.nodes[n2->get_node_id ()] = n2;
	g.nodes[n3->get_node_id ()] = n3;
	non_deterministic_basic_node::initialize_junk_node ();
	g.stack->insert_edge (13, *n1);
	g.stack->insert_edge (15, *n2);
	g.stack->insert_edge (17, *n3);
	n3->insert_edge (ASTERISK, *n2);
	g.print_value (NULL);

	set<unsigned int> function_par;
	function_par.insert (13);
	DEBUG ("\n\nget_arg_glob_connected_nodes()");
	function_par = g.get_arg_glob_connected_nodes (function_par);
	set<unsigned int>::iterator si;
	for (si = function_par.begin (); si != function_par.end (); si++)
	{
		DEBUG ("%d, ", *si);
	}
	g.print_value (NULL);

	DEBUG ("\n\nextract_arg_glob_connected_graph()");
	non_deterministic_basic_graph * g1 = g.extract_arg_glob_connected_graph (function_par);
	DEBUG ("\nLeft over:\n");
	g.print_value (NULL);
	DEBUG ("\nExtracted\n");
	g1->print_value (NULL);

	set<unsigned int> lv;
	DEBUG ("\n\ndelete_local_variables");
	lv.insert (15);
	g1->delete_local_variables (lv);
	g1->print_value (NULL);
}

void test20_non_deterministic_basic_graph ()
{
	non_deterministic_basic_graph g;
	non_deterministic_basic_node * n1 = new non_deterministic_basic_node;
	non_deterministic_basic_node * n2 = new non_deterministic_basic_node;
	g.nodes[n1->get_node_id ()] = n1;
	g.nodes[n2->get_node_id ()] = n2;
	non_deterministic_basic_node::initialize_junk_node ();
	non_deterministic_basic_node * junk = non_deterministic_basic_node::get_junk_node ();
	g.stack->insert_edge (13, *n1);
	g.stack->insert_edge (15, *n2);
	n1->insert_edge (ASTERISK, *junk);
	n2->insert_edge (ASTERISK, *junk);
	g.print_value (NULL);

	set<unsigned int> function_par;
	function_par.insert (15);
	DEBUG ("\n\nget_arg_glob_connected_nodes()");
	function_par = g.get_arg_glob_connected_nodes (function_par);
	set<unsigned int>::iterator si;
	for (si = function_par.begin (); si != function_par.end (); si++)
	{
		DEBUG ("%d, ", *si);
	}
	g.print_value (NULL);

	DEBUG ("\n\nextract_arg_glob_connected_graph()");
	non_deterministic_basic_graph * g1 = g.extract_arg_glob_connected_graph (function_par);
	DEBUG ("\nLeft over:\n");
	g.print_value (NULL);
	DEBUG ("\nExtracted\n");
	g1->print_value (NULL);

	set<unsigned int> lv;
	DEBUG ("\n\ndelete_local_variables");
	lv.insert (13);
	g1->delete_local_variables (lv);
	g1->print_value (NULL);
}

void test21_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1, g2;
	node_index s1 = g1.stack->get_node_id ();
	node_index s2 = g2.stack->get_node_id ();
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n4->get_node_id ()] = n4;
	g2.nodes[n2->get_node_id ()] = n2;
	g2.nodes[n3->get_node_id ()] = n3;
	g1.stack->insert_edge (13, *n1 ,s1);
	n1->insert_edge (13, *n1, s1);
	n1->insert_edge (13, *n4, s1);
	n4->insert_edge (13, *n1, s1);
	g2.stack->insert_edge (13, *n3, s2);
	n3->insert_edge (13, *n3, s2);
	n3->insert_edge (13, *n2, s2);
	n2->insert_edge (13, *n3, s2);
	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nGraph 2\n");
	g2.print_value (NULL);

	map<node_index, node_index> visited_pairs;
	map<state_index, state_index, state_order> equiv_state_pairs;
	if (g1.stack->depth_first_comparison (*g2.stack, g1.nodes, g2.nodes, visited_pairs, equiv_state_pairs))
	{
		DEBUG ("\nG1 and G2 have same out graphs");
		DEBUG ("\nNodes mapping: ");
		map<node_index, node_index>::iterator vpi;
		for (vpi = visited_pairs.begin (); vpi != visited_pairs.end (); vpi++)
			DEBUG ("(%d,%d),", vpi->first, vpi->second);
	}
	else
		DEBUG ("\nG1 and G2 have different graphs");
}

void test22_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1, g2;
	node_index s1 = g1.stack->get_node_id ();
	node_index s2 = g2.stack->get_node_id ();
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n9 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n10 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n11 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n12 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n13 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n14 = new non_deterministic_simple_node;

	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;
	g1.nodes[n7->get_node_id ()] = n7;

	g2.nodes[n8->get_node_id ()] = n8;
	g2.nodes[n9->get_node_id ()] = n9;
	g2.nodes[n10->get_node_id ()] = n10;
	g2.nodes[n11->get_node_id ()] = n11;
	g2.nodes[n12->get_node_id ()] = n12;
	g2.nodes[n13->get_node_id ()] = n13;
	g2.nodes[n14->get_node_id ()] = n14;

	g1.stack->insert_edge (13, *n1 ,s1);
	n1->insert_edge (13, *n2 ,s1);
	n1->insert_edge (13, *n3 ,s1);
	n2->insert_edge (13, *n4 ,s1);
	n3->insert_edge (13, *n5 ,s1);
	n3->insert_edge (13, *n6 ,s1);
	n4->insert_edge (13, *n6 ,s1);
	n5->insert_edge (13, *n7 ,s1);
	n6->insert_edge (13, *n7 ,s1);

	g2.stack->insert_edge (13, *n8 ,s2);
	n8->insert_edge (13, *n9 ,s2);
	n8->insert_edge (13, *n10 ,s2);
	n9->insert_edge (13, *n11 ,s2);
	n10->insert_edge (13, *n13 ,s2);
	n11->insert_edge (13, *n12 ,s2);
	n11->insert_edge (13, *n13 ,s2);
	n12->insert_edge (13, *n14 ,s2);
	n13->insert_edge (13, *n14 ,s2);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nGraph 2\n");
	g2.print_value (NULL);

	// SHOULD PRINT DIFFERENT
	map<node_index, node_index> visited_pairs;
	map<state_index, state_index, state_order> equiv_state_pairs;
	if (g1.stack->depth_first_comparison (*g2.stack, g1.nodes, g2.nodes, visited_pairs, equiv_state_pairs))
	{
		DEBUG ("\nG1 and G2 have same out graphs");
		DEBUG ("\nNodes mapping: ");
		map<node_index, node_index>::iterator vpi;
		for (vpi = visited_pairs.begin (); vpi != visited_pairs.end (); vpi++)
			DEBUG ("(%d,%d),", vpi->first, vpi->second);
	}
	else
		DEBUG ("\nG1 and G2 have different graphs");
}

void test23_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1, g2;
	node_index s1 = g1.stack->get_node_id ();
	node_index s2 = g2.stack->get_node_id ();
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n9 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n10 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n11 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n12 = new non_deterministic_simple_node;

	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;

	g2.nodes[n7->get_node_id ()] = n7;
	g2.nodes[n8->get_node_id ()] = n8;
	g2.nodes[n9->get_node_id ()] = n9;
	g2.nodes[n10->get_node_id ()] = n10;
	g2.nodes[n11->get_node_id ()] = n11;
	g2.nodes[n12->get_node_id ()] = n12;

	g1.stack->insert_edge (13, *n1 ,s1);
	n1->insert_edge (13, *n2 ,s1);
	n1->insert_edge (13, *n3 ,s1);
	n2->insert_edge (13, *n4 ,s1);
	n2->insert_edge (13, *n5 ,s1);
	n3->insert_edge (13, *n5 ,s1);
	n5->insert_edge (13, *n6 ,s1);

	g2.stack->insert_edge (13, *n7 ,s2);
	n7->insert_edge (13, *n8 ,s2);
	n7->insert_edge (13, *n9 ,s2);
	n8->insert_edge (13, *n10 ,s2);
	n8->insert_edge (13, *n11 ,s2);
	n9->insert_edge (13, *n10 ,s2);	// DIFFERENT
//	n9->insert_edge (13, *n11 ,s2);	// SAME
	n11->insert_edge (13, *n12 ,s2);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nGraph 2\n");
	g2.print_value (NULL);

	map<node_index, node_index> visited_pairs;
	map<state_index, state_index, state_order> equiv_state_pairs;
	if (g1.stack->depth_first_comparison (*g2.stack, g1.nodes, g2.nodes, visited_pairs, equiv_state_pairs))
	{
		DEBUG ("\nG1 and G2 have same out graphs");
		DEBUG ("\nNodes mapping: ");
		map<node_index, node_index>::iterator vpi;
		for (vpi = visited_pairs.begin (); vpi != visited_pairs.end (); vpi++)
			DEBUG ("(%d,%d),", vpi->first, vpi->second);
	}
	else
		DEBUG ("\nG1 and G2 have different graphs");
}

void test24_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n0 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n9 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n10 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n11 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n12 = new non_deterministic_simple_node;

	g1.nodes[n0->get_node_id ()] = n0;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;
	g1.nodes[n7->get_node_id ()] = n7;
	g1.nodes[n8->get_node_id ()] = n8;
	g1.nodes[n9->get_node_id ()] = n9;
	g1.nodes[n10->get_node_id ()] = n10;
	g1.nodes[n11->get_node_id ()] = n11;
	g1.nodes[n12->get_node_id ()] = n12;

	g1.stack->insert_edge (13, *n0 ,s1);
	n0->insert_edge (13, *n7 ,s1);
	n0->insert_edge (13, *n10 ,s1);
	n0->insert_edge (13, *n11 ,s1);
	n0->insert_edge (13, *n12 ,s1);
	n7->insert_edge (13, *n3 ,s1);
	n7->insert_edge (13, *n4 ,s1);
	n11->insert_edge (13, *n8 ,s1);
	n12->insert_edge (13, *n9 ,s1);
	n10->insert_edge (13, *n6 ,s1);
	n8->insert_edge (13, *n4 ,s1);
	n9->insert_edge (13, *n5 ,s1);
	n9->insert_edge (13, *n6 ,s1);
	n5->insert_edge (13, *n2 ,s1);
	n6->insert_edge (13, *n2 ,s1); 
	n3->insert_edge (13, *n1 ,s1); 
	n4->insert_edge (13, *n1 ,s1); 

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);

	// SHOULD PRINT DIFFERENT
	map<node_index, node_index> visited_nodes;
	if (n1->is_in_graph_isomorphic (*n2, g1.nodes, g1.nodes, visited_nodes))
		DEBUG ("\nN1 and N2 have same out graphs");
	else
		DEBUG ("\nN1 and N2 have different graphs");
}

void test25_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n0 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;

	g1.nodes[n0->get_node_id ()] = n0;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;

	g1.stack->insert_edge (13, *n0 ,s1);
	n0->insert_edge (13, *n1 ,s1);
	n0->insert_edge (13, *n2 ,s1);
	n1->insert_edge (13, *n2 ,s1);
	n2->insert_edge (13, *n1 ,s1);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);

	// SHOULD PRINT DIFFERENT
	map<node_index, node_index> visited_nodes;
	if (n1->is_in_graph_isomorphic (*n2, g1.nodes, g1.nodes, visited_nodes))
		DEBUG ("\nN1 and N2 have same out graphs");
	else
		DEBUG ("\nN1 and N2 have different graphs");
}

void test26_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n0 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;

	g1.nodes[n0->get_node_id ()] = n0;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;

	g1.stack->insert_edge (13, *n0 ,s1);
	n0->insert_edge (13, *n1 ,s1);
	n0->insert_edge (13, *n2 ,s1);
	n1->insert_edge (13, *n2 ,s1);
	n2->insert_edge (13, *n1 ,s1);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);

	// SHOULD PRINT DIFFERENT
	map<node_index, node_index> visited_nodes;
	if (n1->is_in_graph_isomorphic (*n2, g1.nodes, g1.nodes, visited_nodes))
		DEBUG ("\nN1 and N2 have same out graphs");
	else
		DEBUG ("\nN1 and N2 have different graphs");
}

void test27_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n0 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;

	g1.nodes[n0->get_node_id ()] = n0;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;

	g1.stack->insert_edge (13, *n0 ,s1);
	n0->insert_edge (13, *n1 ,s1);
	n0->insert_edge (13, *n2 ,s1);
	n1->insert_edge (13, *n1 ,s1);
	n2->insert_edge (13, *n2 ,s1);
	n1->insert_edge (13, *n2 ,s1);
	n2->insert_edge (13, *n1 ,s1);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);

	// SHOULD PRINT DIFFERENT
	map<node_index, node_index> visited_nodes;
	if (n1->is_in_graph_isomorphic (*n2, g1.nodes, g1.nodes, visited_nodes))
		DEBUG ("\nN1 and N2 have same out graphs");
	else
		DEBUG ("\nN1 and N2 have different graphs");
}

void test28_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n0 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;

	g1.nodes[n0->get_node_id ()] = n0;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;

	g1.stack->insert_edge (13, *n0 ,s1);
	n0->insert_edge (13, *n3 ,s1);
	n0->insert_edge (13, *n4 ,s1);
	n3->insert_edge (13, *n1 ,s1);
	n4->insert_edge (13, *n2 ,s1);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);

	// SHOULD PRINT DIFFERENT
	map<node_index, node_index> visited_nodes;
	if (n1->is_in_graph_isomorphic (*n2, g1.nodes, g1.nodes, visited_nodes))
		DEBUG ("\nN1 and N2 have same out graphs");
	else
		DEBUG ("\nN1 and N2 have different graphs");
}

void test29_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n0 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;

	g1.nodes[n0->get_node_id ()] = n0;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;

	g1.stack->insert_edge (13, *n0 ,s1);
	n0->insert_edge (13, *n3 ,s1);
	n0->insert_edge (13, *n4 ,s1);
	n3->insert_edge (13, *n1 ,s1);
	n3->insert_edge (13, *n2 ,s1);
	n4->insert_edge (13, *n1 ,s1);
	n4->insert_edge (13, *n2 ,s1);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);

	// SHOULD PRINT DIFFERENT
	map<node_index, node_index> visited_nodes;
	if (n1->is_in_graph_isomorphic (*n2, g1.nodes, g1.nodes, visited_nodes))
		DEBUG ("\nN1 and N2 have same out graphs");
	else
		DEBUG ("\nN1 and N2 have different graphs");
}

void test30_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n0 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n9 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n10 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n11 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n12 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n13 = new non_deterministic_simple_node;

	g1.nodes[n0->get_node_id ()] = n0;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;
	g1.nodes[n7->get_node_id ()] = n7;
	g1.nodes[n8->get_node_id ()] = n8;
	g1.nodes[n9->get_node_id ()] = n9;
	g1.nodes[n10->get_node_id ()] = n10;
	g1.nodes[n11->get_node_id ()] = n11;
	g1.nodes[n12->get_node_id ()] = n12;
	g1.nodes[n13->get_node_id ()] = n13;

	g1.stack->insert_edge (13, *n0 ,s1);
	n0->insert_edge (14, *n1 ,s1);
	n0->insert_edge (15, *n2 ,s1);
	n0->insert_edge (15, *n3 ,s1);
	n0->insert_edge (17, *n4 ,s1);
	n0->insert_edge (18, *n5 ,s1);
	n0->insert_edge (19, *n6 ,s1);
	n0->insert_edge (20, *n7 ,s1);
	n0->insert_edge (21, *n8 ,s1);
	n0->insert_edge (22, *n9 ,s1);
	n0->insert_edge (22, *n10 ,s1);
	n0->insert_edge (24, *n11 ,s1);
	n0->insert_edge (25, *n12 ,s1);
	n0->insert_edge (26, *n13 ,s1);
	n1->insert_edge (0, *n2 ,s1);
	n1->insert_edge (0, *n3 ,s1);
	n2->insert_edge (32, *n9 ,s1);
	n3->insert_edge (32, *n10 ,s1);
	n4->insert_edge (0, *n2 ,s1);
	n4->insert_edge (0, *n3 ,s1);
	n4->insert_edge (0, *n9 ,s1);
	n4->insert_edge (0, *n10 ,s1);
	n5->insert_edge (0, *n2 ,s1);
	n5->insert_edge (0, *n3 ,s1);
	n6->insert_edge (0, *n2 ,s1);
	n6->insert_edge (0, *n3 ,s1);
	n7->insert_edge (0, *n2 ,s1);
	n7->insert_edge (0, *n3 ,s1);
	n7->insert_edge (0, *n9 ,s1);
	n7->insert_edge (0, *n10 ,s1);
	n8->insert_edge (0, *n9 ,s1);
	n8->insert_edge (0, *n10 ,s1);
	n9->insert_edge (32, *n9 ,s1);
	n10->insert_edge (32, *n10 ,s1);
	n11->insert_edge (0, *n2 ,s1);
	n11->insert_edge (0, *n3 ,s1);
	n11->insert_edge (0, *n9 ,s1);
	n11->insert_edge (0, *n10 ,s1);
	n12->insert_edge (0, *n9 ,s1);
	n12->insert_edge (0, *n10 ,s1);
	n13->insert_edge (0, *n2 ,s1);
	n13->insert_edge (0, *n3 ,s1);
	n13->insert_edge (0, *n9 ,s1);
	n13->insert_edge (0, *n10 ,s1);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);

	map<node_index, node_index> visited_nodes;
	if (n9->is_in_graph_isomorphic (*n10, g1.nodes, g1.nodes, visited_nodes))
		DEBUG ("\nN1=%d and N2=%d have same in graphs", n9->get_node_id (), n10->get_node_id ());
	else
		DEBUG ("\nN1=%d and N2=%d have different in graphs", n9->get_node_id (), n10->get_node_id ());
}


void test31_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1, g2;
	node_index s1 = g1.stack->get_node_id ();
	node_index s2 = g2.stack->get_node_id ();
	non_deterministic_simple_node * n01 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n02 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;

	g1.nodes[n01->get_node_id ()] = n01;
	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g2.nodes[n02->get_node_id ()] = n02;
	g2.nodes[n3->get_node_id ()] = n3;
	g2.nodes[n4->get_node_id ()] = n4;

	g1.stack->insert_edge (9, *n01 ,s1);
	n01->insert_edge (13, *n1 ,s1);
	n01->insert_edge (15, *n1 ,s1);
	n01->insert_edge (17, *n2 ,s1);
	n1->insert_edge (13, *n1 ,s1);
	n1->insert_edge (15, *n1 ,s1);
	n1->insert_edge (17, *n2 ,s1);
	n2->insert_edge (19, *n1 ,s1);

	g2.stack->insert_edge (9, *n02 ,s2);
	n02->insert_edge (13, *n3 ,s2);
	n02->insert_edge (15, *n3 ,s2);
	n02->insert_edge (17, *n4 ,s2);
	n3->insert_edge (13, *n3 ,s2);
	n3->insert_edge (15, *n3 ,s2);
	n3->insert_edge (17, *n4 ,s2);
	n4->insert_edge (19, *n3 ,s2);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\nGraph 2\n");
	g2.print_value (NULL);

	map<node_index, node_index> visited_nodes;
	g1.copy_value (g2, false);
	DEBUG ("\nGraph 1--after merge\n");
	g1.print_value (NULL);
	DEBUG ("\nGraph 2--after merge\n");
	g2.print_value (NULL);
}

void test32_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;

	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;
	g1.nodes[n7->get_node_id ()] = n7;
	g1.nodes[n8->get_node_id ()] = n8;

	g1.stack->insert_edge (100, *n1 ,s1);
	n1->insert_edge (0, *n2 ,s1);
	n2->insert_edge (1, *n3 ,s1);
	n2->insert_edge (5, *n7 ,s1);
	n3->insert_edge (2, *n4 ,s1);
	n7->insert_edge (6, *n4 ,s1);
	n4->insert_edge (3, *n5 ,s1);
	n4->insert_edge (7, *n8 ,s1);
	n5->insert_edge (4, *n6 ,s1);
	n4->insert_edge (8, *n4 ,s1);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\nAccess paths");
	g1.print_access_paths ();
}

void test33_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n9 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n10 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n11 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n12 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n13 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n14 = new non_deterministic_simple_node;
	non_deterministic_simple_node * d1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * d2 = new non_deterministic_simple_node;

	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;
	g1.nodes[n7->get_node_id ()] = n7;
	g1.nodes[n8->get_node_id ()] = n8;
	g1.nodes[n9->get_node_id ()] = n9;
	g1.nodes[n10->get_node_id ()] = n10;
	g1.nodes[n11->get_node_id ()] = n11;
	g1.nodes[n12->get_node_id ()] = n12;
	g1.nodes[n13->get_node_id ()] = n13;
	g1.nodes[n14->get_node_id ()] = n14;
	g1.nodes[d1->get_node_id ()] = d1;
	g1.nodes[d2->get_node_id ()] = d2;

	label p = 11;
	label q = 13;
	label dl1 = 15;
	label dl2 = 17;
	label left = 19;
	label right = 21;
	label basic = 23;

	// Edges from root
	g1.stack->insert_edge (q, *n1 ,s1);
	g1.stack->insert_edge (q, *n4 ,s1);
	g1.stack->insert_edge (q, *n9 ,s1);
	g1.stack->insert_edge (q, *n12 ,s1);
	g1.stack->insert_edge (p, *n2 ,s1);
	g1.stack->insert_edge (p, *n3 ,s1);
	g1.stack->insert_edge (p, *n5 ,s1);
	g1.stack->insert_edge (p, *n6 ,s1);
	g1.stack->insert_edge (p, *n7 ,s1);
	g1.stack->insert_edge (p, *n8 ,s1);
	g1.stack->insert_edge (p, *n10 ,s1);
	g1.stack->insert_edge (p, *n11 ,s1);
	g1.stack->insert_edge (p, *n13 ,s1);
	g1.stack->insert_edge (p, *n14 ,s1);
	g1.stack->insert_edge (dl1, *d1 ,s1);
	g1.stack->insert_edge (dl2, *d2 ,s1);

	// q to p left-edges
	n1->insert_edge (left, *n2 ,s1);
	n1->insert_edge (left, *n3 ,s1);
	n4->insert_edge (left, *n5 ,s1);
	n4->insert_edge (left, *n6 ,s1);
	n4->insert_edge (left, *n7 ,s1);
	n4->insert_edge (left, *n8 ,s1);
	n9->insert_edge (left, *n10 ,s1);
	n9->insert_edge (left, *n11 ,s1);
	n12->insert_edge (left, *n13 ,s1);
	n12->insert_edge (left, *n14 ,s1);

	// p to p left-edges
	n2->insert_edge (left, *n3 ,s1);
	n3->insert_edge (left, *n2 ,s1);
	n5->insert_edge (left, *n6 ,s1);
	n6->insert_edge (left, *n5 ,s1);
	n7->insert_edge (left, *n8 ,s1);
	n8->insert_edge (left, *n7 ,s1);
	n10->insert_edge (left, *n11 ,s1);
	n11->insert_edge (left, *n10 ,s1);
	n13->insert_edge (left, *n14 ,s1);
	n14->insert_edge (left, *n13 ,s1);

	// self loops
	n2->insert_edge (left, *n2 ,s1);
	n3->insert_edge (left, *n3 ,s1);
	n5->insert_edge (left, *n5 ,s1);
	n6->insert_edge (left, *n6 ,s1);
	n7->insert_edge (left, *n7 ,s1);
	n8->insert_edge (left, *n8 ,s1);
	n10->insert_edge (left, *n10 ,s1);
	n11->insert_edge (left, *n11 ,s1);
	n13->insert_edge (left, *n13 ,s1);
	n14->insert_edge (left, *n14 ,s1);

	// q to p right-edges
	n1->insert_edge (right, *n3 ,s1);
	n4->insert_edge (right, *n6 ,s1);
	n4->insert_edge (right, *n8 ,s1);
	n9->insert_edge (right, *n11 ,s1);
	n12->insert_edge (right, *n14 ,s1);

	// p to q basic-edges
	n5->insert_edge (basic, *n4 ,s1);
	n6->insert_edge (basic, *n4 ,s1);
	n7->insert_edge (basic, *n4 ,s1);
	n8->insert_edge (basic, *n4 ,s1);
	n10->insert_edge (basic, *n9 ,s1);
	n11->insert_edge (basic, *n9 ,s1);
	n11->insert_edge (basic, *n12 ,s1);
	n14->insert_edge (basic, *n12 ,s1);
	n14->insert_edge (basic, *n9 ,s1);

	// d1 to p edges
	d1->insert_edge (0, *n5 ,s1);
	d1->insert_edge (0, *n6 ,s1);
	d1->insert_edge (0, *n7 ,s1);
	d1->insert_edge (0, *n8 ,s1);
	d1->insert_edge (0, *n10 ,s1);
	d1->insert_edge (0, *n11 ,s1);

	// d2 to p edges
	d2->insert_edge (0, *n8 ,s1);
	d2->insert_edge (0, *n11 ,s1);
	d2->insert_edge (0, *n14 ,s1);

	DEBUG ("\nGraph - before edge1\n");
	g1.print_value (NULL);
	g1.is_graph_okay ();

	// Insert edges D2=q->right
	set<node_index> src;
	set<node_index> dest;
	src.insert (d2->get_node_id ());
	dest.insert (n3->get_node_id ());
        dest.insert (n6->get_node_id ());	// Merges n5 with n7, n6 with n8
	dest.insert (n8->get_node_id ());
	dest.insert (n11->get_node_id ());
	dest.insert (n14->get_node_id ());
	g1.insert_edges (src, dest, 0);

	DEBUG ("\nGraph - after edge1\n");
	g1.print_value (NULL);
	g1.is_graph_okay ();

	// Insert edges D2->basic = q
	src.clear ();
	dest.clear ();
	src.insert (n3->get_node_id ());
	src.insert (n6->get_node_id ());
	src.insert (n8->get_node_id ());
	src.insert (n11->get_node_id ());
	src.insert (n14->get_node_id ());
	dest.insert (n1->get_node_id ());
	dest.insert (n4->get_node_id ());
	dest.insert (n9->get_node_id ());
	dest.insert (n12->get_node_id ());
	g1.insert_edges (src, dest, basic);
	// This edge addition was wrong with a previous (buggy) definition of
	// transfer_out_edges (). We updated the definition by performing the
	// merge of affected nodes (rhs nodes) in merge_nodes (). Now it works
	// fine. With previous definition of transfer_out_edges (), there is
	// only 1 q node (wrong). With revised (corrected) definition of
	// transfer_out_edges (), there are 2 q nodes (correct).

	DEBUG ("\nGraph - after edge2\n");
	g1.print_value (NULL);
	g1.is_graph_okay ();
	
	g1.clean ();
	DEBUG ("\nGraph - after clean\n");
	g1.print_value (NULL);
	g1.is_graph_okay ();
}

void test34_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();

	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;

	g1.stack->insert_edge (13, *n2 ,s1);
	g1.stack->insert_edge (17, *n5 ,s1);
	g1.stack->insert_edge (19, *n3 ,s1);
	g1.stack->insert_edge (19, *n4 ,s1);
	
	n2->insert_edge (0, *n3 ,s1);
	n2->insert_edge (0, *n4 ,s1);
	n5->insert_edge (0, *n4 ,s1);

/////////////////////////////////////

	non_deterministic_simple_graph g2;
	node_index s2 = g2.stack->get_node_id ();

	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n9 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n10 = new non_deterministic_simple_node;
	g2.nodes[n7->get_node_id ()] = n7;
	g2.nodes[n8->get_node_id ()] = n8;
	g2.nodes[n9->get_node_id ()] = n9;
	g2.nodes[n10->get_node_id ()] = n10;

	g2.stack->insert_edge (13, *n7 ,s2);
	g2.stack->insert_edge (17, *n10 ,s2);
	g2.stack->insert_edge (19, *n8 ,s2);
	g2.stack->insert_edge (19, *n9 ,s2);
	
	n7->insert_edge (0, *n8 ,s2);
	n7->insert_edge (0, *n9 ,s2);
	n10->insert_edge (0, *n8 ,s2);

	g1.clean ();
	g2.clean ();

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nGraph 2\n");
	g2.print_value (NULL);

	map<node_index, node_index> visited_pairs;
	if (g1.is_value_same (g2))
	{
		DEBUG ("\nG1 and G2 have same out graphs");
		DEBUG ("\nNodes mapping: ");
		map<node_index, node_index>::iterator vpi;
		for (vpi = visited_pairs.begin (); vpi != visited_pairs.end (); vpi++)
			DEBUG ("(%d,%d),", vpi->first, vpi->second);
	}
	else
		DEBUG ("\nG1 and G2 have different graphs");
}

void test35_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();

	non_deterministic_simple_node * n11 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n12 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n13 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n14 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n15 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n16 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n17 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n18 = new non_deterministic_simple_node;
	g1.nodes[n11->get_node_id ()] = n11;
	g1.nodes[n12->get_node_id ()] = n12;
	g1.nodes[n13->get_node_id ()] = n13;
	g1.nodes[n14->get_node_id ()] = n14;
	g1.nodes[n15->get_node_id ()] = n15;
	g1.nodes[n16->get_node_id ()] = n16;
	g1.nodes[n17->get_node_id ()] = n17;
	g1.nodes[n18->get_node_id ()] = n18;

	g1.stack->insert_edge (0, *n12 ,s1);
	g1.stack->insert_edge (0, *n13 ,s1);
	g1.stack->insert_edge (13, *n14 ,s1);
	
	n12->insert_edge (0, *n14 ,s1);
	//n12->insert_edge (0, *n15 ,s1);
	n13->insert_edge (0, *n14 ,s1);
	//n13->insert_edge (0, *n17 ,s1);
	//n15->insert_edge (0, *n18 ,s1);

/////////////////////////////////////

	non_deterministic_simple_graph g2;
	node_index s2 = g2.stack->get_node_id ();

	non_deterministic_simple_node * n21 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n22 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n23 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n24 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n25 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n26 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n27 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n28 = new non_deterministic_simple_node;
	g2.nodes[n21->get_node_id ()] = n21;
	g2.nodes[n22->get_node_id ()] = n22;
	g2.nodes[n23->get_node_id ()] = n23;
	g2.nodes[n24->get_node_id ()] = n24;
	g2.nodes[n25->get_node_id ()] = n25;
	g2.nodes[n26->get_node_id ()] = n26;
	g2.nodes[n27->get_node_id ()] = n27;
	g2.nodes[n28->get_node_id ()] = n28;

	g2.stack->insert_edge (0, *n22 ,s2);
	g2.stack->insert_edge (0, *n23 ,s2);
	g2.stack->insert_edge (13, *n24 ,s2);
	
	n22->insert_edge (0, *n24 ,s2);
	//n22->insert_edge (0, *n25 ,s2);
	n23->insert_edge (0, *n24 ,s2);
	//n23->insert_edge (0, *n27 ,s2);
	//n27->insert_edge (0, *n28 ,s2);

	g1.clean ();
	g2.clean ();

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nGraph 2\n");
	g2.print_value (NULL);

	map<node_index, node_index> visited_pairs;
	if (g1.is_value_same (g2))
	{
		DEBUG ("\nG1 and G2 have same out graphs");
		DEBUG ("\nNodes mapping: ");
		map<node_index, node_index>::iterator vpi;
		for (vpi = visited_pairs.begin (); vpi != visited_pairs.end (); vpi++)
			DEBUG ("(%d,%d),", vpi->first, vpi->second);
	}
	else
		DEBUG ("\nG1 and G2 have different graphs");
}

void test36_non_deterministic_simple_graph ()
{
	struct cgraph_node * cnode = cgraph_nodes;
	basic_block bb, bb2;
	if (cnode)
	{
		DEBUG ("\ncgraph_nodes is not empty");
		struct function * function_decl = DECL_STRUCT_FUNCTION (cnode->decl);
		basic_block block;
		int i=1;
		FOR_EACH_BB_FN (block, function_decl)	
		{
			if (i == 1)
				bb = block;
			if (i == 2)
				bb2 = block;
			if (i == 2)
				break;
			i++;
	
		}
		DEBUG ("\nfunction: %s, bb: %d, bb2: %d", cgraph_node_name (cnode), bb->index, bb2->index);
	}
	else
		DEBUG ("\ncgraph_nodes is null");

	context<non_deterministic_simple_graph, variables> c1 (cnode, NULL, NULL, NULL, NULL, NULL);
	context<non_deterministic_simple_graph, variables> c2 (cnode, NULL, NULL, NULL, NULL, NULL);
	context<non_deterministic_simple_graph, variables> c3 (cnode, NULL, NULL, NULL, NULL, NULL);
	context<non_deterministic_simple_graph, variables> c4 (cnode, NULL, NULL, NULL, NULL, NULL);
	c1.add_destination_context (bb, &c2);
	c2.add_source_context (&c1, bb);
	c2.add_destination_context (bb, &c3);
	c3.add_source_context (&c2, bb);
	c3.add_destination_context (bb, &c4);
	c4.add_source_context (&c3, bb);
	c2.add_destination_context (bb2, &c2);
	c2.add_source_context (&c2, bb2);

	set<pair<context_index, block_index> > caller_contexts;
	set<context_index> visited_contexts;
	c1.is_caller_context (c4.get_context_id (), caller_contexts, visited_contexts);

	DEBUG ("\nCallers: ");
	set<pair<context_index, block_index> >::iterator cci;
	for (cci = caller_contexts.begin (); cci != caller_contexts.end (); cci++)
	{
		pair<context_index, block_index> caller = *cci;
		DEBUG ("(%d,%d),", caller.first, caller.second);
	}
}

void test37_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;

	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;

	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (2, *n2 ,s1);
	g1.stack->insert_edge (1, *n3 ,s1);
	g1.stack->insert_edge (2, *n3 ,s1);
	g1.stack->insert_edge (3, *n4 ,s1);
	n4->insert_edge (4, *n3 ,s1);

	non_deterministic_simple_graph g2;
	node_index s2 = g2.stack->get_node_id ();
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;

	g2.nodes[n5->get_node_id ()] = n5;
	g2.nodes[n6->get_node_id ()] = n6;
	g2.nodes[n7->get_node_id ()] = n7;

	g2.stack->insert_edge (1, *n5 ,s2);
	g2.stack->insert_edge (2, *n5 ,s2);
	g2.stack->insert_edge (1, *n6 ,s2);
	g2.stack->insert_edge (2, *n6 ,s2);
	g2.stack->insert_edge (3, *n7 ,s2);
	n7->insert_edge (4, *n6 ,s2);

	g1.clean ();
	g2.clean ();

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\nGraph 2\n");
	g2.print_value (NULL);
	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test38_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;

	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;

	g1.stack->insert_edge (1, *n3 ,s1);
	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (2, *n2 ,s1);
	g1.stack->insert_edge (2, *n3 ,s1);
	g1.stack->insert_edge (4, *n4 ,s1);
	n2->insert_edge (3, *n4 ,s1);

	non_deterministic_simple_graph g2;
	node_index s2 = g2.stack->get_node_id ();
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;

	g2.nodes[n5->get_node_id ()] = n5;
	g2.nodes[n6->get_node_id ()] = n6;
	g2.nodes[n7->get_node_id ()] = n7;
	g2.nodes[n8->get_node_id ()] = n8;

	g2.stack->insert_edge (1, *n7 ,s2);
	g2.stack->insert_edge (1, *n6 ,s2);
	g2.stack->insert_edge (2, *n6 ,s2);
	g2.stack->insert_edge (4, *n8 ,s2);
	n6->insert_edge (3, *n8 ,s2);
	n7->insert_edge (3, *n8 ,s2);

	g1.clean ();
	g2.clean ();

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\nGraph 2\n");
	g2.print_value (NULL);
	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test39_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;
	g1.nodes[n7->get_node_id ()] = n7;
	g1.nodes[n8->get_node_id ()] = n8;

	g1.stack->insert_edge (13, *n2 ,s1);
	g1.stack->insert_edge (15, *n3 ,s1);
	n2->insert_edge (0, *n4 ,s1);
	n2->insert_edge (0, *n5 ,s1);
	n3->insert_edge (0, *n5 ,s1);
	n3->insert_edge (0, *n6 ,s1);
	n4->insert_edge (0, *n8 ,s1);
	n5->insert_edge (0, *n7 ,s1);
	n6->insert_edge (0, *n8 ,s1);
	g1.stack->insert_edge (17, *n7 ,s1);
	g1.stack->insert_edge (17, *n8 ,s1);

	g1.clean ();

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nis_node_property_same() -- same graph: ");
	if (g1.stack->is_node_property_same (*n7, *n8, g1.nodes, false))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test40_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;

	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (1, *n3 ,s1);
	g1.stack->insert_edge (3, *n5 ,s1);
	g1.stack->insert_edge (3, *n6 ,s1);
	n2->insert_edge (2, *n2 ,s1);
	n3->insert_edge (1, *n3 ,s1);
	n3->insert_edge (2, *n4 ,s1);
	n4->insert_edge (1, *n3 ,s1);
	n4->insert_edge (1, *n5 ,s1);
	n4->insert_edge (1, *n6 ,s1);
	n5->insert_edge (1, *n3 ,s1);
	n5->insert_edge (2, *n2 ,s1);

	g1.clean ();

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nis_node_property_same() -- same graph: ");
	if (g1.stack->is_node_property_same (*n5, *n6, g1.nodes, false))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test41_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;

	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (1, *n3 ,s1);
	g1.stack->insert_edge (3, *n4 ,s1);
	g1.stack->insert_edge (3, *n5 ,s1);
	n2->insert_edge (1, *n2 ,s1);
	n2->insert_edge (1, *n3 ,s1);
	n3->insert_edge (2, *n2 ,s1);
	n3->insert_edge (2, *n4 ,s1);
	n3->insert_edge (2, *n5 ,s1);
	n4->insert_edge (1, *n2 ,s1);
	n4->insert_edge (1, *n3 ,s1);

	g1.clean ();

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nis_node_property_same() -- same graph: ");
	if (g1.stack->is_node_property_same (*n4, *n5, g1.nodes, false))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test42_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;

	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (1, *n3 ,s1);
	g1.stack->insert_edge (1, *n4 ,s1);
	g1.stack->insert_edge (1, *n6 ,s1);
	g1.stack->insert_edge (2, *n3 ,s1);
	g1.stack->insert_edge (2, *n4 ,s1);
	n2->insert_edge (1, *n2 ,s1);
	n2->insert_edge (1, *n3 ,s1);
	n2->insert_edge (2, *n3 ,s1);
	n2->insert_edge (2, *n4 ,s1);
	n3->insert_edge (2, *n3 ,s1);
	n3->insert_edge (2, *n4 ,s1);
	n3->insert_edge (2, *n5 ,s1);
	n4->insert_edge (1, *n5 ,s1);
	n4->insert_edge (2, *n3 ,s1);
	n4->insert_edge (2, *n4 ,s1);
	n4->insert_edge (2, *n5 ,s1);
	n6->insert_edge (1, *n6 ,s1);

	g1.clean ();

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nis_node_property_same() -- same graph: ");
	if (g1.stack->is_node_property_same (*n2, *n6, g1.nodes, false))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test43_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;

	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (1, *n3 ,s1);
	g1.stack->insert_edge (2, *n3 ,s1);
	g1.stack->insert_edge (4, *n4 ,s1);
	n2->insert_edge (1, *n4 ,s1);
	n2->insert_edge (1, *n2 ,s1);
	n3->insert_edge (1, *n4 ,s1);
	n3->insert_edge (1, *n3 ,s1);

	non_deterministic_simple_graph g2;
	node_index s2 = g2.stack->get_node_id ();
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;

	g2.nodes[n6->get_node_id ()] = n6;
	g2.nodes[n7->get_node_id ()] = n7;
	g2.nodes[n8->get_node_id ()] = n8;

	g2.stack->insert_edge (1, *n6 ,s2);
	g2.stack->insert_edge (1, *n7 ,s2);
	g2.stack->insert_edge (2, *n7 ,s2);
	g2.stack->insert_edge (4, *n8 ,s2);
	n6->insert_edge (1, *n6 ,s2);
	n7->insert_edge (1, *n8 ,s2);
	n7->insert_edge (1, *n7 ,s2);

	g1.clean ();
	g2.clean ();

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\nGraph 2\n");
	g2.print_value (NULL);
	DEBUG ("\n\nis_value_same():");
	// This example gives true for value_property=in,
	// node_property=in_language; this is when equiv_node_pairs are
	// calculated from equiv_state_pairs. For the rest of the cases
	// (value_property=inout) i.e. when equiv_node_pairs are calculated
	// from depth_first_comparison, the result is false.
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test44_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g;
	map<state_index, state_index, state_order> equiv_state_pairs;
	state_index s1;
	state_index s2;
	s1.insert (1);
	s1.insert (2);
	s1.insert (3);
	s2.insert (4);
	s2.insert (5);
	s2.insert (6);
	equiv_state_pairs[s1] = s2;
	equiv_state_pairs[s2] = s1;
	s1.clear ();
	s2.clear ();
	s1.insert (1);
	s1.insert (7);
	s1.insert (8);
	s2.insert (5);
	s2.insert (9);
	s2.insert (10);
	equiv_state_pairs[s1] = s2;
	equiv_state_pairs[s2] = s1;
	s1.clear ();
	s2.clear ();
	s1.insert (7);
	s1.insert (8);
	s2.insert (9);
	s2.insert (10);
	equiv_state_pairs[s1] = s2;
	equiv_state_pairs[s2] = s1;
	s1.clear ();
	s2.clear ();
	s1.insert (7);
	s1.insert (11);
	s2.insert (10);
	s2.insert (12);
	equiv_state_pairs[s1] = s2;
	equiv_state_pairs[s2] = s1;
	s1.clear ();
	s2.clear ();
	s1.insert (2);
	s2.insert (6);
	equiv_state_pairs[s1] = s2;
	equiv_state_pairs[s2] = s1;

	map<state_index, state_index, state_order>::iterator si;
	for (si = equiv_state_pairs.begin (); si != equiv_state_pairs.end (); si++)
	{
		state_index s1 = si->first;
		state_index s2 = si->second;
		state_index::iterator i;
		DEBUG ("({");
		for (i = s1.begin (); i != s1.end (); i++)
			DEBUG ("%d,", *i);
		DEBUG ("},{");
		for (i = s2.begin (); i != s2.end (); i++)
			DEBUG ("%d,", *i);
		DEBUG ("}),");
	}


	map<node_index, node_index> equiv_node_pairs;
	if (g.get_equivalent_nodes (equiv_state_pairs, equiv_node_pairs))
	{
		DEBUG ("found equiv nodes=");
		map<node_index, node_index>::iterator npi;
		for (npi = equiv_node_pairs.begin (); npi != equiv_node_pairs.end (); npi++)
		{
			DEBUG ("(%d,%d),", npi->first, npi->second);
		}
	}
	else
		printf ("cant find equiv nodes");
}

void test45_non_deterministic_simple_graph ()
{
	non_deterministic_simple_node * n1 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n9 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n10 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n11 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n12 = new non_deterministic_simple_node;
	non_deterministic_simple_graph g1;
	non_deterministic_simple_graph g2;
	node_index s1 = g1.stack->get_node_id ();
	node_index s2 = g2.stack->get_node_id ();

	g1.nodes[n1->get_node_id ()] = n1;
	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n7->get_node_id ()] = n7;
	g1.nodes[n8->get_node_id ()] = n8;
	g1.nodes[n11->get_node_id ()] = n11;
	g1.stack->insert_edge (6, *n1 ,s1);
	g1.stack->insert_edge (6, *n2 ,s1);
	g1.stack->insert_edge (6, *n3 ,s1);
	g1.stack->insert_edge (6, *n7 ,s1);
	g1.stack->insert_edge (6, *n8 ,s1);
	g1.stack->insert_edge (6, *n11 ,s1);
	n2->insert_edge (1, *n1 ,s1);
	n2->insert_edge (1, *n2 ,s1);
	n2->insert_edge (1, *n3 ,s1);
	n2->insert_edge (2, *n1 ,s1);
	n2->insert_edge (2, *n7 ,s1);
	n2->insert_edge (2, *n8 ,s1);
	n2->insert_edge (3, *n7 ,s1);
	n2->insert_edge (3, *n8 ,s1);
	n2->insert_edge (4, *n7 ,s1);
	n2->insert_edge (4, *n11 ,s1);
	n2->insert_edge (5, *n2 ,s1);

	g2.nodes[n4->get_node_id ()] = n4;
	g2.nodes[n5->get_node_id ()] = n5;
	g2.nodes[n6->get_node_id ()] = n6;
	g2.nodes[n9->get_node_id ()] = n9;
	g2.nodes[n10->get_node_id ()] = n10;
	g2.nodes[n12->get_node_id ()] = n12;
	g2.stack->insert_edge (6, *n4 ,s2);
	g2.stack->insert_edge (6, *n5 ,s2);
	g2.stack->insert_edge (6, *n6 ,s2);
	g2.stack->insert_edge (6, *n9 ,s2);
	g2.stack->insert_edge (6, *n10 ,s2);
	g2.stack->insert_edge (6, *n12 ,s2);
	n6->insert_edge (1, *n4 ,s2);
	n6->insert_edge (1, *n5 ,s2);
	n6->insert_edge (1, *n6 ,s2);
	n6->insert_edge (2, *n5 ,s2);
	n6->insert_edge (2, *n9 ,s2);
	n6->insert_edge (2, *n10 ,s2);
	n6->insert_edge (3, *n9 ,s2);
	n6->insert_edge (3, *n10 ,s2);
	n6->insert_edge (4, *n10 ,s2);
	n6->insert_edge (4, *n12 ,s2);
	n6->insert_edge (5, *n6 ,s2);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\nGraph 2\n");
	g2.print_value (NULL);
	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test46_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;
	g1.stack->insert_edge (6, *n2 ,s1);
	g1.stack->insert_edge (7, *n5 ,s1);
	n2->insert_edge (1, *n3 ,s1);
	n2->insert_edge (1, *n4 ,s1);
	n2->insert_edge (2, *n6 ,s1);
	n3->insert_edge (1, *n5 ,s1);
	n4->insert_edge (1, *n6 ,s1);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nis_node_property_same():");
	//if (g1.stack->is_node_property_same (*n5, *n6, g1.nodes, false))
	if (g1.stack->is_node_property_same (*n3, *n4, g1.nodes, false))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test47_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;
	g1.nodes[n7->get_node_id ()] = n7;
	g1.nodes[n8->get_node_id ()] = n8;
	g1.stack->insert_edge (6, *n2 ,s1);
	g1.stack->insert_edge (7, *n3 ,s1);
	g1.stack->insert_edge (8, *n7 ,s1);
	g1.stack->insert_edge (8, *n8 ,s1);
	n2->insert_edge (1, *n4 ,s1);
	n2->insert_edge (1, *n5 ,s1);
	n3->insert_edge (1, *n5 ,s1);
	n3->insert_edge (1, *n6 ,s1);
	n4->insert_edge (2, *n7 ,s1);
	n5->insert_edge (2, *n8 ,s1);
	n6->insert_edge (2, *n7 ,s1);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nis_node_property_same():");
	if (g1.stack->is_node_property_same (*n5, *n6, g1.nodes, false))
	//if (g1.stack->is_node_property_same (*n4, *n5, g1.nodes, false))
	//if (g1.stack->is_node_property_same (*n7, *n8, g1.nodes, false))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test48_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_graph g2;
	node_index s2 = g2.stack->get_node_id ();
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n9 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n10 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.stack->insert_edge (6, *n2 ,s1);
	g1.stack->insert_edge (7, *n3 ,s1);
	g1.stack->insert_edge (8, *n4 ,s1);
	g1.stack->insert_edge (8, *n5 ,s1);
	n2->insert_edge (1, *n4 ,s1);
	n2->insert_edge (1, *n5 ,s1);
	n3->insert_edge (1, *n5 ,s1);

	g2.nodes[n7->get_node_id ()] = n7;
	g2.nodes[n8->get_node_id ()] = n8;
	g2.nodes[n9->get_node_id ()] = n9;
	g2.nodes[n10->get_node_id ()] = n10;
	g2.stack->insert_edge (6, *n7 ,s2);
	g2.stack->insert_edge (7, *n8 ,s2);
	g2.stack->insert_edge (8, *n9 ,s2);
	g2.stack->insert_edge (8, *n10 ,s2);
	n7->insert_edge (1, *n9 ,s2);
	n7->insert_edge (1, *n10 ,s2);
	n8->insert_edge (1, *n9 ,s2);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\nGraph 2\n");
	g2.print_value (NULL);
	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test49_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_graph g2;
	node_index s2 = g2.stack->get_node_id ();
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (1, *n4 ,s1);
	g1.stack->insert_edge (2, *n2 ,s1);
	g1.stack->insert_edge (2, *n3 ,s1);
	g1.stack->insert_edge (3, *n3 ,s1);
	g1.stack->insert_edge (3, *n4 ,s1);
	g1.stack->insert_edge (4, *n2 ,s1);
	g1.stack->insert_edge (4, *n3 ,s1);
	g1.stack->insert_edge (4, *n4 ,s1);

	g2.nodes[n6->get_node_id ()] = n6;
	g2.nodes[n7->get_node_id ()] = n7;
	g2.nodes[n8->get_node_id ()] = n8;
	g2.stack->insert_edge (1, *n6 ,s2);
	g2.stack->insert_edge (2, *n7 ,s2);
	g2.stack->insert_edge (2, *n8 ,s2);
	g2.stack->insert_edge (3, *n8 ,s2);
	g2.stack->insert_edge (4, *n6 ,s2);
	g2.stack->insert_edge (4, *n7 ,s2);
	g2.stack->insert_edge (4, *n8 ,s2);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\nGraph 2\n");
	g2.print_value (NULL);
	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test50_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_graph g2;
	node_index s2 = g2.stack->get_node_id ();
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (2, *n2 ,s1);
	g1.stack->insert_edge (3, *n3 ,s1);
	g1.stack->insert_edge (4, *n2 ,s1);
	g1.stack->insert_edge (4, *n3 ,s1);
	n3->insert_edge (5, *n2 ,s1);

	g2.nodes[n5->get_node_id ()] = n5;
	g2.nodes[n6->get_node_id ()] = n6;
	g2.nodes[n7->get_node_id ()] = n7;
	g2.stack->insert_edge (1, *n5 ,s2);
	g2.stack->insert_edge (2, *n6 ,s2);
	g2.stack->insert_edge (3, *n7 ,s2);
	g2.stack->insert_edge (4, *n5 ,s2);
	g2.stack->insert_edge (4, *n6 ,s2);
	g2.stack->insert_edge (4, *n7 ,s2);
	n7->insert_edge (5, *n6 ,s2);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\nGraph 2\n");
	g2.print_value (NULL);
	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test51_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_graph g2;
	node_index s2 = g2.stack->get_node_id ();
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n7 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n8 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (1, *n3 ,s1);
	g1.stack->insert_edge (2, *n2 ,s1);
	g1.stack->insert_edge (4, *n4 ,s1);
	n2->insert_edge (3, *n4 ,s1);

	g2.nodes[n6->get_node_id ()] = n6;
	g2.nodes[n7->get_node_id ()] = n7;
	g2.nodes[n8->get_node_id ()] = n8;
	g2.stack->insert_edge (1, *n7 ,s2);
	g2.stack->insert_edge (2, *n6 ,s2);
	g2.stack->insert_edge (4, *n8 ,s2);
	n6->insert_edge (3, *n8 ,s2);
	n7->insert_edge (3, *n8 ,s2);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\nGraph 2\n");
	g2.print_value (NULL);
	DEBUG ("\n\nis_value_same():");
	if (g1.is_value_same (g2))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
	DEBUG ("\n\nis_node_property_same() -- same graph: ");
	map<state_index, state_index, state_order> equiv_state_pairs;
	if (g1.get_equivalent_states (g2, equiv_state_pairs))
		DEBUG ("\nequiv_state_pairs found");
	{
		if (n4->is_node_property_same (*n8, g1.nodes, g2.nodes, equiv_state_pairs, 0))
			DEBUG ("\nTRUE");
		else
			DEBUG ("\nFALSE");
	}

}

void test52_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (1, *n3 ,s1);
	g1.stack->insert_edge (2, *n3 ,s1);
	g1.stack->insert_edge (4, *n4 ,s1);
	g1.stack->insert_edge (4, *n5 ,s1);
	n2->insert_edge (3, *n4 ,s1);
	n3->insert_edge (3, *n4 ,s1);
	n3->insert_edge (3, *n5 ,s1);

	DEBUG ("\nGraph 1\n");
	g1.print_value (NULL);
	DEBUG ("\n\nis_node_property_same():");
	if (g1.stack->is_node_property_same (*n4, *n5, g1.nodes, false))
		DEBUG ("TRUE");
	else
		DEBUG ("FALSE");
}

void test53_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (2, *n3 ,s1);
	g1.stack->insert_edge (3, *n4 ,s1);
	g1.stack->insert_edge (3, *n5 ,s1);
	n2->insert_edge (13, *n4 ,s1);
	n3->insert_edge (13, *n5 ,s1);

	RESULT ("\nCompact graph:");
	non_deterministic_simple_graph * compact_g = 
		g1.get_compact_graph ();
	compact_g->print_value (NULL);
	map<label, set<label> > compact_root_aliases;
	compact_g->get_root_aliases (compact_root_aliases, compact_root_aliases);
	compact_g->print_root_aliases (compact_root_aliases);
	RESULT ("\nOur graph:");
	map<label, set<label> > our_root_aliases;
	g1.get_root_aliases (our_root_aliases, our_root_aliases);
	g1.print_root_aliases (our_root_aliases);
}

void test54_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;
	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (2, *n5 ,s1);
	g1.stack->insert_edge (3, *n3 ,s1);
	g1.stack->insert_edge (3, *n6 ,s1);
	g1.stack->insert_edge (4, *n4 ,s1);
	n2->insert_edge (13, *n3 ,s1);
	n3->insert_edge (13, *n4 ,s1);
	n5->insert_edge (13, *n6 ,s1);

	RESULT ("\nCompact graph:");
	non_deterministic_simple_graph * compact_g = 
		g1.get_compact_graph ();
	compact_g->print_value (NULL);
	map<label, set<label> > compact_root_aliases;
	compact_g->get_root_aliases (compact_root_aliases, compact_root_aliases);
	compact_g->print_root_aliases (compact_root_aliases);
	RESULT ("\nOur graph:");
	g1.print_value (NULL);
	map<label, set<label> > our_root_aliases;
	g1.get_root_aliases (our_root_aliases, our_root_aliases);
	g1.print_root_aliases (our_root_aliases);
}

void test55_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n6 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.nodes[n6->get_node_id ()] = n6;
	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (2, *n3 ,s1);
	g1.stack->insert_edge (3, *n4 ,s1);
	g1.stack->insert_edge (4, *n5 ,s1);
	g1.stack->insert_edge (4, *n6 ,s1);
	n2->insert_edge (15, *n5 ,s1);
	n2->insert_edge (17, *n6 ,s1);
	n3->insert_edge (13, *n5 ,s1);
	n4->insert_edge (13, *n6 ,s1);

	RESULT ("\nCompact graph:");
	non_deterministic_simple_graph * compact_g = 
		g1.get_compact_graph ();
	compact_g->print_value (NULL);
	map<label, set<label> > compact_root_aliases;
	compact_g->get_root_aliases (compact_root_aliases, compact_root_aliases);
	compact_g->print_root_aliases (compact_root_aliases);
	RESULT ("\nOur graph:");
	g1.print_value (NULL);
	map<label, set<label> > our_root_aliases;
	g1.get_root_aliases (our_root_aliases, our_root_aliases);
	g1.print_root_aliases (our_root_aliases);
}

void test56_non_deterministic_simple_graph ()
{
	non_deterministic_simple_graph g1;
	node_index s1 = g1.stack->get_node_id ();
	non_deterministic_simple_node * n2 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n3 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n4 = new non_deterministic_simple_node;
	non_deterministic_simple_node * n5 = new non_deterministic_simple_node;

	g1.nodes[n2->get_node_id ()] = n2;
	g1.nodes[n3->get_node_id ()] = n3;
	g1.nodes[n4->get_node_id ()] = n4;
	g1.nodes[n5->get_node_id ()] = n5;
	g1.stack->insert_edge (1, *n2 ,s1);
	g1.stack->insert_edge (2, *n3 ,s1);
	g1.stack->insert_edge (3, *n4 ,s1);
	g1.stack->insert_edge (4, *n5 ,s1);
	n2->insert_edge (13, *n3 ,s1);
	n2->insert_edge (13, *n4 ,s1);
	n3->insert_edge (13, *n5 ,s1);

	RESULT ("\nCompact graph:");
	non_deterministic_simple_graph * compact_g = 
		g1.get_compact_graph ();
	compact_g->print_value (NULL);
	map<label, set<label> > compact_root_aliases;
	compact_g->get_root_aliases (compact_root_aliases, compact_root_aliases);
	compact_g->print_root_aliases (compact_root_aliases);
	RESULT ("\nOur graph:");
	g1.print_value (NULL);
	map<label, set<label> > our_root_aliases;
	g1.get_root_aliases (our_root_aliases, our_root_aliases);
	g1.print_root_aliases (our_root_aliases);
}

void test_bb_order ()
{
	points_to_analysis_simple pta_s;
	// Preprocess the control flow graph and parse the program
	pta_s.preprocess_and_parse_program ();
	DEBUG ("\nPreprocessing and parsing done\n");

	for (struct cgraph_node * cnode = cgraph_nodes; cnode; cnode = cnode->next)
	{
		/* Nodes without a body, and clone nodes are not interesting. */
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;
		set_cfun (DECL_STRUCT_FUNCTION (cnode->decl));

		int number_of_blocks = n_basic_blocks - NUM_FIXED_BLOCKS;
		DEBUG ("\nnumber_of_blocks=%d", number_of_blocks);
		DEBUG ("\nrev_post_order: ");
		int * rev_post_order = XNEWVEC (int, number_of_blocks);
		pre_and_rev_post_order_compute (NULL, rev_post_order, false);
		for (int i = 0; i < number_of_blocks; i++)
		{
			basic_block bb = BASIC_BLOCK (rev_post_order[i]);
			DEBUG ("(bb=%d,rp=%d),", bb->index, i);
		}
		DEBUG ("\npost_order: ");
		for (int i = 0; i < number_of_blocks; i++)
		{
			basic_block bb = BASIC_BLOCK (rev_post_order[i]);
			DEBUG ("(bb=%d,p=%d),", bb->index, number_of_blocks - i - 1);
		}

	}
	program.delete_block_aux ();
	// pta_s.restore_control_flow_graph ();
}

//static stack<gimple> 
//get_gimple_stmt ()
//{
//	stack<gimple> ds;
//	for (struct cgraph_node * cnode = cgraph_nodes; cnode; cnode = cnode->next)
//        {
//                // Nodes without a body, and clone nodes are not interesting.
//                if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
//                        continue;
//
//                push_cfun (DECL_STRUCT_FUNCTION (cnode->decl));
//		const char * fname = cgraph_node_name (cnode);
//		DEBUG ("\nfname=%s", fname);
//		basic_block bb;
//		FOR_EACH_BB (bb)
//		{
//			for (gimple_stmt_iterator gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
//			{
//				gimple s = gsi_stmt (gsi);
//				ds.push (s);
//				DEBUG ("\nstmt bb=%d", gimple_bb (s)->index);
//			}
//		}
//		pop_cfun ();
//	}
//	return ds;
//}

static stack<def_stmt>
get_gimple_stmt ()
{
	stack<def_stmt> ds;
	struct cgraph_node * cnode = NULL;
	for (cnode = cgraph_nodes; cnode; cnode = cnode->next)
	{
		// Nodes without a body, and clone nodes are not interesting.
		if (!gimple_has_body_p (cnode->decl) || cnode->clone_of)
			continue;

		push_cfun(DECL_STRUCT_FUNCTION (cnode->decl));

		basic_block current_block;
		FOR_EACH_BB (current_block)
		{
			list<pair<unsigned int, bool> > parsed_data_indices =
				((block_information *)(current_block->aux))->
					get_parsed_data_indices ();

			list<pair<unsigned int, bool> >::iterator it;
			for (it = parsed_data_indices.begin (); it != parsed_data_indices.end (); it++)
			{
				unsigned int index = (*it).first;
				bool is_assignment = (*it).second;

				if (is_assignment)
					ds.push (index);
			}
		}

		pop_cfun();
	}
	return ds;
}

void test1_ap_fi_graph ()
{
#if SUMM_STMT_CLOSURE
	ap_fi_graph g;
	ap_fi_node * n1 = new ap_fi_node (g.nodes);
	ap_fi_node * n2 = new ap_fi_node (g.nodes);
	ap_fi_node * n3 = new ap_fi_node (g.nodes);
	ap_fi_node * n4 = new ap_fi_node (g.nodes);
	ap_fi_node * n5 = new ap_fi_node (g.nodes);
	ap_fi_node * n6 = new ap_fi_node (g.nodes);
	ap_fi_node * n7 = new ap_fi_node (g.nodes);
	ap_fi_node * n8 = new ap_fi_node (g.nodes);
	ap_fi_node * n9 = new ap_fi_node (g.nodes);
	ap_fi_node * n10 = new ap_fi_node (g.nodes);

	stack<def_stmt> ds_all = get_gimple_stmt ();
	def_stmt s1,s2,s3,s4,s5,s6;
	s1 = ds_all.top (); ds_all.pop ();
	s2 = ds_all.top (); ds_all.pop ();
	s3 = ds_all.top (); ds_all.pop ();
	s4 = ds_all.top (); ds_all.pop ();
	s5 = ds_all.top (); ds_all.pop ();

	set<def_stmt> ds;
	ds.insert (s1); ds.insert (s2); 
	n1->insert_edge (13, s1, *n2); 
	n1->insert_edge (13, s2, *n2); 
	ds.clear (); ds.insert (s3); 
	node_index n11_id, n12_id;
	bool n11_unbounded, n12_unbounded;
	g.update (n2->get_node_id (), 13, ds, n11_id, n11_unbounded); 
	ap_fi_node * n11 = g.nodes[n11_id];
	ds.clear (); ds.insert (s2); 
	g.update (n2->get_node_id (), 15, ds, n12_id, n12_unbounded); 
	ap_fi_node * n12 = g.nodes[n12_id];
	ds.clear (); ds.insert (s4); 
	ap_node_index anid;
	bool ap_unbounded;
	g.update (n12->get_node_id (), 15, ds, anid, ap_unbounded); 
	ds.clear (); ds.insert (s1);
	g.update (n11->get_node_id (), 13, ds, anid, ap_unbounded); 
	ds.clear (); ds.insert (s4); 
	g.update (n11->get_node_id (), 13, ds, anid, ap_unbounded); 
	// Additional edge with repeating label,id -- not added
	ds.clear (); ds.insert (s3); 
	g.update (n11->get_node_id (), 13, ds, anid, ap_unbounded); 
	// Additional edge with non-repeating label -- added
	ds.clear (); ds.insert (s5); 
	g.update (n11->get_node_id (), 13, ds, anid, ap_unbounded); 

#ifdef DOT_FILE
	FILE * file = fopen (DOT_FILE, "w");
	fprintf (file, "\n");
	fclose (file);
	file = fopen (DOT_FILE, "a");
	g.print_graph (file);
	fclose (file);
#endif
#endif
}

void test1_pt_fi_graph ()
{
	pt_fi_graph g;
	set<node_index> vnodes, rnodes, tnodes, tfnodes, tfptrnodes, 
		rfnodes, rfptrnodes, heapnodes, heapfnodes;
	// Works on a program which has the following variable ids in parser --
	// test31m.c
	label t=29,v=8,r=9,heap=65;
	// program.print_variable_data ();
	set<node_index>::iterator ni;

	g.generate_addressof_nodes (r, rnodes);
	g.generate_addressof_nodes (t, tnodes);		// API	
		// calls generate_addressof_field_nodes()		// API
	g.insert_edges (rnodes, tnodes, ASTERISK);

	list<label> fs;
	fs.push_back (32);

//	g.generate_addressof_nodes (heap, heapnodes);
//	g.insert_edges (rnodes, heapnodes, ASTERISK);			// API
	// on-the-fly heap fields
//	g.generate_pointer_nodes (r, &fs, heapfnodes); 			// API
		// calls generate_field_nodes() which calls 		// API
		// generate_heap_field_nodes() which in turn calls 	// API
		// generate_addressof_nodes()				// API

	set<pt_node_index> empty_nodes;
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
	g.get_field_nodes (tnodes, 32, tfnodes, empty_nodes, empty_edges, empty_edges);			// API
	g.generate_addressof_nodes (v, vnodes);
	g.insert_edges (tfnodes, vnodes, ASTERISK);
	g.get_pointer_nodes (r, &fs, rfnodes, empty_nodes, empty_edges, empty_edges);
	RESULT ("\nrfnodes=");
	for (ni = rfnodes.begin (); ni != rfnodes.end (); ni++)
		RESULT ("%d,", *ni);
	g.generate_deref_nodes (r, &fs, rfptrnodes, empty_nodes, empty_edges, empty_edges); // API
	RESULT ("\nrfptrnodes=");
	for (ni = rfptrnodes.begin (); ni != rfptrnodes.end (); ni++)
		RESULT ("%d,", *ni);
	g.get_deref_nodes (r, &fs, rfptrnodes, empty_nodes, empty_edges, empty_edges);	// API
		// get nodes that are generated.
	RESULT ("\nrfptrnodes=");
	for (ni = rfptrnodes.begin (); ni != rfptrnodes.end (); ni++)
		RESULT ("%d,", *ni);

	rfptrnodes.clear ();
//	get_must_pointer_nodes (r, &fs, rfptrnodes);			// API
//	RESULT ("\nrfptrnodes=");
//	for (ni = rfptrnodes.begin (); ni != rfptrnodes.end (); ni++)
//		RESULT ("%d,", *ni);


#ifdef DOT_FILE
	FILE * file = fopen (DOT_FILE, "w");
	fprintf (file, "\n");
	fclose (file);
	file = fopen (DOT_FILE, "a");
	g.print_graph (file);						// API
	fclose (file);
#endif
}

static void my_update_ap (set<pt_node_index> & pt_n_proc, 
	set<pt_node_index> & lptr, 
	set<pt_node_index> & must_lptr, 
	label l, 
	def_stmt_set ds, 
	set<pt_node_index> & rptr,
	pt_fi_graph & g_pt, 
	ap_fi_graph & g_ap,
	pt_access_fi_map & pt_access_map)
{
	set<pt_node_index> nodes;
	map<node_index, pt_fi_node *>::iterator gni;
	for (gni = g_pt.nodes.begin (); gni != g_pt.nodes.end (); gni++)
		nodes.insert (gni->first);
	pt_node_set value_in;
	value_in.pt_nodes = nodes;
	set<pt_node_index> s;
	map<pt_node_index, access_name> new_access_name = 
		pt_access_map.pt_to_access_name;
	map<pt_node_index, pt_node_index> summ_cmpts_map;

	points_to_analysis_fi pta_fi (true);
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
	set<pt_node_index> ext_bndry;	// Call get_reachable_nodes() and get_ext_bndry_nodes()
	pta_fi.pull_new_an (pt_n_proc, ext_bndry, value_in, lptr, must_lptr, l, ds, rptr, empty_edges,
		summ_cmpts_map, new_access_name);	// API
	map<pt_node_index, pt_node_index> clone;
	set<pt_node_index>::iterator ni;
	for (ni = pt_n_proc.begin (); ni != pt_n_proc.end (); ni++)
		clone[*ni] = *ni;
	// pt_access_map.set_access_name (pt_n_proc, clone, new_access_name);	// API

	// Breadth-first traversal
	set<pt_node_index> succ_nodes;
	for (ni = pt_n_proc.begin (); ni != pt_n_proc.end (); ni++)
	{
		pt_fi_node * n = g_pt.nodes[*ni];
		map<label, set<pt_node_index> > out_e = n->get_out_edge_list ();
		map<label, set<pt_node_index> >::iterator ei;
		for (ei = out_e.begin (); ei != out_e.end (); ei++)
			succ_nodes.insert (ei->second.begin (), ei->second.end ());
	}

	if (succ_nodes.size ())
		my_update_ap (succ_nodes, lptr, must_lptr, l, ds, rptr, g_pt, g_ap, pt_access_map);
}

void test1_pt_access_fi_map ()
{
	pt_fi_graph g_pt;
	ap_fi_graph g_ap;
	pt_access_fi_map pt_access_map (g_pt, g_ap);
	RESULT ("\nInitial map=");
	pt_access_map.print_map (NULL, NULL);

	set<node_index> vnodes, rnodes, tnodes, tfnodes, tfptrnodes, 
		rfnodes, rfptrnodes, heapnodes, heapfnodes;
	// Works on a program which has the following variable ids in parser --
	// test31m.c
	label t=29,v=8,r=9,heap=65;
	// program.print_variable_data ();

	set<pt_node_index> empty_set;
	def_stmt_set ds;
	ds.insert (0);

	g_pt.generate_addressof_nodes (r, rnodes);
	// pt_access_map.init_ap_of_stack_var_from_root (rnodes, g_pt, g_ap);
	g_pt.generate_addressof_nodes (t, tnodes);			
	// pt_access_map.init_ap_of_stack_var_from_root (tnodes, g_pt, g_ap);
	g_pt.insert_edges (rnodes, tnodes, ASTERISK);
	my_update_ap (tnodes, rnodes, empty_set, ASTERISK, ds, tnodes, g_pt, g_ap, pt_access_map); 

	list<label> fs;
	fs.push_back (32);

	g_pt.generate_addressof_nodes (heap, heapnodes);
	// pt_access_map.init_ap_of_stack_var_from_root (heapnodes, g_pt, g_ap);
	g_pt.insert_edges (rnodes, heapnodes, ASTERISK);			
	my_update_ap (heapnodes, rnodes, empty_set, ASTERISK, ds, heapnodes, g_pt, g_ap, pt_access_map); 

	// generate_pointer_nodes (r, &fs, heapfnodes); 			

	set<pt_node_index> empty_nodes;
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
	g_pt.get_field_nodes (tnodes, 32, tfnodes, empty_nodes, empty_edges, empty_edges);			
	g_pt.generate_addressof_nodes (v, vnodes);
	// pt_access_map.init_ap_of_stack_var_from_root (vnodes, g_pt, g_ap);
	g_pt.insert_edges (tfnodes, vnodes, ASTERISK);
	my_update_ap (vnodes, tfnodes, empty_set, ASTERISK, ds, vnodes, g_pt, g_ap, pt_access_map); 

	g_pt.generate_deref_nodes (r, &fs, rfptrnodes, empty_nodes, empty_edges, empty_edges);			

#ifdef DOT_FILE
	FILE * file = fopen (DOT_FILE, "w");
	fprintf (file, "\n");
	fclose (file);
	file = fopen (DOT_FILE, "a");
	g_pt.print_graph (file);

	set<pt_node_index> nodes;
	map<node_index, pt_fi_node *>::iterator gni;
	for (gni = g_pt.nodes.begin (); gni != g_pt.nodes.end (); gni++)
		nodes.insert (gni->first);
//	my_update_ap (nodes, empty_set, empty_set, 0, ds, empty_set, g_pt, g_ap, pt_access_map);

	pt_access_map.print_map (NULL, NULL);
	g_ap.print_graph (file);

	fclose (file);
#endif
}

void test1_points_to_analysis_fi ()
{
	pt_fi_graph g_pt;
	ap_fi_graph g_ap;
	pt_access_fi_map pt_access_map (g_pt, g_ap);
	RESULT ("\nInitial map=");
	pt_access_map.print_map (NULL, NULL);

	set<node_index> vnodes, rnodes, tnodes, tfnodes, tfptrnodes, 
		rfnodes, rfptrnodes, heapnodes, heapfnodes;
	// Works on a program which has the following variable ids in parser --
	// test31m.c
	label t=29,v=8,r=9,heap=65;
	// program.print_variable_data ();

	set<pt_node_index> empty_set;
	def_stmt_set ds;
	ds.insert (0);

	g_pt.generate_addressof_nodes (r, rnodes);
	g_pt.generate_addressof_nodes (t, tnodes);			

	set<pt_node_index> nodes;
	map<node_index, pt_fi_node *>::iterator gni;
	for (gni = g_pt.nodes.begin (); gni != g_pt.nodes.end (); gni++)
		nodes.insert (gni->first);
	my_update_ap (nodes, empty_set, empty_set, 0, ds, empty_set, g_pt, g_ap, pt_access_map);

	g_pt.insert_edges (rnodes, tnodes, ASTERISK);

	/*******************************************************************************************/
	points_to_analysis_fi pta_fi (true);
	pta_fi.g_pt = g_pt;
	pta_fi.g_ap = g_ap;
	pta_fi.pt_access_map = pt_access_map;
	pt_node_set value_in;
	value_in.pt_nodes = nodes;
	map<pt_node_index, access_name> new_pt_to_access_name = pt_access_map.pt_to_access_name;
	map<pt_node_index, max_depth> new_pt_to_max_depth;
	map<pt_node_index, pt_node_index> summ_cmpts_map;
#if SUMM_K_CONSISTENT
	new_pt_to_max_depth = pt_access_map.pt_to_max_depth;
#endif
	set<pt_node_index> affected_nodes;
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
	affected_nodes = pta_fi.find_new_ans_and_affected_region (tnodes, value_in, 
		rfnodes, empty_set, ASTERISK, ds, tnodes, empty_edges, empty_edges,
		new_pt_to_max_depth, summ_cmpts_map, new_pt_to_access_name);

	RESULT ("\nAffected nodes=");
	set<pt_node_index>::iterator ni;
	for (ni = affected_nodes.begin (); ni != affected_nodes.end (); ni++)
		RESULT ("%d,", *ni);
	g_ap = pta_fi.g_ap;
	/*******************************************************************************************/

#ifdef DOT_FILE
	FILE * file = fopen (DOT_FILE, "w");
	fprintf (file, "\n");
	fclose (file);
	file = fopen (DOT_FILE, "a");
	g_pt.print_graph (file);

	pt_access_map.print_map (NULL, NULL);
	g_ap.print_graph (file);

	fclose (file);
#endif
}

void test2_points_to_analysis_fi ()
{
	pt_fi_graph g_pt;
	ap_fi_graph g_ap;
	pt_access_fi_map pt_access_map (g_pt, g_ap);
	RESULT ("\nInitial map=");
	pt_access_map.print_map (NULL, NULL);

	set<pt_node_index> vnodes, rnodes, tnodes, tfnodes, tfptrnodes, tdupnodes,
		rfnodes, rfptrnodes, heapnodes, heapfnodes;
	// Works on a program which has the following variable ids in parser --
	// test31m.c
	//label t=29,v=8,r=9,heap=65;
	label r=7,heap=56;	// with in-line malloc in main()
	// program.print_variable_data ();

	set<pt_node_index> empty_set;
	def_stmt_set ds;
	ds.insert (0);

	g_pt.generate_addressof_nodes (r, rnodes);
	g_pt.generate_addressof_nodes (heap, tnodes);			
	RESULT ("\nt node = %d", *(tnodes.begin ()));
	g_pt.insert_edges (rnodes, tnodes, ASTERISK);
	g_pt.generate_addressof_nodes (heap, tdupnodes);
	RESULT ("\ndup t node = %d", *(tdupnodes.begin ()));

	set<pt_node_index> nodes;
	map<node_index, pt_fi_node *>::iterator gni;
	RESULT ("\nNodes=");
	for (gni = g_pt.nodes.begin (); gni != g_pt.nodes.end (); gni++)
	{
		nodes.insert (gni->first);
		RESULT ("%d,", gni->first);
	}
	RESULT ("\nmy_update_ap");
	my_update_ap (nodes, empty_set, empty_set, 0, ds, empty_set, g_pt, g_ap, pt_access_map);


	/*******************************************************************************************/
	points_to_analysis_fi pta_fi (true);
	pta_fi.g_pt = g_pt;
	pta_fi.g_ap = g_ap;
	pta_fi.pt_access_map = pt_access_map;
	pt_node_set value_in;
	value_in.pt_nodes = nodes;
	map<pt_node_index, access_name> new_pt_to_access_name = 
		pt_access_map.pt_to_access_name;
	map<pt_node_index, max_depth> new_pt_to_max_depth;
	map<pt_node_index, pt_node_index> summ_cmpts_map;
#if SUMM_K_CONSISTENT
	new_pt_to_max_depth = pt_access_map.pt_to_max_depth;
#endif
	set<pt_node_index> affected_nodes;
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;

	map<pt_node_index, pt_node_index> clone_map = 
		pta_fi.clone_nodes (value_in, 
			rnodes, empty_set, ASTERISK, ds, tdupnodes, empty_edges, empty_edges,
			new_pt_to_max_depth, summ_cmpts_map, new_pt_to_access_name, affected_nodes);

	RESULT ("\nAffected nodes=");
	set<pt_node_index>::iterator ni;
	for (ni = affected_nodes.begin (); ni != affected_nodes.end (); ni++)
		RESULT ("%d,", *ni);

	RESULT ("\nClone map=");
	map<pt_node_index, pt_node_index>::iterator mi;
	for (mi = clone_map.begin (); mi != clone_map.end (); mi++)
		RESULT ("(%d,%d), ", mi->first, mi->second);

	g_ap = pta_fi.g_ap;
	/*******************************************************************************************/

#ifdef DOT_FILE
	FILE * file = fopen (DOT_FILE, "w");
	fprintf (file, "\n");
	fclose (file);
	file = fopen (DOT_FILE, "a");
	g_pt.print_graph (file);

	pt_access_map.print_map (NULL, NULL);
	g_ap.print_graph (file);

	fclose (file);
#endif
}

void test3_points_to_analysis_fi ()
{
	points_to_analysis_fi pta_fi (true);
	pt_access_fi_map pt_access_map (pta_fi.g_pt, pta_fi.g_ap);
	pta_fi.pt_access_map = pt_access_map;

	RESULT ("\nInitial map=");
	pt_access_map.print_map (NULL, NULL);

	set<pt_node_index> vnodes, rnodes, tnodes, tfnodes, tfptrnodes, tdupnodes,
		rfnodes, rfptrnodes, heapnodes, heapfnodes;
	// Works on a program which has the following variable ids in parser --
	// test31m.c
	label t=29,v=8,r=9,heap=65;
	// program.print_variable_data ();

	set<pt_node_index> empty_set;
	def_stmt_set ds;
	ds.insert (-1);

	pta_fi.g_pt.generate_addressof_nodes (r, rnodes);
	pta_fi.g_pt.generate_addressof_nodes (t, tnodes);			
	RESULT ("\nt node = %d", *(tnodes.begin ()));
//	pta_fi.g_pt.insert_edges (rnodes, tnodes, ASTERISK);

	set<pt_node_index> nodes;
	map<node_index, pt_fi_node *>::iterator gni;
	RESULT ("\nNodes=");
	for (gni = pta_fi.g_pt.nodes.begin (); gni != pta_fi.g_pt.nodes.end (); gni++)
	{
		nodes.insert (gni->first);
		RESULT ("%d,", gni->first);
	}
	RESULT ("\nmy_update_ap");
	my_update_ap (nodes, empty_set, empty_set, 0, ds, empty_set, 
		pta_fi.g_pt, pta_fi.g_ap, pta_fi.pt_access_map);


	/*******************************************************************************************/
	pt_node_set value_in;
	value_in.pt_nodes = nodes;
	set<pt_node_index> ngen;
	set<pt_node_index> nkill;
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
	map<pt_node_index, pt_node_index> clone;

	pta_fi.clone_and_update_subgraph (value_in, 
		rnodes, empty_set, ASTERISK, ds, tnodes, empty_edges, empty_edges, clone);

	RESULT ("\nngen=");
	set<pt_node_index>::iterator ni;
	for (ni = ngen.begin (); ni != ngen.end (); ni++)
		RESULT ("%d,", *ni);

	RESULT ("\nnkill=");
	for (ni = nkill.begin (); ni != nkill.end (); ni++)
		RESULT ("%d,", *ni);

	/*******************************************************************************************/

#ifdef DOT_FILE
	FILE * file = fopen (DOT_FILE, "w");
	fprintf (file, "\n");
	fclose (file);
	file = fopen (DOT_FILE, "a");
	pta_fi.g_pt.print_graph (file);

	pta_fi.pt_access_map.print_map (NULL, NULL);
	pta_fi.g_ap.print_graph (file);

	fclose (file);
#endif
}

void test1_points_to_analysis_fi_region ()
{
	pt_fi_graph g_pt;

	set<pt_node_index> n1, n2, n3, n4, n5, n6, n7, n8, n9;
	label l1=12, l2=4, l3=5, l4=6, l5=7, l6=8, l7=9, l8=10, l9=11;

	g_pt.generate_addressof_nodes (l1, n1);
	g_pt.generate_addressof_nodes (l2, n2);
	g_pt.generate_addressof_nodes (l3, n3);
	g_pt.generate_addressof_nodes (l4, n4);
	g_pt.generate_addressof_nodes (l5, n5);
	g_pt.generate_addressof_nodes (l6, n6);
	g_pt.generate_addressof_nodes (l7, n7);
	g_pt.generate_addressof_nodes (l8, n8);
	g_pt.generate_addressof_nodes (l9, n9);
	g_pt.insert_edges (n1, n5, ASTERISK);
	g_pt.insert_edges (n2, n6, ASTERISK);
	g_pt.insert_edges (n3, n6, ASTERISK);
	g_pt.insert_edges (n4, n5, ASTERISK);
	g_pt.insert_edges (n5, n8, ASTERISK);
	g_pt.insert_edges (n6, n8, ASTERISK);
	g_pt.insert_edges (n6, n9, ASTERISK);
	g_pt.insert_edges (n7, n8, ASTERISK);

	set<pt_node_index> value;
	value.insert (g_pt.stack.get_node_id ());
	value.insert (n1.begin (), n1.end ());
	value.insert (n2.begin (), n2.end ());
	value.insert (n3.begin (), n3.end ());
	value.insert (n4.begin (), n4.end ());
	value.insert (n5.begin (), n5.end ());
	value.insert (n6.begin (), n6.end ());
	value.insert (n7.begin (), n7.end ());
	value.insert (n8.begin (), n8.end ());
	value.insert (n9.begin (), n9.end ());

	set<pt_node_index> nvisit;
	nvisit.insert (n2.begin (), n2.end ());
	nvisit.insert (n5.begin (), n5.end ());
	nvisit.insert (n8.begin (), n8.end ());

	label l = 0;
	set<pt_node_index> nreach;
	set<pt_node_index> lptr, rpte, must_lptr;
	map<pt_node_index, map<label, set<pt_node_index> > > incl_in_edges;
	map<pt_node_index, map<label, set<pt_node_index> > > incl_out_edges;
	nreach = g_pt.get_reachable_nodes (nvisit, 
		lptr, rpte, incl_in_edges, incl_out_edges, value);

	set<pt_node_index> ext_bndry;
	ext_bndry = g_pt.get_ext_bndry_nodes (nreach, 
		lptr, must_lptr, l, rpte, incl_in_edges, incl_out_edges, value); 

	g_pt.print_graph (NULL);

	set<pt_node_index>::iterator ni;
	RESULT ("\nnvisit=");
	for (ni = nvisit.begin (); ni != nvisit.end (); ni++)
		RESULT ("%d,", *ni);
	RESULT ("\nnreach=");
	for (ni = nreach.begin (); ni != nreach.end (); ni++)
		RESULT ("%d,", *ni);
	RESULT ("\next_bndry=");
	for (ni = ext_bndry.begin (); ni != ext_bndry.end (); ni++)
		RESULT ("%d,", *ni);
}

void test1_points_to_analysis_fi_len ()
{
	// test45.c

	// struct node p1, p2, p3, p4, *x1, *y1; 
	// int main () 
	// { 
	//      x1 = &p1; 
	//      x1= &p2; 
	//      x1= &p3; 
	//      y1 = &p4; 
	// }

/*
	points_to_analysis_fi pta_fi;

	set<pt_node_index> n56, n57, n59, n61, n62, n64, n71, n74, n76;
	label l56=25, l57=26, l59=16, l61=18, l62=12, l64=14, l71=10, l74=6, l76=8;

	pta_fi.g_pt.generate_addressof_nodes (l56, n56);
	pta_fi.g_pt.generate_addressof_nodes (l57, n57);
	pta_fi.g_pt.generate_addressof_nodes (l59, n59);
	pta_fi.g_pt.generate_addressof_nodes (l61, n61);
	pta_fi.g_pt.generate_addressof_nodes (l62, n62);
	pta_fi.g_pt.generate_addressof_nodes (l64, n64);
	pta_fi.g_pt.generate_addressof_nodes (l71, n71);
	pta_fi.g_pt.generate_addressof_nodes (l74, n74);
	pta_fi.g_pt.generate_addressof_nodes (l76, n76);
	pta_fi.g_pt.insert_edges (n56, n59, ASTERISK);
	pta_fi.g_pt.insert_edges (n56, n62, ASTERISK);
	pta_fi.g_pt.insert_edges (n59, n62, ASTERISK);
	pta_fi.g_pt.insert_edges (n62, n59, ASTERISK);
	pta_fi.g_pt.insert_edges (n64, n56, ASTERISK);
	pta_fi.g_pt.insert_edges (n59, n59, ASTERISK);
	pta_fi.g_pt.insert_edges (n62, n62, ASTERISK);
	pta_fi.g_pt.insert_edges (n61, n56, ASTERISK);

	pta_fi.g_pt.insert_edges (n56, n71, ASTERISK);
	pta_fi.g_pt.insert_edges (n56, n74, ASTERISK);
	pta_fi.g_pt.insert_edges (n71, n74, ASTERISK);
	pta_fi.g_pt.insert_edges (n74, n71, ASTERISK);
	pta_fi.g_pt.insert_edges (n76, n56, ASTERISK);
	pta_fi.g_pt.insert_edges (n57, n74, ASTERISK);
	pta_fi.g_pt.insert_edges (n74, n74, ASTERISK);
	pta_fi.g_pt.insert_edges (n71, n71, ASTERISK);

	set<pt_node_index> value;
	map<pt_node_index, pt_fi_node *>::iterator ni;
	for (ni = pta_fi.g_pt.nodes.begin (); ni != pta_fi.g_pt.nodes.end (); ni++)
		value.insert (ni->first);

	pta_fi.g_pt.print_graph (NULL);

	pta_fi.get_max_acyclic_ap_len (value);
*/
}

void test2_points_to_analysis_fi_len ()
{
	// test2.c

	points_to_analysis_fi pta_fi (true);

	set<pt_node_index> n6, n7, n8, n12, n13, n19, n20, n18;
	label l6=6, l7=7, l8=8, l12=12, l13=13, l19=19, l20=20, l18=18; 

	pta_fi.g_pt.generate_addressof_nodes (l6, n6);
	pta_fi.g_pt.generate_addressof_nodes (l7, n7);
	pta_fi.g_pt.generate_addressof_nodes (l8, n8);
	pta_fi.g_pt.generate_addressof_nodes (l12, n12);
	pta_fi.g_pt.generate_addressof_nodes (l13, n13);
	pta_fi.g_pt.generate_addressof_nodes (l19, n19);
	pta_fi.g_pt.generate_addressof_nodes (l20, n20);
	pta_fi.g_pt.generate_addressof_nodes (l18, n18);
	pta_fi.g_pt.insert_edges (n6, n7, ASTERISK);
	pta_fi.g_pt.insert_edges (n6, n12, ASTERISK);
	//pta_fi.g_pt.insert_edges (n8, n12, ASTERISK);
	pta_fi.g_pt.insert_edges (n8, n7, ASTERISK);
	pta_fi.g_pt.insert_edges (n8, n13, ASTERISK);
//	pta_fi.g_pt.insert_edges (n13, n12, ASTERISK);
	pta_fi.g_pt.insert_edges (n12, n19, ASTERISK);
	pta_fi.g_pt.insert_edges (n20, n18, ASTERISK);
	pta_fi.g_pt.insert_edges (n18, n19, ASTERISK);

	set<pt_node_index> value;
	map<pt_node_index, pt_fi_node *>::iterator ni;
	for (ni = pta_fi.g_pt.nodes.begin (); ni != pta_fi.g_pt.nodes.end (); ni++)
		value.insert (ni->first);

	pta_fi.g_pt.print_graph (NULL);

	pta_fi.get_max_acyclic_ap_len (value);

	set<pt_node_index> nodes;
	map<node_index, pt_fi_node *>::iterator gni;
	for (gni = pta_fi.g_pt.nodes.begin (); gni != pta_fi.g_pt.nodes.end (); gni++)
		nodes.insert (gni->first);

	def_stmt_set ds;
	pt_node_set value_in;
	value_in.gen (value);
	map<pt_node_index, access_name> new_pt_to_access_name;
	map<pt_node_index, max_depth> new_pt_to_max_depth;
	set<pt_node_index> empty_set;
	map<pt_node_index, map<label, set<pt_node_index> > > empty_edges;
	set<set<pt_node_index> > summ_cmpts;
	map<pt_node_index, pt_node_index> summ_cmpts_map;
	
#if SUMM_K_CONSISTENT
	pta_fi.find_new_ans_and_affected_region (nodes, value_in, 
		empty_set, empty_set, ASTERISK, ds, empty_set, empty_edges,
		new_pt_to_max_depth, summ_cmpts_map, new_pt_to_access_name);
//	pta_fi.find_new_summ_cmpts (nodes, empty_set, value_in, 
//		empty_set, empty_set, ASTERISK, empty_set, empty_edges,
//		new_pt_to_max_depth, summ_cmpts);

//	pta_fi.pt_access_map.print_max_depth_map (new_pt_to_max_depth);
#endif
}

void test3_points_to_analysis_fi_ap_tree ()
{
	list<label> ap;
	ap.push_back (9);
	set<tree> ap_trees;
	program.get_ap_trees (ap, ap_trees);

	set<tree>::iterator ti;
	for (ti = ap_trees.begin (); ti != ap_trees.end (); ti++)
	{
		RESULT ("\n\n------\n");
		print_node (dump_file, 0, *ti, 0);

		set<unsigned int> subfields;
		program.get_subfield_offsets (*ti, subfields);
		set<unsigned int>::iterator si;
		RESULT ("\nsubfields=");
		for (si = subfields.begin (); si != subfields.end (); si++)
			RESULT ("%d,", *si);

	}

}

void test1_allocation_site_based_analysis ()
{
	unlabeled_edges value;
	value.out_edge_list[10].insert (20);
	value.out_edge_list[10].insert (30);
	value.out_edge_list[20].insert (30);
	value.out_edge_list[30].insert (40);
	value.out_edge_list[40].insert (40);
	value.out_edge_list[40].insert (50);
	value.out_edge_list[50].insert (60);
	value.out_edge_list[50].insert (70);
	value.out_edge_list[60].insert (80);
	value.out_edge_list[70].insert (80);
	value.out_edge_list[80].insert (50);
	value.print_value (NULL);

	map<label, set<list<label> > > var_aps;
	value.get_access_paths (var_aps, true);
	value.print_access_paths (var_aps);
}

void test2_allocation_site_based_analysis ()
{
//	test2.c
	unlabeled_edges value;
	value.out_edge_list[6].insert (7);
	// id 19=n1.0+64
	// id 20=n1.64+64
	// id 21=n1.192+64
	// If id 20 and 21 are used, then there is no cycle.
	// If id 19 and 21 are used, then there is a cycle.
	value.out_edge_list[8].insert (20);
	value.out_edge_list[21].insert (7);
	value.out_edge_list[6].insert (12);
	value.out_edge_list[12].insert (12);
	value.out_edge_list[13].insert (18);
	value.out_edge_list[21].insert (18);
	value.print_value (NULL);

	map<label, set<list<label> > > var_aps;
	value.get_access_paths (var_aps, true);
	value.print_access_paths (var_aps);
}

void test3_allocation_site_based_analysis ()
{
//	test2.c
	unlabeled_edges value;
	value.out_edge_list[6].insert (7);
	value.out_edge_list[6].insert (12);
	value.out_edge_list[8].insert (12);
	value.out_edge_list[13].insert (12);
	value.out_edge_list[12].insert (19);
	value.out_edge_list[20].insert (18);
	value.out_edge_list[18].insert (19);
	value.print_value (NULL);

	map<label, set<list<label> > > var_aps;
	value.get_access_paths (var_aps, true);
	value.print_access_paths (var_aps);

	unsigned int c = unlabeled_edges::get_max_acyclic_ap_len (value.out_edge_list);
	RESULT ("\ncount=%d", c);
}

void test4_allocation_site_based_analysis ()
{
//	test45.c
	unlabeled_edges value;
	value.out_edge_list[6].insert (7);
	value.out_edge_list[7].insert (7);
	value.out_edge_list[9].insert (11);
	value.out_edge_list[11].insert (7);
	value.out_edge_list[12].insert (7);
	value.print_value (NULL);

	map<label, set<list<label> > > var_aps;
	value.get_access_paths (var_aps, true);
	value.print_access_paths (var_aps);

	unsigned int c = unlabeled_edges::get_max_acyclic_ap_len (value.out_edge_list);
	RESULT ("\ncount=%d", c);
}

void test1_deterministic_insert ()
{
	deterministic_graph * g = new deterministic_graph;
	sites ss;
	ss.insert (-5);
	deterministic_node * nx = new deterministic_node (ss, 5, g->nodes);
	ss.clear ();
	ss.insert (-6);
	deterministic_node * ny = new deterministic_node (ss, 6, g->nodes);
	ss.clear ();
	ss.insert (1);
	deterministic_node * n1 = new deterministic_node (ss, 10, g->nodes);
	ss.clear ();
	ss.insert (1);
	ss.insert (2);
	deterministic_node * n2 = new deterministic_node (ss, 10, g->nodes);
	ss.clear ();
	ss.insert (3);
	deterministic_node * n3 = new deterministic_node (ss, 10, g->nodes);
	ss.clear ();
	ss.insert (4);
	deterministic_node * n4 = new deterministic_node (ss, 10, g->nodes);
	ss.clear ();
	ss.insert (5);
	deterministic_node * n5 = new deterministic_node (ss, 20, g->nodes);
	ss.clear ();
	ss.insert (6);
	deterministic_node * n6 = new deterministic_node (ss, 20, g->nodes);
	ss.clear ();
	ss.insert (7);
	deterministic_node * n7 = new deterministic_node (ss, 30, g->nodes);

	g->stack.insert_edge (5, *nx);
	g->stack.insert_edge (6, *ny);

	nx->insert_edge (10, *n1);
	n1->insert_edge (10, *n3);
	n3->insert_edge (10, *n3);
	n3->insert_edge (20, *n5);
	n5->insert_edge (30, *n7);

	ny->insert_edge (10, *n2);
	n2->insert_edge (10, *n4);
	n4->insert_edge (20, *n6);
	n6->insert_edge (20, *n6);
	n6->insert_edge (30, *n7);

	g->print_value (NULL);

	RESULT ("\n\nDelete y");
	g->stack.delete_edge (6, *ny);
	g->print_value (NULL);

	RESULT ("\n\nAdd xf");
	g->insert_edge (*nx, 10, 2);
	g->print_value (NULL);
}

void test2_deterministic_copy ()
{
	deterministic_graph * g1 = new deterministic_graph;
	sites ss;
	ss.insert (-5);
	deterministic_node * nx1 = new deterministic_node (ss, 5, g1->nodes);
	ss.clear ();
	ss.insert (1);
	deterministic_node * n1 = new deterministic_node (ss, 10, g1->nodes);
	ss.clear ();
	ss.insert (3);
	deterministic_node * n3 = new deterministic_node (ss, 10, g1->nodes);
	ss.clear ();
	ss.insert (5);
	deterministic_node * n5 = new deterministic_node (ss, 20, g1->nodes);
	ss.clear ();
	ss.insert (7);
	deterministic_node * n7 = new deterministic_node (ss, 30, g1->nodes);

	deterministic_graph * g2 = new deterministic_graph;
	ss.clear ();
	ss.insert (-5);
	deterministic_node * nx2 = new deterministic_node (ss, 5, g2->nodes);
	ss.clear ();
	ss.insert (1);
	ss.insert (2);
	deterministic_node * n2 = new deterministic_node (ss, 10, g2->nodes);
	ss.clear ();
	ss.insert (4);
	deterministic_node * n4 = new deterministic_node (ss, 10, g2->nodes);
	ss.clear ();
	ss.insert (6);
	deterministic_node * n6 = new deterministic_node (ss, 20, g2->nodes);
	ss.clear ();
	ss.insert (7);
	deterministic_node * n8 = new deterministic_node (ss, 30, g2->nodes);

	g1->stack.insert_edge (5, *nx1);
	nx1->insert_edge (10, *n1);
	n1->insert_edge (10, *n3);
	n3->insert_edge (10, *n3);
	n3->insert_edge (20, *n5);
	n5->insert_edge (30, *n7);

	g2->stack.insert_edge (5, *nx2);
	nx2->insert_edge (10, *n2);
	n2->insert_edge (10, *n4);
	n4->insert_edge (20, *n6);
	n6->insert_edge (20, *n6);
	n6->insert_edge (30, *n8);

	RESULT ("\nGRAPH 1");
	g1->print_value (NULL);
	RESULT ("\n\n\nGRAPH 2");
	g2->print_value (NULL);

	RESULT ("\n\n\nG1 + G2");
	g1->copy_value (*g2, false);
	g1->print_value (NULL);

	RESULT ("\n\n\nCLEAN G1 + G2");
	g1->clean ();
	g1->print_value (NULL);
}
#endif

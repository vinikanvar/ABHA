
/************************
 * @author Vini Kanvar
************************/

#include "../common.hh"

#ifndef BLOCK_INFO
#define BLOCK_INFO

#include "../misc/debug.hh"
#include "../misc/parser.hh"

#define CALL_BLOCK 1
#define RETURN_BLOCK 2
#define START_BLOCK 4
#define END_BLOCK 8
#define AUX_BLOCK 16
#define NORETURN_BLOCK 32

/** This is an auxillary data structure associated with each basic block. 
 *  This consists of the cgraph node which this basic block belongs to. The IN and
 *  OUT pointsto information associated with the basic block, the callstring map
 *  (if the basic block is Sp), and flags to determine the type of the block 
 *  (call block, return block, end block, start block) 
 */

class block_information
{
	unsigned int block_type;

	// The reverse-post or post order value of the block.
	unsigned int order;

	// Is this the header of a loop 
	bool is_loop_join;

	/** Parsed information is the constraints (as referred by tree-ssa-structalias.c)
	 *  Integer index to the list of parsed information.
	 *  Bool is true if the parsed information has lhs and rhs corresponding to 
	 *  an assignment statement. Bool is false if the parsed information is 
	 *  a single parsed information due to use of a pointer variable.
	 *  This is a list of indices to the parsed_information.
	 */
	list<pair<unsigned int, bool> > parsed_data_indices;
	
	/** 
	 * We accumulate all the created argument-parameter and return-received
	 * variables mapping constraints. These need to be deleted and added
	 * into parsed_data_indices depending on the called function. They can
	 * be reused from call_return_indices instead of being recreated after
	 * being erased from parsed_data_indices. 
	 */ 
	list<pair<unsigned int, bool> > call_return_indices;

private:
	void push_parsed_data_indices (unsigned int i, bool b);
	void push_call_return_indices (unsigned int i, bool b);

public:
	block_information ();
	unsigned int get_block_type ();
	void set_block_type (unsigned int block_type);
	bool get_loop_join ();
	void set_loop_join ();
	unsigned int get_block_order ();
	void set_block_order (unsigned int order);

	void add_to_parsed_data_indices (unsigned int, bool, basic_block bb);
	void add_to_call_return_indices (unsigned int, bool, basic_block bb);
	list<pair<unsigned int, bool> > get_parsed_data_indices ();
	list<pair<unsigned int, bool> > get_call_return_indices ();
	void erase_assignment_indices ();
};

#endif


/************************
 * @author Vini Kanvar
************************/

#include "common.hh"

#ifndef ANALYSIS_PLUGIN
#define ANALYSIS_PLUGIN

#include "dfa/liveness_analysis.hh"
//#include "dfa/relevance_analysis.hh"
#include "dfa/liveness_analysis_simple.hh"
//#include "dfa/alias_analysis.hh"
//#include "dfa/points_to_analysis.hh"
//#include "dfa/points_to_analysis_basic.hh"
//#include "dfa/points_to_analysis_simple.hh"
#include "dfa/points_to_analysis_fi.hh"
#include "dfa/allocation_site_based_analysis.hh"
#include "misc/debug.hh"
#include "misc/test_cases.hh"
#include "misc/profile.hh"
#include "misc/tvla.hh"

/*-----------------------------------------------------------------------------
 *  Each plugin MUST define this global int to assert compatibility with GPL; 
 *  else the compiler throws a fatal error 
 *-----------------------------------------------------------------------------*/
int plugin_is_GPL_compatible;

/* The driver function for interprocedural aggregate analysis */
static unsigned int aggregate_analysis ();


/*-----------------------------------------------------------------------------
 *  Structure of the pass we want to insert, identical to a regular ipa pass
 *-----------------------------------------------------------------------------*/

struct simple_ipa_opt_pass pass_plugin = 
{
  {
    SIMPLE_IPA_PASS,
    "aggregate",                          /*  name */
    NULL,                                 /*  gate */
    aggregate_analysis,                   /*  execute */
    NULL,                                 /*  sub */
    NULL,                                 /*  next */
    0,                                    /*  static pass number */
    TV_INTEGRATION,                       /*  tv_id */
    0,                                    /*  properties required */
    0,                                    /*  properties provided */
    0,                                    /*  properties destroyed */
    0,                                    /*  todo_flags start */
    0                                     /*  todo_flags end */
  }
};

/*-----------------------------------------------------------------------------
 *  This structure provides the information about inserting the pass in the
 *  pass manager. 
 *-----------------------------------------------------------------------------*/
struct register_pass_info pass_info = {
  &(pass_plugin.pass),                  /* Address of new pass, here, the 'struct
                                        opt_pass' field of 'simple_ipa_opt_pass'
                                        defined above */
        "pta",                          /* Name of the reference pass for hooking up
                                        the new pass.   */
        0,                              /* Insert the pass at the specified instance
                                        number of the reference pass. Do it for
                                        every instance if it is 0. */
        PASS_POS_INSERT_AFTER           /* how to insert the new pass: before,
                                        after, or replace. Here we are inserting
                                        a pass names 'plug' after the pass named
                                        'cfg' */
};

/*-----------------------------------------------------------------------------
 *  plugin_init is the first function to be called after the plugin is loaded
 *-----------------------------------------------------------------------------*/
  int
plugin_init (struct plugin_name_args *plugin_info,
    struct plugin_gcc_version *version)
{

        /*-----------------------------------------------------------------------------
        * Plugins are activiated using this callback 
        *-----------------------------------------------------------------------------*/
        register_callback (
        plugin_info->base_name,     /* char *name: Plugin name, could be any
                                     name. plugin_info->base_name gives this
                                     filename */
        PLUGIN_PASS_MANAGER_SETUP,  /* int event: The event code. Here, setting
                                     up a new pass */
        NULL,                       /* The function that handles event */
        &pass_info);                /* plugin specific data */

        return 0;
}

#endif 

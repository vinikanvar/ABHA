/*
 * Profile.cpp
 *
 *  Created on: 24-Jun-2016
 *      Author: prasanna
 */


#include "profile.hh"
#ifdef PROFILE
#include <stdlib.h>
#include<stdio.h>
#include <sys/time.h>
#include <assert.h>

/* stores the time when we start executing instructions in
 * the current function.  This could happen at function
 * entry, or when we return from a callee.
 */
static unsigned long long start_time[MAX_FUN];
static unsigned long long cstart[MAX_FUN];

static unsigned long long start_space[MAX_FUN];
static unsigned long long c_space_start[MAX_FUN];

/* stores total time spent in the function, cumulative and
 * self */
static unsigned long long cum_time[MAX_FUN];
static unsigned long long self_time[MAX_FUN];

static unsigned long long cum_space[MAX_FUN];
static unsigned long long self_space[MAX_FUN];

/* number of calls to this function */
static unsigned long num_calls[MAX_FUN];

/* keeps track of the call stack. Required so that we
 * increment time in the caller once we return from callee.
 */
static unsigned int call_stack[CALL_DEPTH];

/* Top of the call stack */
static unsigned int cTop = 0;

/* Current function we are looking into */
static unsigned int funcId;


/* helper function to return current timeval as
 * unsigned long long */
static unsigned long long time_now()
{
    struct timeval t;
    gettimeofday(&t, NULL);
    return 1000000LL * t.tv_sec + t.tv_usec;
}

unsigned long long get_curr_time()
{
	return time_now();
}

static unsigned long long space_now()
{
	struct sysinfo info;

	if (sysinfo(&info) != 0)
	{
    		FILE * stat_file = fopen (STAT_FILE, "a");
		PROFILE_RESULT ("Error: sysinfo: error reading system statistics");
		fclose (stat_file);
	}

	unsigned long long tot = info.totalram;
	unsigned long long free = info.freeram;
	return (tot - free);
}

unsigned long long get_curr_space()
{
	return space_now();
}

void timer_start(unsigned int funId)
{
    unsigned long long now_time = time_now();
    /* Compute the time spent in caller and store it */
    unsigned int caller = call_stack[cTop];
    if (caller)
        self_time[caller] += now_time - start_time[caller];

    /* push current function, and start its timer */
    ++cTop;
    assert(cTop < CALL_DEPTH);
    call_stack[cTop] = funId;
    cstart[funId] = start_time[funId] = now_time;
    ++num_calls[funId];

    return;
}

void timer_end(unsigned int funId)
{
    unsigned long long now_time = time_now();
    /* some sanity check */
    assert(call_stack[cTop] == funId);
    assert(cTop > 0);
    /* stop timer for current function, and pop it from call stack */
    self_time[funId] += now_time - start_time[funId];
    cum_time[funId]  += now_time - cstart[funId];

    --cTop;

    /* start the clock for the caller */
    unsigned int caller = call_stack[cTop];
    if (caller)
        start_time[caller] = now_time;

    return;
}

void space_profiler_start(unsigned int funId)
{
    unsigned long long now_space = space_now();
    /* Compute the space spent in caller and store it */
    unsigned int caller = call_stack[cTop];
    if (caller)
        self_space[caller] += now_space - start_space[caller];

    /* push current function, and start its space profiler */
    ++cTop;
    assert(cTop < CALL_DEPTH);
    call_stack[cTop] = funId;
    c_space_start[funId] = start_space[funId] = now_space;
    ++num_calls[funId];

    return;
}

void space_profiler_end(unsigned int funId)
{
    unsigned long long now_space = space_now();
    /* some sanity check */
    assert(call_stack[cTop] == funId);
    assert(cTop > 0);
    /* stop space profiler for current function, and pop it from call stack */
    self_space[funId] += now_space - start_space[funId];
    cum_space[funId]  += now_space - c_space_start[funId];

    --cTop;

    /* start the space profiler for the caller */
    unsigned int caller = call_stack[cTop];
    if (caller)
        start_space[caller] = now_space;

    return;
}

/* id generator for functions */
static int curr_fun_id = 0;
unsigned int next_prof_id(void)
{
    ++curr_fun_id;
    assert(curr_fun_id < MAX_FUN);
    return curr_fun_id;
}

bool is_profiling_on = false;
char* id2name[MAX_FUN];
char* id2_space_name[MAX_FUN];
void print_profile_stats(void)
{
    int i;
    cum_time[0] = self_time[0] = time_now() - start_time[0];
    FILE * stat_file = fopen (STAT_FILE, "a");

    PROFILE_RESULT ("\n");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("\n");
    PROFILE_RESULT ("  %51s %15s %6s  %15s  %6s\n", "FUNCTION (  #Calls)", "SelfTIME", "%", "CumTIME", "%");
    PROFILE_RESULT ("  %51s %15s %6s  %15s  %6s\n", "",                    " (uSec) ", "",  " (uSec)", "");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("\n");
    fprintf (stat_file, "\n");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "\n");
    fprintf (stat_file, "  %51s %15s %6s  %15s  %6s\n", "FUNCTION (  #Calls)", "SelfTIME", "%", "CumTIME", "%");
    fprintf (stat_file, "  %51s %15s %6s  %15s  %6s\n", "",                    " (uSec) ", "",  " (uSec)", "");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "\n");

    for (i = 1; i <= curr_fun_id; i++) {
        PROFILE_RESULT ("  %40s (%8ld) %15llu  %6.2lf  %15llu  %6.2lf\n",
               id2name[i], num_calls[i],
               self_time[i], 100.0D*self_time[i]/self_time[0],
               cum_time[i],  100.0D*cum_time[i]/cum_time[0]);
        fprintf (stat_file, "  %40s (%8ld) %15llu  %6.2lf  %15llu  %6.2lf\n",
               id2name[i], num_calls[i],
               self_time[i], 100.0D*self_time[i]/self_time[0],
               cum_time[i],  100.0D*cum_time[i]/cum_time[0]);
    }

    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("\n");
    PROFILE_RESULT ("  %51s %15llu  100.00  %15llu  100.00\n", id2name[0],
           self_time[0], cum_time[0]);
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("\n");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "\n");
    fprintf (stat_file, "  %51s %15llu  100.00  %15llu  100.00\n", id2name[0],
           self_time[0], cum_time[0]);
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "\n");

//////////////////////////////////////////////////////////////////////////////////////////////

    cum_space[0] = self_space[0] = space_now() - start_space[0];

    PROFILE_RESULT ("\n");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("\n");
    PROFILE_RESULT ("  %51s %15s %6s  %15s  %6s\n", "FUNCTION (  #Calls)", "SelfSPACE", "%", "CumSPACE", "%");
    PROFILE_RESULT ("  %51s %15s %6s  %15s  %6s\n", "",                    " (byte) ", "",  " (byte)", "");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("\n");
    fprintf (stat_file, "\n");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "\n");
    fprintf (stat_file, "  %51s %15s %6s  %15s  %6s\n", "FUNCTION (  #Calls)", "SelfSPACE", "%", "CumSPACE", "%");
    fprintf (stat_file, "  %51s %15s %6s  %15s  %6s\n", "",                    " (byte) ", "",  " (byte)", "");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "\n");

    for (i = 1; i <= curr_fun_id; i++) {
        PROFILE_RESULT ("  %40s (%8ld) %15llu  %6.2lf  %15llu  %6.2lf\n",
               id2_space_name[i], num_calls[i],
               self_space[i], 100.0D*self_space[i]/self_space[0],
               cum_space[i],  100.0D*cum_space[i]/cum_space[0]);
        fprintf (stat_file, "  %40s (%8ld) %15llu  %6.2lf  %15llu  %6.2lf\n",
               id2_space_name[i], num_calls[i],
               self_space[i], 100.0D*self_space[i]/self_space[0],
               cum_space[i],  100.0D*cum_space[i]/cum_space[0]);
    }

    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("\n");
    PROFILE_RESULT ("  %51s %15llu  100.00  %15llu  100.00\n", id2_space_name[0],
           self_space[0], cum_space[0]);
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("-------------------------------------------------------------");
    PROFILE_RESULT ("\n");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "\n");
    fprintf (stat_file, "  %51s %15llu  100.00  %15llu  100.00\n", id2_space_name[0],
           self_space[0], cum_space[0]);
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "-------------------------------------------------------------");
    fprintf (stat_file, "\n");

    fclose (stat_file);
}

void init_profile_stats(void)
{
#if PROFILE
    is_profiling_on = true;
#else
    is_profiling_on = false;
#endif

    /* Compute the time spent in caller and store it */
    cum_time[0] = start_time[0] = time_now();
    id2name[0] = (char*)"TOTAL TIME";

    cum_space[0] = start_space[0] = space_now();
    id2_space_name[0] = (char*)"TOTAL SPACE";
}

#endif



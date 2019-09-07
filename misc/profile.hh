/*
 * Profile.h
 *
 *  Created on: 24-Jun-2016
 *      Author: Amey Karkare, Prasanna Kumar
 *      Extended for memory profiling by Vini Kanvar
 */

#ifndef _PROFILE_H_
#define _PROFILE_H_

#include "../misc/debug.hh"

//#define PROFILE
#ifdef PROFILE

#define MAX_FUN 9999
#define CALL_DEPTH 1999

void timer_start(unsigned int funId);
void timer_end(unsigned int funId);
void space_profiler_start(unsigned int funId);
void space_profiler_end(unsigned int funId);
unsigned int next_prof_id(void);
void init_profile_stats(void);
void print_profile_stats(void);
unsigned long long get_curr_time();

// The default value of global static variables is 0
extern bool is_profiling_on;
extern char* id2name[MAX_FUN];
extern char* id2_space_name[MAX_FUN];
#define PRINT_PROFILE_STATS() print_profile_stats()
#define INIT_PROFILE_STATS() init_profile_stats()

#define FUNBEGIN()                                          \
    static unsigned int _fun_prof_id = 0;                        \
    if (is_profiling_on){					\
    /*fprintf(stderr, "<== %s\n", __func__);*/                       \
    if (!_fun_prof_id)                                           \
    {                                                            \
        _fun_prof_id = next_prof_id();                           \
        id2name[_fun_prof_id] = (char*)__func__;                        \
        id2_space_name[_fun_prof_id] = (char*)__func__;                        \
    } else { /* nothing */ }                                     \
    timer_start(_fun_prof_id);                                    \
    space_profiler_start(_fun_prof_id);}                            \


#define FUNEND() 					\
    	if (is_profiling_on){				\
		timer_end(_fun_prof_id);		\
		space_profiler_end(_fun_prof_id);}

/* careful: we want to use
 *     if (..) RETURN(x, y); else something
 * so we use this funny looking form.
 * otherwise "semicolon" at the end of RETURN will be treated as a
 * separate stmt
 */
#define RETURN(_retval)                          \
    if (1) { FUNEND(); /*fprintf(stderr, "==> %s\n", __func__);*/ return (_retval); } else /*nothing*/
#define RETURN_VOID()                                          \
    if (1) { FUNEND(); /*fprintf(stderr, "==> %s\n", __func__);*/ return; } else /*nothing*/

#define BEGIN_PROFILE()                                          \
		unsigned long long loop_time = get_curr_time();          \


#define END_PROFILE(id) \
    FILE * stat_file = fopen (STAT_FILE, "a");		\
  PROFILE_RESULT ("Error: Time taken for  %s is %15llu\n", id, (get_curr_time() - loop_time)); \
    fclose (stat_file);				\


#define BEGIN_SPACE_PROFILE()                                          \
		unsigned long long loop_space = get_curr_space();          \


#define END_SPACE_PROFILE(id) \
    FILE * stat_file = fopen (STAT_FILE, "a");		\
  PROFILE_RESULT ("Error: Space taken for  %s is %15llu\n", id, (get_curr_space() - loop_space)); \
    fclose (stat_file);		\



#else /* no profiling */

#define FUNBEGIN() (void)0
#define FUNEND() (void)0
#define RETURN(_retval) return (_retval)
#define RETURN_VOID() return
#define PRINT_PROFILE_STATS() (void)0
#define INIT_PROFILE_STATS() (void)0
#define BEGIN_PROFILE() (void)0
#define END_PROFILE(id) (void)0
#define BEGIN_SPACE_PROFILE() (void)0
#define END_SPACE_PROFILE(id) (void)0

#endif
#endif /* _PROFILE_H_ */

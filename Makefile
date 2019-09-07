TEST_FILES=test86.c
OUT=result86
MAX_LEN_PRINT=6
SUMM= -DMAX_LEN_PRINT=${MAX_LEN_PRINT} -DLIVENESS_DETERMINISTIC=1    -DGREEDY_ALIAS_CLOSURE=0   -DGC_ON_THE_FLY=0     -DACCUM_LIVE_CONTEXT_INDEPT=1 -DACCESS_BASED=1 
TIME_STATISTICS=0

TVLA=/home/vini/Work/Education/TVLA/tvla/my-examples/c2tvp
SETS_TVP_FILE=\"${TVLA}/sets.tvp\"
CFG_TVP_FILE=\"${TVLA}/cfg.tvp\"
EDGE_FILE=\"${test}/dump-stats/edge_file\"
UNIQUE_EDGE_FILE=\"${test}/dump-stats/unique_edge_file\"
HEAP_FILE=\"${test}/dump-stats/heap_file\"
USEFUL_AP_FILE=\"${test}/dump-stats/useful_ap_file\"
STAT_FILE=\"${test}/dump-stats/done.txt\"
NEW_FILE=\"${test}/dump-stats/new.txt\"
GC_FILE=\"${test}/dump-stats/gc.txt\"

DDFILES = -DSETS_TVP_FILE=\"${SETS_TVP_FILE}\" -DCFG_TVP_FILE=\"${CFG_TVP_FILE}\" -DEDGE_FILE=\"${EDGE_FILE}\" -DUNIQUE_EDGE_FILE=\"${UNIQUE_EDGE_FILE}\" -DHEAP_FILE=\"${HEAP_FILE}\" -DUSEFUL_AP_FILE=\"${USEFUL_AP_FILE}\" -DSTAT_FILE=\"${STAT_FILE}\" -DNEW_FILE=\"${NEW_FILE}\" -DGC_FILE=\"${GC_FILE}\"
DFILES = -DSETS_TVP_FILE=${SETS_TVP_FILE} -DCFG_TVP_FILE=${CFG_TVP_FILE} -DEDGE_FILE=${EDGE_FILE} -DUNIQUE_EDGE_FILE=${UNIQUE_EDGE_FILE} -DHEAP_FILE=${HEAP_FILE} -DUSEFUL_AP_FILE=${USEFUL_AP_FILE} -DSTAT_FILE=${STAT_FILE} -DNEW_FILE=${NEW_FILE} -DGC_FILE=${GC_FILE}
FILES = SETS_TVP_FILE='\"${SETS_TVP_FILE}\"' CFG_TVP_FILE='\"${CFG_TVP_FILE}\"' EDGE_FILE='\"${EDGE_FILE}\"' UNIQUE_EDGE_FILE='\"${UNIQUE_EDGE_FILE}\"' HEAP_FILE='\"${HEAP_FILE}\"' USEFUL_AP_FILE='\"${USEFUL_AP_FILE}\"' STAT_FILE='\"${STAT_FILE}\"' NEW_FILE='\"${NEW_FILE}\"' GC_FILE='\"${GC_FILE}\"'

PARTIAL_ORDER_STATISTICS=0

DIRECTIVES=  ${DFILES}   ${SUMM}         -DPARTIAL_ORDER_STATISTICS=${PARTIAL_ORDER_STATISTICS} -DTIME_STATISTICS=${TIME_STATISTICS}  

#------ MAKE CHANGES TO BASE_DIR : Please put the path to base directory of your pristine gcc-4.7.2 build -----------#
BASE_DIR = /home/vini/Work/Education/GCC/Installations/gcc-4.7.2-fn-ptr

INSTALL = ${BASE_DIR}/install
CPP = ${INSTALL}/bin/g++
CC = ${INSTALL}/bin/gcc
NEW_PATH = ${BASE_DIR}/gcc-4.7.2-fn-ptr/gcc

GCCPLUGINS_DIR:= ${shell ${CPP} -print-file-name=plugin}
INCLUDE= -fPIC -I${GCCPLUGINS_DIR}/include -I${NEW_PATH}

FLAGS_SRC= -flto -flto-partition=none -O3 -std=c++0x ${DIRECTIVES}
FLAGS_TEST= -flto -flto-partition=none -O0 -std=gnu99 -fno-inline -fno-ipa-cp-clone


SRC = /home/vini/Work/Education/GCC/Installations/heap-analysis/plugins/hra-source
TEST=/home/vini/Work/Education/GCC/Installations/heap-analysis/plugins/hra-test/test-cases

%.o: /home/vini/%.c
	${CPP} ${FLAGS_TEST} ${INCLUDE} -c $< 

%.o: ${TEST}/%.c
	${CC} ${FLAGS_TEST} ${INCLUDE} -c $< 

%.o: ${SRC}/%.cpp
	${CPP} ${FLAGS_SRC} ${INCLUDE} -c $< 

%.o: ${SRC}/misc/%.cpp
	${CPP} ${FLAGS_SRC} ${INCLUDE} -c $< 

%.o: ${SRC}/ipa/%.cpp
	${CPP} ${FLAGS_SRC} ${INCLUDE} -c $< 

%.o: ${SRC}/dfa/%.cpp
	${CPP} ${FLAGS_SRC} ${INCLUDE} -c $< 

%.o: ${SRC}/dfv/%.cpp
	${CPP} ${FLAGS_SRC} ${INCLUDE} -c $< 

%.o: ${SRC}/misc/%.cpp
	${CPP} ${FLAGS_SRC} ${INCLUDE} -c $< 

plugin.so: \
liveness_analysis.o \
non_deterministic_node.o \
non_deterministic_graph.o \
deterministic_graph.o \
deterministic_node.o \
side_effects.o \
liveness_analysis_simple.o \
allocation_site_based_analysis.o \
test_cases.o \
tvla.o \
variables.o \
context.o \
backward_inter_procedural_analysis.o \
forward_inter_procedural_analysis.o \
inter_procedural_analysis.o \
parser.o \
analysis_plugin.o \
unlabeled_edges.o \
debug.o \
profile.o \
block_information.o \
\
pt_node_set.o \
pt_fi_graph.o \
pt_fi_node.o \
ap_fi_graph.o \
ap_fi_node.o \
pt_access_fi_map.o \
access_name.o \
points_to_analysis_fi.o
	${CPP} ${INCLUDE} ${FLAGS_SRC} -shared $^ -o $@ 

##############################

TEST_OBJS=${TEST_FILES:.c=.o}
test: ${TEST_OBJS} plugin.so
	${CPP} -fplugin=./plugin.so ${TEST_OBJS} ${FLAGS_TEST} -fdump-ipa-all -fdump-tree-all -fdump-ipa-pta -fipa-pta -o ${OUT} -O3

pta:
	${CPP} -O3 -fdump-ipa-pta -fipa-pta test.c

dot:
	dot -Tps graph.dot -o out.ps
	evince out.ps &

##############################

alloc:
	make -e SUMM='-DMAX_LEN_PRINT=${MAX_LEN_PRINT} -DLIVENESS_DETERMINISTIC=${LIVENESS_DETERMINISTIC}  -DGREEDY_ALIAS_CLOSURE=${GREEDY_ALIAS_CLOSURE}  -DGC_ON_THE_FLY=${GC_ON_THE_FLY}  -DACCUM_LIVE_CONTEXT_INDEPT=${ACCUM_LIVE_CONTEXT_INDEPT}' ${FILES}
	cp plugin.so plugin-alloc-l${MAX_LEN_PRINT}.so 

##############################

access:
	make all-clean; \
	make -e SUMM='-DACCESS_BASED=1 -DSUMM_TYPE_K=1 -DMAX_LEN_PRINT=${MAX_LEN_PRINT}' ${FILES}
	cp plugin.so plugin-access-l${MAX_LEN_PRINT}.so 

##############################

alloc-dump-analysis:
	g++ ${SRC}/statistics/allocation_site_based_analysis/points_to_edges.cpp ${DDFILES} -DMAX_LEN_PRINT=${MAX_LEN_PRINT} 
	./a.out

##############################

clean:
	\rm -f test *.c.* *~ a.out result* test*.o

all-clean:
	make clean
	\rm plugin.so *.o *.c


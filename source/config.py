#!/usr/bin/env python2
# -------------------------------------------------------------------------------------------------
#
#    ,ggggggggggg,     _,gggggg,_      ,ggggggggggg,      ,gggg,  
#   dP"""88""""""Y8, ,d8P""d8P"Y8b,   dP"""88""""""Y8,  ,88"""Y8b,
#   Yb,  88      `8b,d8'   Y8   "8b,dPYb,  88      `8b d8"     `Y8
#    `"  88      ,8Pd8'    `Ybaaad88P' `"  88      ,8Pd8'   8b  d8
#        88aaaad8P" 8P       `""""Y8       88aaaad8P",8I    "Y88P'
#        88""""Y8ba 8b            d8       88"""""   I8'          
#        88      `8bY8,          ,8P       88        d8           
#        88      ,8P`Y8,        ,8P'       88        Y8,          
#        88_____,d8' `Y8b,,__,,d8P'        88        `Yba,,_____, 
#       88888888P"     `"Y8888P"'          88          `"Y8888888 
#
#   The Block Oriented Programming (BOP) Compiler - v2.1
#
#
# Kyriakos Ispoglou (ispo) - ispo@purdue.edu
# PURDUE University, Fall 2016-18
# -------------------------------------------------------------------------------------------------
#
#
# config.py
#
# This is the main configuration file with BOPC options.
#
# NOTE: There are a bunch of minor configuration options, on coreutils.py but there is no reason
#       to modify them.
#
# -------------------------------------------------------------------------------------------------



# -------------------------------------------------------------------------------------------------
# Depth metric for functions (can be 'min', 'max' or 'median')
#  
# Determine the metric for measuring function's depth. This option estimates the minimum number of
# distinct basic blocks that should be executed within a function. To do that, one should look at
# the shortest paths from the entry point to all final basic blocks (those that end with a return
# instruction) and select as depththe length of the minimum of these (shortest) paths ('min' 
# option).
#
# However this metric might not always work that well, as it's very common to make argument checks
# at the very early stages of a function and abort if they do not meet the requirements.
#   
# Hence, we provide 3 metrics: The minimum among the shortest paths that we discussed, the maximum
# ('max' option) and the median of all shortest paths ('median' option).
# 
FUNCTION_DEPTH_METRIC = 'min'



# -------------------------------------------------------------------------------------------------
# When the Symbolic Execution engine gives up on a basic block abstraction (in seconds)
#
ABSBLK_TIMEOUT = 5



# -------------------------------------------------------------------------------------------------
# How many tries we should make before we give up on __enum_induced_subgraphs().
#
# Enumerating all induced subgraphs can take exponential time. To address that we set an upper
# bound. After calculating a fixed number of induced subgraphs, we give up, and we use the 
# best ones up to that point. Set this value to -1 to set the upper bound to infinity.
#
MAX_INDUCED_SUBRAPHS_TRIES = -1
MAX_ALLOWED_INDUCED_SUBGRAPHS = 1024



# -------------------------------------------------------------------------------------------------
# How many times we should permute the OOO SPL statements before we give up. Set to -1 to try all
# possible permutations. This makes sense when 'ooo' optimization is enabled
#
N_OUT_OF_ORDER_ATTEMPTS = 3



# -------------------------------------------------------------------------------------------------
# Trace searching algorithm picks the K shortest paths from Delta Graph (K = PARAMETER_K). However
# there are cases that there are >K paths that are all worth to try. In those cases we keep trying
# paths, as long as their distances are below this threshold.
#
# MAX_GOOD_INDUCED_SUBGRAPH_SIZE = 10 (NOT IMPLEMENTED)
#
PARAMETER_K = 4#10



# -------------------------------------------------------------------------------------------------
# Number of different shortest paths between 2 functional blocks (needed for concolic execution).
# Set to -1 to try all shortest paths
#
PARAMETER_P = 8



# -------------------------------------------------------------------------------------------------
# The actual size of load/store operations for memrd and memwr SPL statements in bytes. This
# parameter can be 1, 2, 4 or 8 bytes.
#
MEMORY_LOADSTORE_SIZE = 1



# -------------------------------------------------------------------------------------------------
# When the Symbolic Execution engine gives up on trace searching (in seconds). That is, when
# the concolic execution gives up on verifying a dispatcher gadget.
#
SE_TRACE_TIMEOUT = 8



# -------------------------------------------------------------------------------------------------
# Maximum length of the final trace (a candidate execution trace cannot have more blocks that this).
#
MAX_ALLOWED_TRACE_SIZE = 100



# -------------------------------------------------------------------------------------------------
# Maximum number of basic blocks in path between 2 accepted blocks (i.e., maximum number of basic
# blocks in a dispatcher).
#
MAX_ALLOWED_SUBPATH_LEN = 40



# -------------------------------------------------------------------------------------------------
# The stack base address (along with $rsp) for symbolic execution.
#
# WARNING: Make sure that RSP doesn't go beyond page limit (o/w addresses are not +w) +0x800 is a
#          very good offset. Don't change it !
# 
STACK_BASE_ADDR = 0x7ffffffffff0000
RSP_BASE_ADDR   = STACK_BASE_ADDR + 0x800



# -------------------------------------------------------------------------------------------------
# In some cases it may be worth to make $rbp symbolic as well (depends on the binary).
#
MAKE_RBP_SYMBOLIC = False



# -------------------------------------------------------------------------------------------------
# What if the final solution requires some registers to be initialized upon entry point? In that
# case we can either shift the entry point backwards, at the point that register is initiliazed,
# and re-run BOPC from there, or we can simply such solutions.
#
ALLOW_REGISTER_WRITES = True



# -------------------------------------------------------------------------------------------------
# I have no idea what this is for, but it seems that I was planning to make another optimization.
#
MAXIMUM_THRESHOLD = 0x800



# -------------------------------------------------------------------------------------------------
# When we deal with loops, the Symbolic Execution engine should simulate the loop the same number
# of times (to ensure that the all iterations can be exetuted successfully under exploitation).
# However, when we have infinity loops, we cannot simulate the loop and infinite amount of times,
# but instead we have to stop at a certain threshold.
#
# WARNING: Make sure that in case of conditional loops, the number of expected iterations is
#          larger than this value, otherwise we will get no solution
#
SIMULATED_LOOP_ITERATIONS = 4 #128



# -------------------------------------------------------------------------------------------------
# Another optimization that never implemented...
#
ADAPTIVE_LOOP_SIMULATION = True



# -------------------------------------------------------------------------------------------------

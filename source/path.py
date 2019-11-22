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
# path.py:
#
# This module is the "assistant" of the Symbolic Execution engine. Clearly, the unrestricted usage
# of symbolic execution can cause BOPC to run for ever (bottleneck). To address this problem,
# we aim to restrict the Symbolic Execution as much as possible. So, instead of letting Symbolic
# Execution engine to use it's build-in BFS for the path exploration, we find out (i.e., guess) the
# exact path(s) and we _guide_ the Symbolic Execution engine to strictly follow them. Therefore, we
# avoid the exponential growth of the states.
#
# In case that the recommended path does not work out (due to the unsatisfiable constraints), we
# need to try another path and so on. In the worst case we will try all the paths and the result
# will be the same with the unguided Symbolic Execution. Having a way to quickly generate candidate
# paths is crucial here.
#
# The trick here is to "rank" the paths, starting from the one which is more likely to succeed. A
# good metric here is the path length in the CFG (shortest paths in CFG are not like shortest paths
# in normal graphs, due to the context sensitivity). Therefore, we start with the shortest path
# first, then we move on the second shortest path and so on.
#
#
# * * * ---===== TODO list =====--- * * *
#
# [1]. Implement Lawler's modification in k_shortest_paths() to avoid duplicates (or ue Eppstein's
#      algorithm to deal with looping paths).
#
# -------------------------------------------------------------------------------------------------
from coreutils import *

import networkx as nx
import queue
import heapq
import traceback


# ------------------------------------------------------------------------------------------------
# Constant Definitions
# ------------------------------------------------------------------------------------------------
_NULL_NODE   = -1                                   # null (non-existent) node
_SINK_NODE   = 0                                    # the sink node in delta graph



# -------------------------------------------------------------------------------------------------
# _queue_obj: This class is the wrapper object that is used in the priority queue.
#
class _queue_obj( object ):
    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor. Simply initialize class members.
    #
    # :Arg data: Object's data
    # :Arg weight: Object's weight (used for the comparisons)
    #
    def __init__( self, data, weight ):
        self.weight = weight
        self.data   = data


    # ---------------------------------------------------------------------------------------------
    # __cmp__(): Overloaded operator for object comparison.
    #
    # :Arg other: The other object to compare.
    # :Ret: Function retuns a <0 value if self.weight < other.weight, 0 if 
    #       self.weight == other.weight and a >0 value if self.weight > other.weight.
    #
    def __cmp__( self, other ):
        return cmp(self.weight, other.weight)



# -------------------------------------------------------------------------------------------------



# -------------------------------------------------------------------------------------------------
# _cs_ksp_intrl: This class finds the k shortest context sensitive loopless paths with non-negative
#   edge costs from a single source to a single destination using Yen's algorithm as described in
#   [1]. Algorithm first finds the shortest paths (using any of the well known  algorithms) and 
#   then it finds K-1 deviations of the shortest path.
#
#   The problem here, is that shortest paths are CFG shortest paths and therefore they are context
#   sensitive. Thus we have to modify the existing algorithm. TODO: rewrite
#
#
# [1]. Yen, Jin Y. "Finding the k shortest loopless paths in a network." management Science 
#       17.11 (1971): 712-716.
#
class _cs_ksp_intrl( object ):
    ''' ======================================================================================= '''
    '''                                   INTERNAL FUNCTIONS                                    '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __get_precall_stack(): This function calculates the "precall" stack for a given node in a
    #       path. The precall stack is like the regular call stack, but instead of storing the
    #       return address for every function call, it stores the caller's address (we do this as
    #       it's more convenient to work with). Precall stack is the "context" of the current node.
    #
    # :Arg path: A path as a list
    # :Arg node: The given node to retrieve pre-call stack for
    # :Ret: The pre-call stack for the given node.
    #
    def __get_precall_stack( self, path, node=None ):
        pcallstack = []


        for u, v in to_edges(path):                 # for every edge on the path          
            if u == node: break                     # if you have reached the target node, stop

            # we can do this, because path is not malformed
            # get the jump kind of the edge in CFG
            if self.__G.has_edge(self.__f(u), self.__f(v)):
                jumpkind = self.__G.get_edge_data(self.__f(u), self.__f(v))['jumpkind']
            else:
                error("Edge (0x%x -> 0x%x) is missing from the CFG" % (u, v))

            # push on calls, pop on returns (as a regular stack works)
            if   jumpkind == 'Ijk_Call': pcallstack.append(u)
            elif jumpkind == 'Ijk_Ret':  pcallstack.pop()


        return pcallstack                           # return the precall stack



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor. 
    #
    # :Arg graph: Graph to work on
    # :Arg shortest_path_cb: A callback function for calculating shortest paths
    # :Arg f: A lambda function to transform nodes before used as "indices" in the graph
    #
    def __init__( self, graph, shortest_path_cb, f ):
        self.__G             = graph                # simply store arguments locally
        self.__shortest_path = shortest_path_cb
        self.__f             = f

    

    # ---------------------------------------------------------------------------------------------
    # k_shortest_paths(): As the name suggests, this function finds the k shortest loopless paths.
    #       The only issue here is that Yen's algorithm can return duplicate paths. We can fix this
    #       issue by implementing "Lawler's modification". The algorithm also uses an optimization:
    #       Instead of removing edges and nodes from the graph and adding them later, we simply
    #       "mark" them and we instruct each shortest path algorithm to explicitly avoid them
    #       during search. 
    #
    # :Arg source: The source node
    # :Arg destination: The destination node
    # :Arg cur_uid: UID of the SPL statement that is about to execute
    # :Arg K: The number of paths to search for
    # :Ret: This function is actually a generator. Every time that's invoked it returns a tuple 
    #       (cost, path) that contains the cost of the next shortest path along with that path.
    #       If such a path does not exists, function returns (-1, []).
    #
    def k_shortest_paths( self, source, destination, cur_uid, K ):
        assert( K > 0 )                             # we should search for at least 1 path

        source      = int(source)                   # source and destination may be 'long'
        destination = int(destination)


        # find the first shortest path (along with its auxiliary information)
        path, pathlens, expaths = self.__shortest_path( source, destination, cur_uid )        
        length = pathlens[-1]


        if length < 0 or length == INFINITY:        # if path doesn't exist, stop
            return

        yield length, expaths[-1]                   # start with the shortest expanded path


        # NOTE: We start to work with path and not with expaths[-1]. If path has cycles,
        # then we may return the same path >1 times. Not a big deal though.       

        A = [path]                                  # the k shortest paths
        B = []                                      # heap for next potential shortest path
        L = [ pathlens[:] ]                         # additional tables for previous path lengths
        E = [ expaths[:]  ]                         # and previous expanded paths

        prev_expaths = [ expaths[-1][:] ]           # remember all previous expanded paths
    

        # -------------------------------------------------------------------------------
        # Each iteration finds the next shortest path
        # -------------------------------------------------------------------------------   
        for k in range(1, K):                       # for each shortest path deviation

            # spur node ranges from first to one before the last node in the previous (k-1) path
            for i in range(0, len(A[k-1]) - 1):
                spur = A[k - 1][i]                  # pick a spur node

                # root path: Path from the source to the spur node of the (k-1) path
                rootpath    = A[k-1][:i+1]
                rootpathlen = L[k-1][i]

                
                # Now it's time for our optimization: Instead of removing edges and nodes, we
                # set to them the "avoid" attribute and we explicitly instruct shortest path
                # algorithm to avoid them during search. The "avoid" operation has to be 
                # context sensitive

                for p in A:                         # for each previous path
                    if len(p) > i and rootpath == p[:i+1]:
                        # "remove" edge
                        self.__G[ self.__f(p[i]) ][ self.__f(p[i+1]) ][ 'avoid' ] = \
                                    self.__get_precall_stack(p, p[i])
  
                    # print '\tDROP EDGE', self.__f(p[i]), self.__f(p[i+1]), self.__get_precall_stack(p, p[i])



                for node in rootpath[:-1]:          # for each node in rootpath (except spur node)
                    # "remove" node
                    self.__G.node[ self.__f(node) ][ 'avoid' ] = \
                                self.__get_precall_stack(rootpath, node)

                    # print '\tDROP NODE', self.__f(node), self.__get_precall_stack(rootpath, node)


                # calculate spur path from the spur node to the destination
                # (the rootpath is needed for the case of CFG)

                # this destroys 'depth' and 'path', so we have to precalculate them
                spurpath, spurpathlens, spurexpaths = \
                            self.__shortest_path(spur, destination, cur_uid, self.__get_precall_stack(A[k-1], spur))


                # print "TRY SP", hex(spur), hex(destination), pretty_list(spurpath)
                        
                length = spurpathlens[-1]


                # if path exists                
                if length > 0 and length < INFINITY:
                    path = rootpath[:-1] + spurpath

                    # append lengths of the root path to the spur path
                    pathlens = L[k-1][:i] + map(lambda l: l + rootpathlen, spurpathlens)

                    # do the same with expanded (sub)paths
                    expaths = E[k-1][:i][:]

                               # prepend for the root subpath on every spur subpath (use [:] to make copies)
                    for expath in spurexpaths:
                        if i > 0:
                            expaths.append( E[k-1][i-1][:] + expath[:] )
                        else:
                            expaths.append( expath[:] )


                    # Add potential shortest path to the heap


                    # Paths that invoke the same function multiple times, cause the algorithm
                    # to return the same path multiple times (because the spur path can visit
                    # (expand) this function, thus resulting a new path that is actually the same).
                    #
                    # To fix that, we look at the expanded paths (where all functions are expanded)
                    # so we can quickly discard duplicates.
                    is_unique = True

                    for expath in prev_expaths:     # for each previous expanded path
                        if not cmp(expath, expaths[-1]):
                            is_unique = False       # path is not unique. Discard it
                            break


                    # if path is unique add it to the list and to the heap
                    if is_unique: 
                        prev_expaths.append(expaths[-1])                 
                        heapq.heappush(B, (length+rootpathlen, path, pathlens, expaths) )


                # print '\t\tCLEAR ALL DROPS'

                # add back the edges and nodes that have been "deleted" from the graph.                     
                # (simply delete "avoid" attributes from them)
                for node, _ in nx.get_node_attributes(self.__G, 'avoid').items(): 
                    del self.__G.node[ node ]['avoid']                  
            
                for edge, _ in nx.get_edge_attributes(self.__G, 'avoid').items():                   
                    del self.__G[ edge[0] ][ edge[1] ]['avoid']


            if not B:
                # if heap is empty then there are no spur paths. This is the case when all spur
                # paths have already added to A, or when there is no path between source and
                # destination.
                break
                
            # A[k] = shortest path from heap
            cost, path, pathlens, expaths = heapq.heappop(B)
            
            A.append(path)                          # add path to A
            L.append(pathlens)                      # add path lengths to L
            E.append(expaths)                       # add expanded paths to E
       
            yield cost, expaths[-1]                 # return next path (expanded version)



    # ---------------------------------------------------------------------------------------------
    # k_shortest_loops(): As the name suggests, this function finds the k shortest loops (cycles)
    #       starting from a given source. To do that, we find the k shortest paths from the source
    #       to each source predecessor and we add one more edge to form the cycle. Then, we simply
    #       select the k shortest cycles (as we can have up to k paths for each predecessor).
    #
    # :Arg source: The source node
    # :Arg cur_uid: UID of the SPL statement that is about to execute
    # :Arg K: The number of loops to search for
    # :Ret: This function is actually a generator. Every time that's invoked it returns a tuple 
    #       (cost, cycle) that contains the cost of the next cycle  with that cycle. If such a
    #       loop does not exists, function returns (-1, []).
    #
    def k_shortest_loops( self, source, cur_uid, K ):        
        heap = []                                   # heap to store all nodes

        # for each predecessor & for each of the (up to) K shortest paths
        for destination in ADDR2NODE[source].predecessors:
            for length, path in self.k_shortest_paths(source,  destination.addr, cur_uid, K):
                if length != INFINITY:

                    # The last edge that we add, might be in a different context (this happens
                    # when the predecessor edge is a return). If our context is right, the
                    # precall stack will have 0 or 1 elements. In the 2nd case, that element
                    # and the source must be a valid edge in the CFG with the "fakeret" attribute.
                    callstack = self.__get_precall_stack(path)

                    if len(callstack) == 1 and \
                        not self.__G.has_edge(self.__f(callstack[0]), self.__f(source)):
                            continue                # loop out of context


                    # add the predecessor edge to complete the cycle
                    heapq.heappush(heap, (length + 1, path + [source]))


        # yield the (up to) K minimum cycles
        while len(heap) > 0 and K > 0:
            yield heapq.heappop(heap)               # return length, path              
            K -= 1                                  # decrement K

                  

# -------------------------------------------------------------------------------------------------



# -------------------------------------------------------------------------------------------------
# _cfg_shortest_path: This module calculates shortest paths within a CFG. Searching for shortest
#   paths in a CFG is not as simple as searching for shortest paths in a regular graph, as paths
#   are context sensitive. Let's see a counterexample:
#
#                        +              +----------> foo
#                        |              |             +
#                    call foo           |             |
#                        | <----------------+         |
#                       {B}             |   |         |
#                        |              |   |         |
#                        |              |   |         |
#                       {A}             |   |         |
#                        |              |   |         |
#                    call foo +---------+   |         |
#                        |                  |         v
#                        v                  +------+ retn
#
#   Let's assume that our code doesn't have any loops. This means that it's impossible to move from
#   {A} to {B} under program execution and hence, such a path should not exist. However, if we
#   apply a classic shortest path algorithm (e.g., Dijkstra), we will find a path, that goes from
#   {A} to foo(), then to the return point of foo() and then to the instruction right after the 1st
#   call thus ending up at {B}. The main cause of this issue is that in CFG, a block with a retn,
#   has an edge to every possible return point and the shortest path algorithm does not take into
#   consideration the current "context".
#
#   A naive solution here, is to keep track of the current path, using backpointers. Every time we
#   encounter a return instruction, we move backwards to the point that this function was invoked
#   and we pick the appropriate edge, that take us to the instruction right after call.
#   
#   The problem with this solution, is that it can easily fall into a _deadlock_. For instance,
#   consider the case where we have two paths in the priority queue. The 1st path has visited few
#   blocks of some function foo(), and therefore they are marked as visited. Now, the 2nd path
#   reaches a block that calls foo(). If foo() has already been analyzed, we can simply follow the
#   "fakeret" edge and use foo()'s length (or "depth") as edge weight. Unfortunately,we don't know
#   that (as it's under inspection by the 1st path) and we can't visit it twice, thus creating a
#   deadlock
#
#
#   The problem gets even harder when CFG contains recursive functions or sets of functions that
#   form a cycle in the Call Graph). Our approach is to use a variant of Dijkstra's algorithm. If
#   a function doesn't have any callees, a classic Dijsktra suffices to find out the shortest 
#   paths. Otherwise, we recursively do a Dijkstra for each calling function. Thus, we can get each
#   function's depth before we continue searching. Finally, we also need a Call Stack to avoid
#   infinity loops when we analyze recursive functions.
#
class _cfg_shortest_path( _cs_ksp_intrl ):
    ''' ======================================================================================= '''
    '''                                   INTERNAL FUNCTIONS                                    '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __valid_neighbors(): Given a node, find all "valid" neighbors (remember not all edges in CFG
    #       are valid).
    #
    # :Arg node: Node to find it's neighbors.
    # :Ret: A list of all neighbor nodes.
    # 
    def __valid_neighbors( self, node ):
        # get all node's neighbors as tuples (node, jumpkind)
        neighbors = [ (n, self.__G.get_edge_data(node, n)['jumpkind']) 
                        for n in self.__G.neighbors(node) ]

        jumps = [ j for (n,j) in neighbors ]        # isolate jump kinds

        # Uncomment the following line to return all targets and behave like a normal BFS:
        #       return [n for n,_ in neighbors]


        # -------------------------------------------------------------------------------
        # Special Case #1: syscall
        # 
        # When node ends with a syscall, it has 2 edges: One to the node after syscall 
        # (marked as Ijk_FakeRet) and one to an internal node for syscall (marked as 
        # Ijk_Sys_syscall). We only care about the 1st case.
        # -------------------------------------------------------------------------------
        if   ['Ijk_FakeRet', 'Ijk_Sys_syscall'] == jumps: return [neighbors[0][0]]      
        elif ['Ijk_Sys_syscall', 'Ijk_FakeRet'] == jumps: return [neighbors[1][0]]


        # -------------------------------------------------------------------------------
        # Special Case #2: call
        #
        # When node ends with a call, it has 2 edges: One to the function's entry point
        # (marked as Ijk_Call) and one the node after call (marked as Ijk_FakeRet). If
        # it's the 1st time we visit this function, we use the 1st edge in order to 
        # analyse function. Othewise, we use the 2nd edge and we set the weight to be
        # equal with function's minimum depth (from entry point to the shortest exit).
        # -------------------------------------------------------------------------------
        elif ['Ijk_FakeRet', 'Ijk_Call'] == jumps:
            # return caller function as well (but mark it first)
            # caller should be returned first
            return [(neighbors[1][0], 'caller', neighbors[0][0])]
            
            '''
            if neighbors[1][0].addr in self.__depth:                
                self.__G[ node ][ neighbors[0][0] ]['depth'] = self.__depth[neighbors[1][0].addr]
                return [neighbors[0][0]]
            else: 
                return [neighbors[1][0]]
            '''

        elif ['Ijk_Call', 'Ijk_FakeRet'] == jumps:          
            # return caller function as well (but mark it first)
            return [(neighbors[0][0], 'caller', neighbors[1][0])]

            '''
            if neighbors[0][0].addr in self.__depth:        
                self.__G[ node ][ neighbors[1][0] ]['depth'] = self.__depth[neighbors[0][0].addr]
                return [neighbors[1][0]]
            else:           
                return [neighbors[0][0]]
            '''

        elif ['Ijk_Call'] == jumps:
            # in that case, return block is missing, so we skip it
            return [(neighbors[0][0], 'caller', -1)]


        # -------------------------------------------------------------------------------
        # Special Case #3: retn
        #
        # In case of a return, we're using back pointers to move backwards in current
        # path, until we find a node with a Ijk_FakeRet edge that points to a node in
        # the return list (the Ijk_Ret edges).
        #
        #
        # UPDATE: In the "Recursive Dijkstra" approach, a return block indicates the
        # end of the search and therefore, we don't have to look for the block after
        # the caller.
        # -------------------------------------------------------------------------------
        elif 'Ijk_Ret' in jumps:
            return []                   # the party stops here....

            '''
            # get edge's jump kind or None if edge doesn't exit
            edge = lambda u, v: self.__G.get_edge_data(u, v)['jumpkind'] \
                             if self.__G.get_edge_data(u, v) else None

            # get all nodes with Ijk_Ret edges
            ret = [(n,j) for (n,j) in neighbors if j == 'Ijk_Ret']

            curr  = node
            depth = 0 

            while curr > 0:                         # while we haven't reach root
                # get edges from curr to all return targets
                caller = [n for n,_ in ret if edge(curr, n) == 'Ijk_FakeRet']

                if caller:                          # caller found!
                    self.__G[ curr ][ caller[0] ][ 'depth' ] = depth
                    self.__depth[ prev.addr ] = depth

                    return caller                   # caller is unique                  

                prev = curr                         # ow, move one step back
                curr = self.__backpointer.get(curr.addr, _NULL_NODE)

                if curr == _NULL_NODE: return []

                # increase function's depth (if there are nested functions, accumulate depth)
                depth += 1 + self.__G[ curr ][ prev ].get('depth', 0)


            # this point should never be reached
            '''
        

        # -------------------------------------------------------------------------------
        # Case #4: Other jumps (Ijk_boring)
        #
        # For the rest of the jumps, we keep all edges.
        # -------------------------------------------------------------------------------   
        else: return [n for n,_ in neighbors]



    # ---------------------------------------------------------------------------------------------
    ''' # Old Shortest Path algorithm (keep it for reference) #

    # ---------------------------------------------------------------------------------------------
    # __bfs_variant(): Calculate the shortest paths from root to all final nodes, using a variant
    #       of classic Breadth First Search (BFS) algorithm. This algorithm has an extra feature:
    #       it _avoids_ all the nodes and edges that have the "avoid" attribute. In some cases we
    #       we need to find a path that doesn't contain some specific edges/nodes. Thus, instead
    #       of deleting and adding them later, we simply mark them as "avoid" and we instruct the
    #       algorithm to ignore them during searcing.
    # 
    # :Arg root: node to start from searching
    # :Arg finals: a list of all target nodes
    # :Ret: A list of tuples with the length and the path for each final node.
    #   
    def __bfs_variant( self, root, finals=[] ):     
        nleft  = len(finals)                        # number of final nodes
        finals_d = dict((n,0) for n in finals)      # cast to dict to search in O(1)

        visited              = { }                  # visited nodes
        visited[ root.addr ] = 0                    # distance from root is 0

        self.__backpointer            = { }         # backpointers      
        self.__backpointer[root.addr] = _NULL_NODE  # root has no parent

        self.__depth = { }                          # function's min depth


        # clear leftovers in CFG from previous calls
        for n, _ in nx.get_edge_attributes(self.__G,'depth').items():
            del self.__G.edge[ n[0] ][ n[1] ]['depth']


        # -------------------------------------------------------------------------------
        # start searching
        # -------------------------------------------------------------------------------
        if 'avoid' in self.__G.node[ root ]:        # if root must be avoided
            return -1, []                           # abort


        Q = queue.Queue()
        Q.put( root )                               # push root node to the queue

        while not Q.empty():                        # while there are unvisited nodes
            v = Q.get()                             # get front node

            if v in finals_d:                       # is current node in finals?            
                nleft -= 1      
                if nleft <= 0: break                # all final nodes have been found

            for n in self.__valid_neighbors( v ):   # for each neighbor node


                # TODO: exculde clobbering nodes
                
                # ignore nodes and edges that marked as "avoid"
                if 'avoid' in self.__G.node[ n ] or 'avoid' in self.__G[ v ][ n ]:
                    continue


                if n.addr not in visited:           # if not visited, push it to the queue

                    self.__backpointer[n.addr] = v  # set backpointer to the parent node
                    Q.put( n )                      # push node on queue

                    # set node's shortest path accordingly                  
                    visited[n.addr] = visited[v.addr] + 1 + self.__G[ v ][ n ].get('depth', 0)


        # -------------------------------------------------------------------------------
        # Search has finished. Extract paths
        # -------------------------------------------------------------------------------
        sp = []                                     # list of shortest paths

        for n in finals:                            # for each final node           
            path = []
            p = n
            
            while p > 0:                            # go all the way up to the root         
                path.insert(0, int(p.addr) )        # add node to the path (in reverse order)
                p = self.__backpointer.get(p.addr, -1)
                
                
            # if final node is not visited, set distance to -1
            sp.append( (visited.get(n.addr, -1), path) )
            
        return sp # return list of tuples



    # ---------------------------------------------------------------------------------------------
    '''



    # ---------------------------------------------------------------------------------------------
    # __depth_metric(): Determine the metric for measuring function's depth. This function tries
    #       to estimate the minimum number of distinct basic blocks that should be executed within 
    #       a function. To do that, one should look at the shortest paths from the entry point to
    #       all final basic blocks (those that end with a return instruction) and select as depth
    #       the length of the minimum of these (shortest) paths.
    #
    #       However this metric might not always work well, as it's very common to make argument 
    #       checks at the very early stages of a function and abort if they do not meet the 
    #       requirements.
    #   
    #       To fix that, this function offers 3 metrics: The minimum among the shortest paths, the
    #       maximum and the median of all shortest paths. We leave the final decision up to the 
    #       user.
    #
    # :Arg retns: A list of tuples (dist, path) that contains all shortest paths to a final block
    #             along with their distances
    # :Ret: Function's depth along with a path (if applicable).
    #
    def __depth_metric( self, retns ):
        if not len(retns): return 0, []

        # getting the median is tricky, so we have to sort all return paths first
        sorted_retns = sorted(retns[:], key=lambda x: x[0])

        if FUNCTION_DEPTH_METRIC == 'min':                   
            return sorted_retns[0]
        
        elif FUNCTION_DEPTH_METRIC == 'max':            
            return sorted_retns[-1]
        
        elif FUNCTION_DEPTH_METRIC == 'median':
            return sorted_retns[len(sorted_retns) >> 1]

        else:
            fatal("Invalid value for 'FUNCTION_DEPTH_METRIC'!")



    # ---------------------------------------------------------------------------------------------
    # __clob_stmts(): This function finds all SPL statements whose accepted blocks are clobbering
    #       with a given statement. This is essentially a Depth First Search (DFS) on the Reverse
    #       Adjacency list (self.__radj) starting from current statement. This is due to the time
    #       sensitivity of the clobbering blocks; thtat is a clobbering block becomes truly 
    #       clobbering *after* the execution of some SPL statement.
    #   
    # :Arg cur_uid: of Current statement's UID
    # :Ret: Function returns a set of all statement UIDs whose blocks are _effectively_ clobbering.
    #
    def __clob_stmts( self, cur_uid ):
        if not self.__clobbering:           # if clobbering blocks are ignored
            return set()                    # skip it

        if cur_uid != START_PC and cur_uid not in self.__radj:
            fatal("Statement with uid '%d' is not in the reverse adjacency list" % cur_uid)

        clobs = set()                       # clobbering (visited) statements
        stack = [cur_uid]                   # start from root

        while stack:
            curr = stack.pop()              # get top element of the stack

            if curr not in clobs:
                clobs.add(curr)             # mark it
                
                if curr in self.__radj:     # add reverse neighbors, if any (up to 2)
                    stack.extend( self.__radj[curr] )

        return clobs                        # return clobbering statement set


 
    # ---------------------------------------------------------------------------------------------
    # __dijkstra_variant_rcsv(): This is the recursive variant of Dijkstra's algorithm that we
    #       described above.
    #
    # :Arg root: node to start searching from
    # :Arg finals: a list of all target (final) nodes
    # :Arg precall_stack: Current precall stack
    # :Arg init_dist: Initial distance to start from (i.e., distance from initial root)
    # :Ret: Function return  two lists of tuples. The first list contains the length and the path
    #       path for each final node. The second list contains the length and the path for each
    #       return node.
    #
    def __dijkstra_variant_rcsv( self, root, finals=[], precall_stack=[], init_dist=0 ):
        nleft    = len(finals)                      # number of final nodes
        finals_d = dict((n,0) for n in finals)      # cast to dict to search in O(1)

        Q        = queue.PriorityQueue()            # implement it using a prioirty queue
        retn_s   = [ ]                              # return node set


        dbg_prnt(DBG_LVL_4, 'Starting recursive Dijkstra at: 0x%x (%s). Pre-call Stack: %s' % 
                 (root.addr, func_name (root.addr), pretty_list(precall_stack, ', ')))


        # if root is clobbering skip it (function is recursive, root may not be the top node)
        if 'clobbering' in self.__G.node[ root ]:
                return [(INFINITY, [])]*len(finals), [(INFINITY, [])]*len(finals)

        # if root node must be avoided (in the current context), or if it's already in the
        # Call Stack, return non-existing path(s).
        if 'avoid' in self.__G.node[root] and precall_stack == self.__G.node[root]['avoid'] or \
            root in self.__callstack:
                return [(INFINITY, [])]*len(finals), [(INFINITY, [])]*len(finals)


        self.__callstack[root] = 1
        self.__dist[root]      = init_dist          # distance from root 


        # when function has multiplee callers, just keep the 1st one for the shortest path
        if root not in self.__backpointer:
            self.__backpointer[root] = -1           # root has no parent


        # -------------------------------------------------------------------------------
        # Main Dijkstra loop
        # -------------------------------------------------------------------------------
        Q.put(_queue_obj(root, self.__dist[root]))  # add root to the queue

        while not Q.empty():                        # while there are vertices in the queue
            u = Q.get().data                        # get front node's data

        
            # print node with minimum cost
            if self.__backpointer[u] == -1: n, a = '-1', 0xffffffff
            else: n, a = self.__backpointer[u].name, self.__backpointer[u].addr

            dbg_prnt(DBG_LVL_4, "\tSelect min: %3d 0x%x (%s)\t<-- 0x%x (%s)" % 
                                    (self.__dist[u], u.addr, u.name, a, n))


            # In practise, paths lengths are not longer than MAX_ALLOWED_SUBPATH_LEN, as
            # it's highly unlikely to have satisfiable constraints. Therefore we stop once
            # a path reaches its upper bound, to boost our algorithm.
            if self.__dist[u] > MAX_ALLOWED_SUBPATH_LEN:
                continue                            # discard current path


            if u in finals_d:                       # is current node in finals?                       
                nleft -= 1
                if nleft <= 0: break                # all final nodes have been found

            if u.has_return: retn_s.append(u)       # returns nodes are needed too



            # check all (valid) neighbors for the current node
            for v in self.__valid_neighbors( u ):

                # -----------------------------------------------------------------------
                # Is current block a caller?
                # -----------------------------------------------------------------------
                if isinstance(v, tuple) and v[1] == 'caller':

                    # ignore clobbering nodes
                    if 'clobbering' in self.__G.node[ v[0] ]:
                            continue

                    # ignore nodes and edges that marked as "avoid"                
                    if 'avoid' in self.__G.node[v[0]] and precall_stack == self.__G.node[v[0]]['avoid'] or \
                       'avoid' in self.__G[u][v[0]]   and precall_stack == self.__G[u][v[0]]['avoid']:
                            continue

                  
                    # if function is not yet analyzed
                    if v[0] not in self.__funcdepth:            
                        # It is possible that the function is not in __funcdepth but it is still
                        # visited. This happens when 1) function is recursive or 2) function was
                        # invoked through a jmp before the call. For instance:
                        #   
                        #        .text:0000000000410FC0 cipher_decrypt  proc near
                        #        .....
                        #        .text:0000000000411021        mov     context, [rsp+1A8h+var_10]
                        #        .text:0000000000411029        mov     src, [rsp+1A8h+var_8]
                        #        .text:0000000000411031        add     rsp, 1A8h
                        #        .text:0000000000411038        jmp     _memcpy        
                        #
                        #        .plt:0000000000403A70 _memcpy         proc near
                        #        .plt:0000000000403A70        jmp     cs:off_621528
                        #
                        #
                        # In both cases, we don't touch the function if its root is already visited
                        if self.__dist[v[0]] <= self.__dist[u] + 1:
                            continue


                        # set distance to the root node
                        self.__dist[v[0]]        = self.__dist[u] + 1
                        self.__backpointer[v[0]] = u


                        # Recursively call Dijkstra for the new function
                        F, R = self.__dijkstra_variant_rcsv(v[0], finals, precall_stack + [u.addr], 
                                                            self.__dist[u] + 1)

                        # estimate function's depth
                        #
                        # Note that if function has no returns, then cost will be 0 and P may not
                        # be applicable
                        cost, P = self.__depth_metric(R)
                        self.__funcdepth[ v[0] ] = (cost, P)


                        # All return paths have now their backpointers set. 
                        # We select P as return path (according to __depth_metric)
                        R = [(cost, P)]

                        
                        dbg_arb(DBG_LVL_4,  '\tF set:', [(f[0], pretty_list(f[1])) for f in F])
                        dbg_arb(DBG_LVL_4,  '\tR set:', [(r[0], pretty_list(r[1])) for r in R])
                        dbg_prnt(DBG_LVL_4, '\tP set: %s' % pretty_list(P))
                        dbg_prnt(DBG_LVL_4, "\tFunction '%s' has depth %d" % (v[0].name, cost))

                    else:
                        R = []                      # in that case, R is empty
                        
                        # is function is already analyzed, just use its paths
                        # (+1 to jump the function and +1 to return from it)

                        if v[2] != -1:              # check if there's an edge
                            self.__G[ u ][ v[2] ]['depth'] = self.__funcdepth[ v[0] ][0] +1 +1
                            self.__G[ u ][ v[2] ]['path']  = self.__funcdepth[ v[0] ][1]


                    # -------------------------------------------------------------------
                    # at this point, __funcdepth is set (unless dist[v[0]] <= dist[u]+1)
                    # -------------------------------------------------------------------
                    try:
                        altd = self.__dist[u] + 1 + self.__funcdepth[ v[0] ][0] + 1
                    except KeyError:
                        altd = INFINITY             # function root is visited but depth is unknown



                    # if there's no return, skip this edge
                    if v[2] == -1:
                        warn("Caller 0x%x (%s) has no return" % (v[0].addr, v[0].name), DBG_LVL_4)
                        continue

                    # v[2] may also be clobbering
                    if 'clobbering' in self.__G.node[ v[2] ]:
                            continue

                    if altd < self.__dist[v[2]]:    # if alternative path is shorter, ute it
                        self.__dist[v[2]]        = altd
                        self.__backpointer[v[2]] = u
                        
                        Q.put(_queue_obj(v[2], altd))


                        # Now go back and fix backpointers
                        #
                        # it might be possible to not have this edge in the CFG. For example:
                        # 
                        #       .text:000000000040E00D         mov     rdi, ch_0
                        #       .text:000000000040E010         call    chan_write_failed
                        #       .text:000000000040E015         mov     ecx, [ch_0+10h]
                        #
                        #       .text:00000000004124E0 chan_write_failed proc near
                        #       .text:0000000000412552         jmp     chan_delete_if_full_closed
                        #
                        #       .text:00000000004122E0 chan_delete_if_full_closed proc near
                        #       .text:000000000041230C         jmp     channel_free
                        #   
                        #       .text:000000000040DA30 channel_free proc near
                        #       .text:000000000040DAD2         pop     rbx
                        #       .text:000000000040DAD3         retn
                        #        
                        # Here, returning from channel_free(), should bring us to 0x40e015, however
                        # this edge may not be exists. Therefore we need to add an 'Ijk_Ret' edge.
                        if R:
                            for _, retn in R:
                                for a, b in to_edges(retn, direction='backward'):                               
                                    self.__backpointer[ADDR2NODE[a]] = ADDR2NODE[b]
                                
                                if len(retn) > 1:   # fix the last backpointer
                                    self.__backpointer[v[2]] = ADDR2NODE[a]

                                    # add the edge (if not exists)
                                    if not self.__G.has_edge(ADDR2NODE[a], v[2]):
                                        self.__G.add_edge(ADDR2NODE[a], v[2], jumpkind='Ijk_Ret')


                            # This is not needed as we start distances from init_dist
                            #   for r in retn[1:]:
                            #       self.__dist[ ADDR2NODE[r] ] += self.__dist[u] + 1;


                # -----------------------------------------------------------------------
                # Block is not a caller
                # -----------------------------------------------------------------------
                else:       
                    # if node is clobbering skip it
                    if 'clobbering' in self.__G.node[v]:
                            continue

                    # ignore nodes and edges that marked as "avoid"
                    if 'avoid' in self.__G.node[v] and precall_stack == self.__G.node[v]['avoid'] or \
                       'avoid' in self.__G[u][v]   and precall_stack == self.__G[u][v]['avoid']:
                            continue

                    # Although we handle this case pretty well, we still highlight it
                    if u.addr in ADDR2FUNC and v.addr in ADDR2FUNC and ADDR2FUNC[u.addr] != ADDR2FUNC[v.addr]:
                        warn("Node 0x%x (%s) transfers control to '%s'" %
                                (u.addr, u.name, ADDR2FUNC[v.addr].name), DBG_LVL_4)
                        
            
                    # check if the alternative path is better
                    altd = self.__dist[u] + 1
                    if altd < self.__dist[v]:       # if alternative path is shorter, use it
                        self.__dist[v]        = altd
                        self.__backpointer[v] = u
                        
                        Q.put(_queue_obj(v, altd))  # and add it to the queue


        # pop current function from Call Stack before return
        del self.__callstack[root]


        # -------------------------------------------------------------------------------
        # Search has finished. Extract paths
        # -------------------------------------------------------------------------------       
        dbg_prnt(DBG_LVL_4, 'Leaving recursive Dijkstra at 0x%x (%s). Return Set: %s' % 
                                (root.addr, root.name, pretty_list(retn_s, ', ')))



        # -------------------------------------------------------------------------------
        # extr_paths(): This internal function extracts all paths from the return blocks
        #       to the root, using the backpointers.
        #
        # :Arg final_blks: A set of all basic blocks that have a return instruction
        # :Ret: Function
        #
        def extr_paths( final_blks ):
            paths = []                              # list of shortest paths            

            for n in final_blks:                    # for each final node
                path  = []
                p     = n
                found = False

                dbg_prnt(DBG_LVL_4, "\tExtracting (reverse) path from 0x%x to 0x%x" %  
                                            (n.addr, root.addr))
        
                while p > 0:                        # go all the way up to the root                        
                    dbg_prnt(DBG_LVL_4, "\t\t%3d 0x%x (%s)" % (self.__dist.get(p, -1), p.addr, p.name))                 


                    path.insert(0, int(p.addr) )    # add node to the path (in reverse order)

                    if p == root:                   # if you reach root, stop
                        found = True
                        break
               
                    if p in path:                   # cycles will make loop infinite
                        fatal('Backpointers contain a loop. Abort')

                    p = self.__backpointer.get(p, -1)

                  
                # if final node is not visited or root is not found, set distance to -1                
                if not found:
                    distance = INFINITY
                else:               
                    distance = self.__dist.get(n, INFINITY)
                    if distance != -1 and distance != INFINITY:
                         distance -= init_dist

                dbg_prnt(DBG_LVL_4, "\t\tFinal Distance: %d (Initial Distance: %d)" % 
                                        (distance, init_dist))

                # append path to the shortest path list             
                paths.append( (distance, path if distance < INFINITY else []) )                    


            return paths



        # -------------------------------------------------------------------------------

        return extr_paths(finals), extr_paths(retn_s)
    


    # ---------------------------------------------------------------------------------------------
    # __dijkstra_variant(): This function essentially bootstraps the recursive Dijsktra algorithm.
    #
    # :Arg root: node to start from searching
    # :Arg finals: a list of all target nodes
    # :Arg cur_uid: Current statement's UID
    # :Arg precall_stack: Current precall stack
    # :Ret: A list of tuples with the length and the path for each final node.
    #
    def __dijkstra_variant( self, root, finals=[], cur_uid=-1, precall_stack=[] ):
        self.__dist        = { }                    # visited nodes
        self.__backpointer = { }                    # backpointers      
        self.__callstack   = { }                    # call "stack" to prevent infinite recursions
        self.__funcdepth   = { }                    # function depths 


        clobs = self.__clob_stmts(cur_uid)          # set of clobbering block UIDs to avoid


        # UPDATE: Yes they are. Think about calls with clobbering arguments ;)
        #
        #   # the first and last nodes are never clobbering
        #   nonclob = [root.addr] + [final.addr for final in finals]

        # exclude clobbering blocks from search (mark them so they can be avoided)
        for addr, uidlist in self.__clobbering.iteritems():            
            # if addr not in nonclob and not disjoint(set(uidlist), clobs):
            if not disjoint(set(uidlist), clobs):
                self.__G.node[ ADDR2NODE[addr] ]['clobbering'] = 1
               
        
        # initialize all node distances to INF
        for vtx, _ in self.__G.nodes_iter(data=True):
            self.__dist[vtx]        = INFINITY
            self.__backpointer[vtx] = -1


        try:
            # get shortest paths to all final nodes (ignore the return nodes)
            paths, _ = self.__dijkstra_variant_rcsv(root, finals, precall_stack=precall_stack)
        except Exception, e:                        # just in case that something goes wrong                       
            traceback.print_exc()                   # print exception trace
            fatal('Unexpected exception in __dijkstra_variant_rcsv(): %s' % str(e))


        # print function depths (DBG_LVL_4 only)        
        dbg_prnt(DBG_LVL_4, '\tFunction Depths:')

        for func, (depth, path) in self.__funcdepth.iteritems():
            dbg_prnt(DBG_LVL_4, '%32s: %2d (%s)' % (func.name, depth, pretty_list(path)))


        # print path(s) to the user (DBG_LVL_3 and DBG_LVL_4 only)
        for final, path in zip(finals, paths):

            if path[0] != INFINITY:
                dbg_prnt(DBG_LVL_3, "\tShortest Path (%x -> %x) found (%d): %s" % 
                                    (root.addr, final.addr, path[0], pretty_list(path[1], ' -> ')))

            else:
                dbg_prnt(DBG_LVL_4, "\tNo Shortest Path (%x -> %x) found!" % 
                                    (root.addr, final.addr))

        # clean up clobbering nodes
        for node, _ in nx.get_node_attributes(self.__G, 'clobbering').items(): 
            del self.__G.node[ node ]['clobbering']                  


        return paths                                # return shortest paths (1 for each final node)



    # ---------------------------------------------------------------------------------------------
    # __spur_shortest_path(): This function finds the shortest path between spur and destination
    #       nodes. Function first finds the shortest path using __dijkstra_variant() and then
    #       calculates the spur path lengths and the expanded spur paths. This information is
    #       needed for k_shortest_paths(), because 'depth' attributes are cleared every time we
    #       calculate a spur path and hence it becomes impossible to calculate the length of a
    #       subpath. Therefore we precalculate all the lengths for all subpaths from root to the
    #       i-th node, in order to reuse them later on in k_shortest_paths().
    #
    # :Arg spur: Spur node
    # :Arg dst: Destination node (must be exactly one)
    # :Arg precall_stack: Current precall stack
    # :Ret: If a shortest path exists, function returns a tuple (path, pathlens, expaths) that
    #       contains the path, the spur path lengths and the expanded spur paths. Otherwise,
    #       function returns a tuple with pathlens being set to [-1].
    #
    def __spur_shortest_path( self, spur, dst, cur_uid=-1, precall_stack=[] ):
        # ---------------------------------------------------------------------
        # Clear leftovers in CFG from previous calls. 
        #
        # This is an important step as 'depths' for the same function can vary
        # depending on the root and/or the current state of the algorithm.  As 
        # an example consider the  case where we have a set of functions whose
        # call graph is fully connected (i.e., a very weird form of recursion).
        # In this case the 'depth' of each function depends on the initial entry
        # point.
        # ---------------------------------------------------------------------
        for n, _ in nx.get_edge_attributes(self.__G, 'depth').items():
            del self.__G.edge[ n[0] ][ n[1] ]['depth']

        for n, _ in nx.get_edge_attributes(self.__G, 'path').items():
            del self.__G.edge[ n[0] ][ n[1] ]['path']


        # ---------------------------------------------------------------------
        # Find the shortest (context sensitive) path
        # ---------------------------------------------------------------------        
        paths = self.__dijkstra_variant(ADDR2NODE[spur], [ADDR2NODE[dst]], cur_uid, precall_stack)
        length, path = paths[0]

        if len(paths) != 1:                         # this should never happen
            fatal('__spur_shortest_path() should work with a single path')

        if length == INFINITY:                      # if path doesn't exist, abort
            return ([], [-1], [])


        # ---------------------------------------------------------------------
        # Calculate the spur path lengths and the expanded spur paths
        #
        # pathlens[i] has the length of the shortest subpath "path[:i]"
        # expaths[i] has the expanded shortest subpath "path[:i]"
        # ---------------------------------------------------------------------
        spurlen  = 0
        expath   = [path[0]]
        pathlens = [0]        
        expaths  = [expath[:]]
        

        for u, v in to_edges(path):                 # for every edge on the path
            # Edge (u,v) may not exists (due to indirect jumps). For instance:
            #
            #       .text:000000000040589F        call    xfree
            #       .text:00000000004058A4 loc_4058A4:
            #
            #       .text:0000000000415260 xfree           proc near
            #       .....
            #       .text:000000000041526D        jmp     _free
            #
            #       .plt:00000000004034B0 _free           proc near
            #       .plt:00000000004034B0        jmp     cs:off_621248
            #            
            # In that case, we simply increase length by 1
            if not self.__G.has_edge(ADDR2NODE[u], ADDR2NODE[v]):
                edge_data = { }                     # assign an empty dictionary
            else:
                edge_data = self.__G.edge[ ADDR2NODE[u] ][ ADDR2NODE[v] ]


            # update spurlen (get depth edge if exists)
            spurlen += edge_data.get('depth', 1)
            pathlens.append( spurlen )

            # update expanded paths. Append path (if exists) and the new node
            # (it's important to use [:] to create a copy of expath)
            expath += edge_data.get('path', []) + [v]
            expaths.append(expath[:])


        # The expanded path should have as many nodes as the total length
        #
        # However this is not always true, because the expanded path may not be so "expanded"
        # The only problem with that, is that we my return the same path >1 times
        #
        #       if spurlen != len(expath) - 1:
        #           fatal("Something is wrong with 'expath' in __spur_shortest_path()")


        # The last element of pathlens list is the total path length
        if length != pathlens[-1]:          
            # This may occur, when we have an unresolvable function (eval/sudo/sudo):
            #
            #       .text:000000000040F5A5         test    rbp, rbp
            #       .text:000000000040F5A8         jz      short loc_40F5C6
            #       .text:000000000040F5AA         xor     ebx, ebx
            #       .text:000000000040F5AC         nop     dword ptr [rax+00h]
            #       .text:000000000040F5B0
            #       .text:000000000040F5B0 loc_40F5B0:
            #       .text:000000000040F5B0         mov     rdx, r15
            #       .text:000000000040F5B3         mov     rsi, r14
            #       .text:000000000040F5B6         mov     edi, r13d
            #       .text:000000000040F5B9         call    qword ptr [r12+rbx*8]
            #       .text:000000000040F5BD         add     rbx, 1
            #       .text:000000000040F5C1         cmp     rbx, rbp
            #       .text:000000000040F5C4         jnz     short loc_40F5B0
            #       .text:000000000040F5C6
            #       .text:000000000040F5C6 loc_40F5C6:
            #       .text:000000000040F5C6         mov     rbx, [rsp+38h+var_30]
            #       .text:000000000040F5CB         mov     rbp, [rsp+38h+var_28]
            #       .text:000000000040F5D0         mov     r12, [rsp+38h+var_20]
            #       .text:000000000040F5D5         mov     r13, [rsp+38h+var_18]
            #       .text:000000000040F5DA         mov     r14, [rsp+38h+var_10]
            #       .text:000000000040F5DF         mov     r15, [rsp+38h+var_8]
            #       .text:000000000040F5E4         add     rsp, 38h
            #       .text:000000000040F5E8         retn
            #
            # Here, "call qword ptr [r12+rbx*8]" does not really go anywhere, however the distance
            # from 0x40F5B0 to 0x40F5BD is 2. This happens when we visit a function with length <1.
            #
            #       fatal("Something is wrong with 'pathlens' in __spur_shortest_path()")
            pass

        return (path, pathlens, expaths)            # return spur path



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor.
    #
    # :Arg graph: CFG to work on
    #
    def __init__( self, cfg, clobbering={ }, adj={ } ):
        self.__G          = cfg.graph               # store arguments internally
        self.__clobbering = { }                     # clobbering blocks


        self.__radj = mk_reverse_adj(adj)           # build the reverse adjacency list

        # build a suitable dictionary with clobbering blocks
        for uid, addrs in clobbering.iteritems():
            for addr in addrs:
                self.__clobbering.setdefault(addr, []).append(uid)
       

        super(self.__class__, self).__init__(       # call parent class
            self.__G, 
            self.__spur_shortest_path, 
            lambda node : ADDR2NODE[node]           # transform address index to "node" object 
        )



    # ---------------------------------------------------------------------------------------------
    # shortest_path(): Find the shortest path (with respect to CFG) from a single source to a
    #       destination (destinations can be >1). This function is pretty much a wrapper for
    #       __dijkstra_variant()
    #
    # :Arg src: Source node
    # :Arg dst: Destination node(s)
    # :Arg cur_uid: Current UID of the SPL statement
    # :Ret: A list of tuples with the length and the path for each final node. If addresses are
    #   not valid function returns an empty list.
    #
    def shortest_path( self, src, dst, cur_uid=-1 ):
        if not isinstance(dst, int): single = 0
        else: single = 1; dst = [dst]               # make single destination a list


        try:
            # sp = self.__bfs_variant(ADDR2NODE[src], [ADDR2NODE[d] for d in dst])
            sp = self.__dijkstra_variant(ADDR2NODE[src], [ADDR2NODE[d] for d in dst], cur_uid)

            return sp[0] if single else sp          # if there's 1 path, return a tuple

        except KeyError as val:        
            sp = [(INFINITY, [])]*len(dst)          # failure

            warn("CFG does not have a basic block at address %s (decimal)" % val )
            return sp[0] if single else sp



    # ---------------------------------------------------------------------------------------------
    # shortest_loop(): Find the shortest loop (with respect to CFG) starting from a single source 
    #       The cycle is context sensitive, so we have to use __dijkstra_variant(). To find a loop,
    #       all we have to do, is to find the shortest path from the source to all of its
    #       predecessors and then add one more edge to create a cycle.
    #
    #       Here's a good a example of context sensitivity in cycles:
    #
    #           .text:0000000000404EDB         xor     ebx, ebx
    #           .text:0000000000404EDD         nop     dword ptr [rax]
    #           .text:0000000000404EE0
    #           .text:0000000000404EE0 loc_404EE0:
    #           .text:0000000000404EE0         mov     edi, ds:listen_socks[rbx*4] ; fd
    #           .text:0000000000404EE7         call    _close
    #           .text:0000000000404EEC         lea     eax, [rbx+1]
    #           .text:0000000000404EEF i = rax                                 ; int
    #           .text:0000000000404EEF         add     rbx, 1
    #           .text:0000000000404EF3         cmp     cs:num_listen_socks, eax
    #           .text:0000000000404EF9         jg      short loc_404EE0
    #
    #           .plt:0000000000403160 _close  proc near
    #           .plt:0000000000403160         jmp     cs:off_6210A0
    #
    #       In the above code, there's a cycle: 404eec - 404ee0 - 403160 - 10000a0 - 404eec.
    #       However, if we start searching from 0x403160, we will find no cycle, as we're in a
    #       different context (we don't know where to return from 0x10000a0).
    #
    # :Arg src: Source node
    # :Arg cur_uid: Current UID of the SPL statement
    # :Ret: A tuple with the length and the actual cycle. If a cycle does not exists function 
    #       returns an empty list.
    #
    def shortest_loop( self, src, cur_uid=-1 ):
        try:
            # find all predecessor blocks
            predecessors = [pred for pred in ADDR2NODE[src].predecessors]

            # if there are no predecessors, there are no cycles ;)
            if not predecessors: 
                return (INFINITY, [])


            # find shortest path from source to all predecessors
            sp = self.__dijkstra_variant(ADDR2NODE[src], predecessors, cur_uid)

            # find the shortest among the shortest paths          
            dists = [dist for dist, _ in sp]                  
            idx   = dists.index(min(dists))         # index of the minimum


            if sp[idx][0] == INFINITY:
                cycle = (INFINITY, [])
            else:
                # add the predecessor edge to form a cycle
                # TODO: check if the predecessor edge is in the same context
                cycle = (sp[idx][0] + 1, sp[idx][1] + [src])


            del sp                                  # we don't need you anymore

            return cycle                            # return the shortest loop

        except KeyError as val:        
            warn("CFG does not have a basic block at address %s (decimal)" % val )

            return [(INFINITY, [])]                 # failure



# -------------------------------------------------------------------------------------------------
'''
if __name__ == '__main__':                          # DEBUG ONLY
    set_dbg_lvl( DBG_LVL_0 )


    import angr
    
    project = angr.Project('eval/proftpd/proftpd', load_options={'auto_load_libs': False})    
    CFG     = project.analyses.CFGFast()
    CFG.normalize()

    # create a quick mapping between addresses and nodes (basic blocks)
    for node in CFG.graph.nodes():
        ADDR2NODE[ node.addr ] = node


    # create a quick mapping between basic block addresses and their corresponding functions
    for _, func in CFG.functions.iteritems():
        for addr in func.block_addrs:
            ADDR2FUNC[ addr ] = func


    p = _cfg_shortest_path(CFG)


    paths = []


    # avoid some node
    # CFG.graph.node[ ADDR2NODE[0x4058A4] ]['clobbering'] = 1

    # for ll, pp in p.shortest_path(0x405897, [0x40c8f0]):    
    # for ll, pp in p.k_shortest_paths(0x40f5a5, 0x40f5c6, 0, PARAMETER_P): # sudo
    # for ll, pp in p.k_shortest_paths(0x412c98, 0x40c8f0, 0, PARAMETER_P): # openssh
    

    #for ll, pp in p.k_shortest_paths(0x42acf0, 0x42ad5e, 0, 2): # openssh
    for ll, pp in p.k_shortest_paths(0x406806, 0x42ad5e, 0, 10): # openssh

    #for ll, pp in p.k_shortest_loops(0x4043f5, 0, PARAMETER_P):   # openssh
        print '%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'
        print 'Path (%d): %s' % (ll, pretty_list(pp))

        paths.append( (ll, pp) )

    print 'Printing all paths:'
    for ll, pp in paths:
        print 'Path (%d): %s' % (ll, pretty_list(pp))


    print '\n\n\n******************************************************\n\n\n'

    for ll, pp in p.k_shortest_paths(0x42acf0, 0x42ad5e, 0, 10): # openssh
    

    #for ll, pp in p.k_shortest_loops(0x4043f5, 0, PARAMETER_P):   # openssh
        print '%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'
        print 'Path (%d): %s' % (ll, pretty_list(pp))

        paths.append( (ll, pp) )


    print 'Printing all paths:'
    for ll, pp in paths:
        print 'Path (%d): %s' % (ll, pretty_list(pp))


'''

# TODO: FIX MEEEEE!!!!!!!!!!!!!
# BAD LOOP (mod: 0, set: 2) 40b277 - 40b28f - 402a40 - 10003c0 - 40b299 - 40b2b6 - 
#                           40b2e5 - 40b2eb - 402a80 - 10003e0 - 40b277


# -------------------------------------------------------------------------------------------------

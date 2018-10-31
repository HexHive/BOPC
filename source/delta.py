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
# delta.py:
#
# This module is also the "assistant" of the symbolic execution engine along with the path module.
# It implements the Delta Graph (DG). More details on the paper :)
#
# -------------------------------------------------------------------------------------------------
from coreutils import *
import path as P

import networkx as nx
import queue
import heapq



# ------------------------------------------------------------------------------------------------
# Constant Definitions
# ------------------------------------------------------------------------------------------------
# _NULL_NODE = -1                                     # null (non-existent) node
_SINK_NODE = 0                                      # the sink node in delta graph
    


# -------------------------------------------------------------------------------------------------
# _delta(): This class creates and processes the delta graph. Delta graph shows the distances 
#   (deltas) between accepted blocks.
#
class delta( P._cs_ksp_intrl ):
    ''' ======================================================================================= '''
    '''                                   INTERNAL FUNCTIONS                                    '''
    ''' ======================================================================================= '''
        
    # ---------------------------------------------------------------------------------------------
    # __dijkstra_av(): This function finds the shortest path between source and destination 
    #       vertices using Dijkstra's algorithm. What's special about this algorithm, is that it
    #       avoids all vertices and edges that have the "avoid" attribute set. 
    #
    # :Arg src: The source node
    # :Arg dst: The destination node
    # :Ret: A tuple (dist, path) that contains the shortest distance and the shortest path as a 
    #   list of vertices. If such a path does not exist, function retuns (-1, []).
    #
    def __dijkstra_av( self, src, dst, extra=None ):
        Q = queue.PriorityQueue()                   # implement it using a prioirty queue
        dist, prev = { }, { }                       # intialize maps        
        

        if 'avoid' in self.__d.node[ src ]:         # if source vertex must be avoided,
            return -1, []                           # abort


        for vtx, _ in self.__d.nodes_iter(data=True):
            if vtx != src:                          # for all vertices except source
                dist[vtx], prev[vtx] = INFINITY, -1 # initialize distances to INF
 

        # TODO: REPLACE PRIORITY QUEUE OBJECTS
        dist[src], prev[src] = 0, _NULL_NODE        # source has distance 0
        Q.put(src, dist[src])                       # add source vertex to the queue        
    
        ''' ------------------------------------------------------------------------- '''
        ''' Main loop                                                                 '''
        ''' ------------------------------------------------------------------------- '''
        while not Q.empty():                        # while there are vertices in the queue
            u = Q.get()                             # extract best vertex

            if u == dst:                            # destination vertex found?
                path, v = [], u                     # initialize vars
                                
                while v != _NULL_NODE:              # repeat until you reach the source
                    path.insert(0, v)               # add vertex in reverse order
                    v = prev[v]                     # move backwards

                return dist[u], path                # success! return (dist,path)
                

            for v in self.__d.neighbors(u):         # for each adjacent vertex

                # if this vertex or its edge must to be avoided, skip it
                if 'avoid' in self.__d.node[ v ] or 'avoid' in self.__d[ u ][ v ]:
                    continue


                altd = dist[u] + self.__d[u][v]['weight']               
                if altd < dist[v]:                  # if alternative path is shorter
                    dist[v] = altd                  # use it
                    prev[v] = u
                    
                    Q.put( v, altd )                # and add it to the queue


        return -1, []                               # no path. Failure

    '''
    # ---------------------------------------------------------------------------------------------
    # __cost(): Calculate the cost of a given path.
    #
    # :Arg path: Path to work on
    # :Ret: An integer containing path's distance (cost).
    #
    def __cost( self, path ):
        cost = 0
    
        if len(path) > 1:
            for i in range(len(path) - 1):          # for each vertex in the path                           
                cost += self.__d.edge[ path[i] ][ path[i + 1] ]['weight']

        return cost
    '''
    
    # ---------------------------------------------------------------------------------------------
    # maxheap_obj: This class represents maximum-heap objects
    # ---------------------------------------------------------------------------------------------
    class __maxheap_obj( object ):
        def __init__( self, tw, Hk ):           # store total weight and induced subgraph
            self.tw = tw; self.Hk = Hk
        
        def __eq__( self, obj ):                # == operator: Compare total weights
            return self.tw == obj.tw
        
        def __lt__( self, obj ):                # < operator: Invert condition
            return self.tw > obj.tw             # with this trick min-heap becomes max-heap



    # ---------------------------------------------------------------------------------------------
    # __enum_induced_subgraphs(): Enumerate all induced subgraphs with k nodes. Keep track of the
    #   K minimum subgraphs by storing them on a max-heap. This function is recursive.
    #
    #   NOTE /!\: Although this function has an exponential worst case complexity, in practice,
    #       delta graphs are sparse so many of the combinations are truncated at the early stages.
    #       In other words, this function is fast in practice.
    #
    # :Arg depth: The current recursion depth
    # :Arg V: The current set of nodes that constitute the induced subgraph
    # :Ret: None.
    #
    #
    #   
    # TODO: Optimization: When delta graph is flat, use Dijkstra
    # 
    def __enum_induced_subgraphs( self, depth, V ):
        # ---------------------------------------------------------------------
        if depth == len(self.__bound):              # do we have a k-node induced subgraph      
            Hk = nx.DiGraph()                       # Create the induced subgraph
            Hk.add_nodes_from( V )

            Vs = set(V)                             # cast list to set to optimize searching
            tw = 0

            # iterate over edges in __G and keep those who have both edges in the subgraph
            for (u, v, w) in self.__G.edges_iter(data='weight'):
                if u in Vs and v in Vs:

                    # Induced subgraph nodes are indexed using (uid, addr) tuples
                    Hk.add_edge(u, v, visited=False)
                    tw += w                         # update total weight
                    
            if tw >= INFINITY:                      # discard subgraphs with INFINITY-weight edges
                return 0

            dbg_arb(DBG_LVL_3, "Induced subgraph (Total Weight: %2d) found" % tw, V)


            if self.__k > 0:                        # if heap doesn't have enough subgraphs
                heapq.heappush(self.__heap, self.__maxheap_obj(tw,Hk))
                self.__k -= 1
            else:                                   # otherwise keep the K minimum weight subgraphs
                if self.__heap[0].tw >= tw:
                    heapq.heappushpop(self.__heap, self.__maxheap_obj(tw,Hk))


            # Enumerating all induced subgraphs can take O(2^n) time. Although we truncated many
            # solutions, the worst case complexity is still remains.
            #
            # Therefore, if we hit an upper bound we simply stop the enumeration

            self.__inc_ctr += 1
            if MAX_ALLOWED_INDUCED_SUBGRAPHS != -1 and \
                self.__inc_ctr >= MAX_ALLOWED_INDUCED_SUBGRAPHS:
                    return -1                           # maximum number of tries reached

            return 0



        # we always start from depth 1 (we have a single entry point)
        cur = V[depth - 1]
        uid = self.__uid[depth]


        # ---------------------------------------------------------------------
        for n in range(self.__bound[depth]):        # for each block in the current depth

            # At this point we should check whether the selected node has an non-infinity
            # distance with the others. This check is crucial as it can quickly eliminate
            # most of the induced subgraphs.
            #
            # TODO: Elaborate.
            #

            nxt = self.__node_groups[depth][1][n]

            #print self.__uid[depth], (cur, nxt)
            #print self.__adj[ uid ]
            #print self.__radj[ self.__uid[depth] ]

            discard = False


            # To problem here is the non-linearity. Although we're moving from depth X to X+1,
            # it doesn't means that we're going from statement X to X+1.
            #
            # The idea is when add node X+1, to check whether all incoming edges (from already 
            # visited nodes) have non-infinity cost and whether all outgoing edges (from already 
            # visited nodes too) have non-infinity cost as well
            #

            if uid in self.__radj:                  # do the same with incoming edges
                for x in self.__radj[ uid ]:
                    y = self.__uid.index(x)

                    if y >= depth:
                        continue


                    if not self.__G.has_edge(V[y], (uid,nxt)) or \
                        self.__G.get_edge_data(V[y], (uid,nxt))['weight'] == INFINITY:

                            discard = True          # discard current solution
                            break

            if uid in self.__adj and not discard:   # check outgoing edges
                for x in self.__adj[ uid ]:         # for each neighbor of of the next node
                    y = self.__uid.index(x)         # check if it's already in visited

                    if y >= depth:                  # TODO: >= or > ?
                        continue                    # skip if not

                    if not self.__G.has_edge((uid,nxt), V[y]) or \
                        self.__G.get_edge_data((uid,nxt), V[y])['weight'] == INFINITY:
                            discard = True
                            break


            # if self.__G.get_edge_data(V[depth], 
            #                           self.__node_groups[depth][1][nxt])['weight'] != INFINITY:
            if not discard:                
                # recursively move on
                if self.__enum_induced_subgraphs(depth + 1, V + [(uid,nxt)]) < 0:
                    warn('Maximum number of induced subgraphs has been reached. '
                         'Much Sad. Giving up recursing')
                    return -1                       # quickly escape from recursions

            # Node didn't work out. Try another one.

        return 0



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor. Create delta graph delta(CFG, M_v)
    #
    # :Arg graph: CFG to work on
    # :Arg entry: Payload's entry point
    # :Arg accepted: Dictionary of accepted blocks
    # :Arg clobbering: Dictionary of clobbering blocks
    # :Arg adj: Dictionary of the adjacency lists for accepted blocks
    #
    def __init__( self, graph, entry, accepted, clobbering, adj):
        """
        # A sample graph to test things

        self.__G = nx.DiGraph()
        self.__G.add_nodes_from( ['e', 'A1', 'B1', 'B2', 'B3', 'C1', 'D1', 'D2'] )

        self.__G.add_edge( 'e',  'A1', weight=0)
        self.__G.add_edge( 'A1', 'B1', weight=30)
        self.__G.add_edge( 'A1', 'B2', weight=2)
        self.__G.add_edge( 'A1', 'B3', weight=4)

        self.__G.add_edge( 'B1', 'C1', weight=1)
        self.__G.add_edge( 'B2', 'C1', weight=2)
        self.__G.add_edge( 'B3', 'C1', weight=3)

        self.__G.add_edge( 'C1', 'D1', weight=2)
        self.__G.add_edge( 'C1', 'D2', weight=1)

        self.__G.add_edge( 'D1', 'A1', weight=5)        
        self.__G.add_edge( 'D2', 'A1', weight=4)
        self.__G.add_edge( 'D2', 'B2', weight=1)

        self.__G.add_edge( 'D1', 'B1', weight=INFINITY)
        self.__G.add_edge( 'D1', 'B2', weight=INFINITY)
        self.__G.add_edge( 'D1', 'B3', weight=INFINITY)
        self.__G.add_edge( 'D2', 'B1', weight=INFINITY)
        self.__G.add_edge( 'D2', 'B3', weight=INFINITY)

        self.__node_groups = accepted

        # if you use the sample graph, use these node groups
        self.__node_groups = [(0, ['e']), (6, ['A1']), (8, ['B1', 'B2', 'B3']), (10, ['C1']), 
                                (14, ['D1', 'D2'])]

        adj       = { }
        adj[0 ]   = [6]
        adj[ 6 ]  = [8]
        adj[ 8 ]  = [10]
        adj[ 10 ] = [14]
        adj[ 14 ] = [6, 8]

        # self.__G.node['C']['avoid'] = 1
        print self.__G.edges()  
        print accepted
        print adj

        self.__entry = 'e'
        self.__adj   = adj                          # store adjacency list

        return

        """
        dbg_prnt(DBG_LVL_1, "Creating Delta Graph...")


        assert(MAX_ALLOWED_INDUCED_SUBGRAPHS != 0)

        self.__adj = adj                            # store adjacency list
        self.__node_groups = accepted

        self.__d = nx.DiGraph()                     # the delta graph       
        self.__entry = entry                        # payload's entry point

        super(self.__class__, self).__init__(
            self.__d, 
            self.__dijkstra_av, 
            # TODO: USE SPUR_DIJKSTRA ;) <--- No b/c we use induced subgraphs?
            lambda node : node                      # identity function (access graph directly)
        )

        # object for CFG shortest paths
        # cfg = P._cfg_shortest_path(graph, clobbering, adj)

        blacklist = set()                           # blacklisted nodes from Delta Graph


        # build the reverse adjacency list
        self.__radj = { }

        for a, b in self.__adj.iteritems():
            for c in b:
                self.__radj.setdefault(c, []).append(a)


        ''' ------------------------------------------------------------------------- '''
        ''' Main loop                                                                 '''
        ''' ------------------------------------------------------------------------- '''
        # self.__d.add_node(entry)                  # add entry node

        # Easter Egg: When entry is None, skip it and start directly from the 1st accepted block.
        if entry != -1 and entry not in ADDR2NODE:  # check if entry point is valid
            raise Exception('Entry point not found')


        # for _, nxt in sorted(accepted.iteritems()):   # for each next level
        for uid, cur in accepted:                   # for each next level

            # if any node is not a valid basic block address, abort
            if len(filter(lambda n : n not in ADDR2NODE and n != -1, cur)): 
                raise Exception('Node is not a valid address')


            # filter out ndoes from current set
            cur = [node for node in cur if (uid, node) not in blacklist]

            

            # The problem: It's possible for an accepted block, to be accepted for >1 statements.
            # If we index nodes in Delta Graph using block addresses, we will end up reusing the
            # same node at different "levels". 
            #
            # To avoid this situation, we index nodes using a tuple (uid, address). 
            #
            self.__d.add_nodes_from( zip([uid]*len(cur), cur) )

                       
            if uid not in self.__adj:               # the last layer (statement) has no neighbors
                continue


            for nxt in self.__adj[ uid ]:
                # accepted = [(0, [4196485]), (6, [4197081L, 4196382]), ..., (24, [4196485])]

                # get set of accepted blocks for the next statement
                nxt_set2 = [b for (a, b) in accepted if a == nxt][0]

                dbg_prnt(DBG_LVL_3, "Delta Graph edges from (%d) '%s' to (%d) '%s'" %
                                        (uid, pretty_list(cur, ', '), 
                                         nxt, pretty_list(nxt_set2, ', ')))


                nxt_set = [node for node in nxt_set2 if (nxt, node) not in blacklist]
             
                # if len(nxt_set) != len(nxt_set2):
                #     warn('REDUCE FROM %d to %d' %(len(nxt_set2), len(nxt_set)))


                # fully connect nodes from current to the next level (quadratic complexity)
                for c in cur:                           # for each node in current level
                    # print '-------------------------------------'
                    
                    # find paths to all nodes in the next level        
                    cfg = P._cfg_shortest_path(graph, clobbering, adj)
                    path = cfg.shortest_path(c, nxt_set, uid)

                    # backdoor 2: wildcard return
                    if len(nxt_set) == 1 and nxt_set[0] == -1: 
                        self.__d.add_edge((uid, c), (nxt, nxt_set[0]), weight=1)
                        warn('ADD a wildcard return statement')
                        del cfg
                        continue


                    # print '======================================='
                    for n in range(len(nxt_set)):       # for each node in the next level
                        # add an edge with cost their distance in CFG (or INF if edge does not exist)

                        
                        # Easter Egg checking
                        if c == entry and entry == -1: 
                            self.__d.add_edge((uid, c), (nxt, nxt_set[n]), weight=0)                    

                        # if next statement is on the same basic block
                        # but next UID is smaller than current (we move backwards)
                        elif c == nxt_set[n] and uid >= nxt:

                            # find a loop (not a 0-distance path)
                            loop, _ = cfg.shortest_loop(c, uid)

                            self.__d.add_edge((uid, c), (nxt, nxt_set[n]), 
                                        weight=loop if loop >= 0 else INFINITY)
                            pass

                        else:
                            # self.__d.add_edge(c, nxt_set[n], weight=path[n][0] \
                            #                           if path[n][0] >= 0  else INFINITY)
                            #    

                            self.__d.add_edge((uid, c), (nxt, nxt_set[n]), 
                                    weight=path[n][0] if path[n][0] >= 0 else INFINITY)

                            pass

                    del cfg


                # -------------------------------------------------------------
                # Optimization:
                #
                # Check if any nodes are totally disconnected from the previous
                # layer. If so, they cannot be part of an induced subgraph, and
                # therefore we can remove them.
                # -------------------------------------------------------------
                for n in range(len(nxt_set)):

                    good = False

                    for c in cur:
                        if self.__d.has_edge((uid, c), (nxt, nxt_set[n])) and \
                            self.__d[(uid, c)][(nxt, nxt_set[n])]['weight'] != INFINITY:
                                # n has at least one edge to the previous layer
                                good = True

                    if not good and self.__d.has_node( (nxt, nxt_set[n]) ):
                    #    warn('edge (%d, %x) - (%d, %x) is missing. Add to blacklist.' % 
                    #           (uid, c, nxt, nxt_set[n]))
                        self.__d.remove_node((nxt, nxt_set[n]))
                        blacklist.add( (nxt, nxt_set[n]) )


        '''
        # NOTE: This is for flat delta graphs, where statement i goes to i+1

        for a, nxt in accepted:                     # for each next level

            print 'nxt', cur, nxt, a
            # if any node is not a valid basic block address, abort
            if len(filter(lambda n : n not in ADDR2NODE, nxt)): 
                raise Exception('Node is not a valid address')

            self.__d.add_nodes_from( nxt )          # add nodes for the next level

            # fully connect nodes from current to the next level (quadratic complexity)
            for c in cur:                           # for each node in current level


                print '-------------------------------------'
                path = cfg.shortest_path(c, nxt)    # find paths to all nodes in the next level
                print '======================================='
                for n in range(len(nxt)):           # for each node in the next level
                    # add an edge with cost their distance in CFG (or INF if edge does not exist)

                    # TODO: remove cheating (backdoor)
                    if c == entry: 
                        self.__d.add_edge(c, nxt[n], weight=7)                  

                    else:
                        self.__d.add_edge(c, nxt[n], weight=path[n][0] if path[n][0] >= 0 \
                                                                       else INFINITY)

            cur = nxt                               # move 1 level deeper
        '''


        # because we don't care in which node we'll end up we add an additional sink node
        # sink node is connected with all nodes in the last level
        
        # self.__d.add_node( _SINK_NODE )               # add sink node
        # self.__d.add_edges_from( zip(nxt, [_SINK_NODE]*len(nxt)), weight=1 )

        # at this point we have built delta graph

        # print self.__d.edges(data=True)

        dbg_prnt(DBG_LVL_1, "Delta graph created")
        dbg_prnt(DBG_LVL_3, "Edges:")

        for a,b,c in self.__d.edges(data=True): 
            if c['weight'] == INFINITY:                       # skip infinity edges
                continue

            dbg_prnt(DBG_LVL_3, "%d:%Xh -> %d:%Xh = %s" % (a[0], a[1], b[0], b[1], str(c)))


        self.__G   = self.__d
        self.graph = self.__d

        # for n in self.__G.nodes():
        #     print hex(n)
        # exit()
        


    # ---------------------------------------------------------------------------------------------
    # k_min_induced_subgraphs(): Find the K minimum k-induced subgraphs. Unfortunately we mess with
    #       NP-hardness here. Even worse the problem can't be even approximated (see proof).
    #       Therefore, a brute force is the only solution here. So, we calculate all the induced
    #       subgraphs (that contain exactly 1 accepted block from each statement), and keep track
    #       of the K minimum solutions (we use a max-heap to optimize that).
    # 
    #
    #       NP-hardness proof:
    #           TODO: Copy proof from here (and explain why there are no approximations):
    #           https://cs.stackexchange.com/questions/85077/minimum-weight-k-induced-subgraph
    #
    #
    # :Arg K: The number of traces to search for (up to K)
    # :Ret: Function is a generator and works exactly as super.k_shortest_paths(): Each time it
    #       returns a tuple (tw, Hk) which is the minimum induced subgraph Hk of G, with a total
    #       weight of tw. If such a subgraph does not exists, function return (-1, empty_graph).
    #
    def k_min_induced_subgraphs( self, K ):
        self.__k = K                                    # number of induced subgraphs

        # when delta graph is flat, a k shortest path approach is sufficient:
        #
        # return super(self.__class__, self).k_shortest_paths(self.__entry, _SINK_NODE, K)

    
        # list with number of accepted blocks from each statement
        self.__bound = [len(x) for _, x in self.__node_groups]
        self.__uid   = [y      for y, _ in self.__node_groups]

        self.__heap = []
        heapq._heapify_max(self.__heap)             # create a max-heap


        dbg_prnt(DBG_LVL_3, "Enumerating all induced subgraphs...")

        
        # build the reverse adjacency list
        self.__radj = { }

        for a, b in self.__adj.iteritems():
            for c in b:
                self.__radj.setdefault(c, []).append(a)



        dbg_arb(DBG_LVL_3, "Adjacency List:", self.__adj)
        dbg_arb(DBG_LVL_3, "Reverse Adjacency List:", self.__radj)

        # enumerate all induced subgraphs
        self.__inc_ctr = 0
        self.__enum_induced_subgraphs(1, [(0, self.__entry)] )
        

        dbg_prnt(DBG_LVL_3, "Done. %d induced subgraphs found." % len(self.__heap))


        inv  = []
        none = True

        while len(self.__heap):                     # for each minimum induced subgraph
            obj = heapq.heappop(self.__heap)
            inv.append(obj)                         # move objects from heap to a list


        for obj in reversed(inv):                   # yield objects in reverse order
            # print 'Inverse', obj.tw, obj.Hk.edges(data=True)

            if obj.tw != INFINITY:
                none = False
                yield obj.tw, obj.Hk


        if none:                                    # if you haven't return anything
            yield -1, nx.empty_graph(create_using=nx.DiGraph())



    # ---------------------------------------------------------------------------------------------
    # __enum_paths(): More recursion! This guy is the assistant for flatten_graph().
    #
    # :Arg curr: Current node
    # :Arg graph: The induced subgraph
    # :Arg P: Current path
    # :Arg __visited: Current set of visited nodes
    # :Arg F: Lambda function to encode nodes in P (needed for pretty-print situations)
    # :Ret: P!
    #
    def __enum_paths( self, curr, graph, P, __visited, F=lambda x: x ):
        if curr in __visited:
            return P


        # __visited.add(curr)

        if len(graph.neighbors(curr)) == 1:
            for n in graph.neighbors(curr):              
                P = self.__enum_paths(n, graph, P+[(curr[0], F(curr[1]), F(n[1]))], __visited+[curr], F)
                # P.append((curr, n))
                

        elif len(graph.neighbors(curr)) == 2:
            n1, n2 = graph.neighbors(curr)
            
            # print n1, n2, self.__adj[curr[0]] 

            Q = self.__enum_paths(n1, graph, [(curr[0], F(curr[1]), F(n1[1]))], __visited+[curr], F)
            R = self.__enum_paths(n2, graph, [(curr[0], F(curr[1]), F(n2[1]))], __visited+[curr], F)

            # print 'Q IS', Q
            # print 'R IS', R

            # check if Q or R is the "taken" branch
            # in adj the taken branch is always first
            if self.__adj[curr[0]] == [n1[0], n2[0]]:
                P.append([Q, R])                    # n1 is the "taken" branch
            else:
                P.append([R, Q])                    # n2 is the "taken" branch

        else:
            return P + [(curr[0], F(curr[1]), F(curr[1]))]

        # print 'FINAL P', P
        return P



    # ---------------------------------------------------------------------------------------------
    # flatten_graph(): Flatten the induced subgraph. Enumerate all paths and store them as 
    #   a tree of lists. 
    #
    # :Arg graph: Current induced subgraph
    # :Ret:
    #
    def flatten_graph( self, graph ):
        '''
        # self.__stack = ['e']
        self.__visited = set()

        graph = nx.DiGraph()
    
        graph.add_nodes_from( ['e', 'A2', 'A3', 'A4', 'A5', 'A6', 'A7'] )

        graph.add_edge( 'e',  'A2', weight=0)
        graph.add_edge( 'A2', 'A3', weight=30)
        graph.add_edge( 'A2', 'A4', weight=2)
        graph.add_edge( 'A3', 'A5', weight=4)
        graph.add_edge( 'A4', 'A7', weight=1)
        graph.add_edge( 'A5', 'e',  weight=2)
        graph.add_edge( 'A5', 'A6', weight=3)
        graph.add_edge( 'A6', 'A7', weight=3)
        graph.add_edge( 'A7', 'A2', weight=2)

        P = self.__enum_paths('e', graph, [], [])

        # print 'P', P
        '''        
        self.__visited = set()

        P      = self.__enum_paths((0, self.__entry), graph, [], [])
        pretty = self.__enum_paths((0, self.__entry), graph, [], [], lambda x: '%x' % x)
                
        # TODO: Distinguish between taken/not taken brances
                
        return P, pretty

# -------------------------------------------------------------------------------------------------


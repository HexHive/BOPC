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
# map.py:
#
# This module is responsible for mapping IR's virtual registers and variables, to host registers 
# and addresses of the target binary. During graph marking, we create a bipartite graph that
# contains the virtual registers on the one set and the host registers on the other. The edges 
# denote potential mappings. Furthermore, when a variable is passed as a reference to a virtual
# register, we encode that mapping (variable <-> address) as weight of the corresponding edege.
#
# Finding one such mapping doesn't imply that trace search algorithm will find a solution. Hence,
# we need to go back, find another mapping and try again. This creates the need to enumerate *all*
# possible mappings. So for each register mapping, we extract the edge weights and we enumerate 
# *all* possible variable mappings. We use algorithm at [1] to make enumeration efficient.
#
# The time complexity for register mapping is O(1), because the register set is constant (8 virtual
# registers and 16 host registers). For the variable mappings the time complexity is:
# O(|E|*|V|^0.5 + |N|*A), where A = total number of possible matchings.
#
#
# [1]. Uno, Takeaki. "Algorithms for enumerating all perfect, maximum and maximal matchings in 
#       bipartite graphs." Algorithms and Computation (1997): 92-101.  
#
# -------------------------------------------------------------------------------------------------
from coreutils import *

import networkx as nx
import __builtin__                                  # to use the built-in map()
import copy
import re


# -------------------------------------------------------------------------------------------------
# _match: This class finds all maximum matchings in a given bipartite undirected graph by using
#   the algorithm as described in [1]. Note that the optimization of trimming unnecessary edges 
#   from D(G,M) is not implemented, as this class works with small graphs.
#
#   This class uses a recursion to enumerate all matchings. So, every time a matching is found, a
#   callback is invoked to process the matching. If the callback want to stop getting matchings, 
#   it should return a negative value.
#
class _match( object ): 
    ''' ======================================================================================= '''
    '''                                   INTERNAL FUNCTIONS                                    '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __D(): Generate directed graph D(G,M) as defined in the original paper. Let V1 = __r0, __r1, 
    #       etc. (host registers) and V2 = rax, rdx, rcx, etc. (virtual registers), if we're in
    #       "register" mode, and Let V1 = $loc_2, etc. (variables) and V2 = 0x7ffff.... etc. 
    #       (addresses) if we're in "variable" mode.
    #
    # :Arg G: Undirected graph to work on.
    # :Arg M: A maximum matching, as a list of tuples.
    # :Ret: D(G,M) (directed).
    #   
    def __D( self, G, M ):
        DG = nx.DiGraph()                           # create an empty directed graph        
        DG.add_nodes_from(G.nodes())                # D(G,M) has the same vertices with G
        DG.add_edges_from( M )                      # edges from M are directed from V1 to V2 in D
        
        for e in G.edges():                         # for each edge in G
            if self.__opposite(e[0]):               # if edge is (host, virtual) or (addr, var)
                e = (e[1], e[0])                    # swap it to (virtual, host) or (var, addr)
                        
            # print '!', e, M 
            if not e in M:                          # if edge not in M
                DG.add_edge(e[1], e[0])             # add edge in reverse direction

        return DG                                   # return D(G,M)


    # ---------------------------------------------------------------------------------------------
    # __matchings_iter(): Given a graph G and a matching M, find another matching M' != M. This
    #       is a recursive function which means that, it will find all matchings. If the callback
    #       function wants to stop enumerations for some reason, all it has to do, is to return a 
    #       negative value and __matchings_iter() will stop producing more matchings.
    #
    # :Arg G: Graph to work on
    # :Arg M: A list of tuples, containing a maximum matching
    # :Arg D: The special graph D(G,M)
    # :Ret: Under normal execution, function returns 0. If callback returns -1 at some point,
    #   then function enters exit mode, which returns always -1.
    #
    def __matchings_iter( self, G, M, D ):  
        if G.number_of_edges == 0:                  # if G has no edges,
            return 0                                # stop (normal mode)
        
        try:                                        # look for a cycle in D(G,M)
            cycle = nx.algorithms.find_cycle(D, orientation='original') 

            ''' --------------------------------------------------------------------- '''
            ''' we have found a cycle                                                 '''
            ''' --------------------------------------------------------------------- '''

            # exchange matching edges with other edges in cycle
            Mprime  = [(e[1], e[0]) for e in cycle if e not in M] 
            Mprime += [e for e in M if e not in cycle]

            # remove tuples from bitvector strings
            Mprime = __builtin__.map(lambda x : (x[0],x[1][0]) if isinstance(x[1], tuple)   
                                                               else x, Mprime)


            # M' (Mprime) is a new maximum matching. Invoke callback
            if self.__callback( sorted(Mprime, key=lambda e: e[0]) ) < 0:
                return -1                           # if callback wants to stop, stop
            

            # pick an edge e that is both in M and cycle (always exists)
            e = [e for e in cycle if e in M][0]

        except nx.exception.NetworkXNoCycle:        # D(G,M) has no cycles
            ''' --------------------------------------------------------------------- '''
            ''' no cycle. Look for a feasible path of length 2                        '''
            ''' --------------------------------------------------------------------- '''

            feasible = None

            # for each uncovered node in D(G,M)
            # b/c we're dealing with max matchings, uncovered nodes, are host registers
            for u in list(set(D.nodes()) - set([vtx for e in M for vtx in e])):

                # for each possible target vertex (different from source)
                for v in [v for v in D.nodes() if u != v]:
                    # If a vertex is uncovered, then (path[0], path[1]) is not in M. Therefore,
                    # (path[1], path[2]) must be in M due to the construction of D(G,M). So, if
                    # the 2nd edge is in M, the other endpoint won't have any other edges in M
                    # b/c current matching is maximum and there's already one edge of M adjacent
                    # to that endpoint. This makes any length 2 path in D(G,M) starting from an
                    # uncovered vertex, feasible.

                    # try to find all simple paths of length *exactly* 2 (3 vertices)
                    for path in nx.all_simple_paths(D, u, v, cutoff=2):
                        if len(path) != 3: continue                 
                        feasible = path             # we got a feasible path
                        break

                    if feasible: break              # break both loops
                if feasible: break                  # break both loops

            if not feasible: return 0               # if no feasible path, stop
            
            # get an edge e which is in feasible path but not in M
            e = (feasible[1], feasible[0]) if   (feasible[1], feasible[0]) not in M \
                                           else (feasible[1], feasible[2]) 
                
            # create a new matching
            Mprime = [m for m in M if m[0] != e[0] ] + [e]


            # remove tuples from bitvector strings
            Mprime = __builtin__.map(lambda x : (x[0],x[1][0]) if isinstance(x[1], tuple)   
                                                               else x, Mprime)


            # M' (Mprime) is a new maximum matching. Invoke callback
            if self.__callback( sorted(Mprime, key=lambda e: e[0]) ) < 0:
                return -1                           # if callback wants to stop, stop

            Mprime, M = M, Mprime                   # swap matchings (important!)

        ''' ------------------------------------------------------------------------- '''
        ''' common code for both cases                                                '''
        ''' ------------------------------------------------------------------------- '''

        # generate G+(e)
        Gplus = copy.deepcopy(G)                    # get a hardcopy of G       
        Gplus.remove_node( e[0] )                   # drop e and e's endpoints
        Gplus.remove_node( e[1] )                   # along with all adjacent edges 
        
        # generate G-(e)
        Gminus = copy.deepcopy(G)                   # get a hardcopy of G
        Gminus.remove_edge( e[0], e[1] )            # drop e

        # OPTIONAL: As an optimization, we can trim unnecessary edges from D(G,M)

        # recursively find matchings for G+(e) and G-(e)
        if self.__matchings_iter(Gplus, M, self.__D(Gplus, [x for x in M if x != e]) ) < 0:
            del Gplus, Gminus, D                    # release allocated objects
            return -1                               # quickly return from recursions

        if self.__matchings_iter(Gminus, Mprime, self.__D(Gminus, Mprime)) < 0:
            del Gplus, Gminus, D                    # release allocated objects
            return -1                               # quickly return from recursions


        del Gplus, Gminus, D                        # release allocated objects
        return 0                                    # normal return


    # ---------------------------------------------------------------------------------------------
    # __max_matchings_recursion(): Recursively find all maximum matchings for *registers*. This is
    #       an exponential time approach, as tries all possible combinations. However, it's useful 
    #       to evaluate the correctness of the enum_max_matchings() (debug only).
    #
    # :Arg G: Graph to work on
    # :Arg depth: Current recursion depth
    # :Arg M: Current matching
    # :Ret: None.
    #
    def __max_matchings_recursion( self, G, depth, M ):
        if depth >= self.__n:                       # reach max depth?
            self.__callback(M)                      # invoke callback and stop
            return

        curr = '__r%d' % depth                      # make current virtual register

        for n in G.neighbors( curr ):               # for each adjacent vertex
            # code is for debug, so keep it simple: Instead of keeping track of
            # edges and nodes you remove, just copy the whole graph
            NG = copy.deepcopy(G)

            NG.remove_node( curr )                  # drop nodes that make a pair
            NG.remove_node( n )

            # move on the next matching
            self.__max_matchings_recursion(NG, depth+1, M+[(curr, n)])
            
            del NG                                  # new graph not needed anymore


    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor.
    #
    # :Arg graph: Graph to work on
    # :Arg mode: Working mode (register/variable)
    #
    def __init__( self, graph, mode ):  
        if not nx.is_bipartite(graph):              # check if graph is bipartite
            raise Exception('Not a bipartite graph!')
            
        if nx.is_directed(graph):                   # check if graph is undirected
            raise Exception('Not an undirected graph!')

        self.__G = copy.deepcopy(graph)             # get graph


        # drop nodes without edges
        for n in [n for n in graph.nodes() if graph.degree(n) == 0]:
            self.__G.remove_node(n)                 # remove node 
        

        # opposite() is used to check the orientation of an edge
        # check mode and set lambda accordingly.
        try:                                        
            self.__mode, self.__opposite = mode, {
                'register' : lambda key : not re.match(r'^__r.$', key),
                'variable' : lambda key : isinstance(key, long) or isinstance(key, tuple)
            }[ mode ]
        except KeyError: 
            fatal("Invalid mode '%s'" % mode )      # invalid mode


    # ---------------------------------------------------------------------------------------------
    # __del__(): Class destructor.
    #
    def __del__( self ):
        del self.__G                                # release graph


    # ---------------------------------------------------------------------------------------------
    # enum_max_matchings(): Enumerate all maximum matchings.
    #
    # :Arg callback: A callback function to be invoked every time a new matching is found
    # :Arg n: Size of max matching (optional)
    # :Ret: None.
    #
    def enum_max_matchings( self, callback, n=-1 ):
        self.__callback = callback                  # save callback function

        # find a maximum matching in M      
        M = nx.bipartite.maximum_matching(self.__G)

        # M is a dictionary like: {'__r0': 'rdx', '__r1': 'rcx', '__r2': 'rax', 'rdx': '__r0', 
        # 'rcx': '__r1', 'rax': '__r2'}. Each edge it appears both in forward and reverse 
        # direction. So, we only keep edges in one direction (V1 -> V2)
        #
        # don't use .iteritems() (dictionary is modifed on the fly)
        for key, val in M.items():
            if self.__opposite(key):                # drop (host, virtual) (or (addr, var)) edges 
                del M[key]

        M = M.items()                               # cast dictionary to list (for convenience)


        # To get the number of virtual registers in the graph we can't use this:
        #   virt, _ = nx.bipartite.sets(self.__G) 
        # 
        # This is because bipartite.sets() algorithmically find the sets. So, if a node has no
        # edges it will classified in the 2nd set, even if it has attribute bipartite = 0. To
        # fix that we can either drop nodes with no edges, or to use an alternative:
        virt = [u for u, b in nx.get_node_attributes(self.__G,'bipartite').iteritems() if not b]


        # check if matching cover all virtual registers (or variables)
        # if not an explicit size is given, extract size from bipartite sets        
        if n > 0 and len(M) < n or n < 0 and len(M) < len(virt):                    
            dbg_arb(DBG_LVL_3, "There are no maximum matchings for", self.__G.edges())
            return 0                                # abort


        # TODO: M can be:
        #   [('__r0', 'r14'), ('__r1', 'r15')]
        #   [('foo', ('<BV64 0x7ffffffffff0020>',))]
        #
        # Because bitvectors are strings at this point, no exceptions are thrown

        # remove tuples from bitvector strings
        M = __builtin__.map(lambda x : (x[0],x[1][0]) if isinstance(x[1], tuple) else x, M)

        # print 'M IS ', M

        # M is a the 1st maximum matching. Invoke callback
        # if self.__callback( sorted(M, key=lambda e: e[0]) ) < 0:
        if self.__callback( M ) < 0:
            return -1                               # if callback wants to stop, stop

        # OPTIONAL: As an optimization, we can trim unnecessary edges from D(G,M)

        # find all other maximum matchings
        return self.__matchings_iter(self.__G, M, self.__D(self.__G, M))    


    # ---------------------------------------------------------------------------------------------
    # enum_max_matchings_bf(): Enumerate all maximum matchings using brute force. This is simply
    #       a wrapper of __max_matchings_recursion() (register only (DEB)).
    #
    # :Arg callback: A callback function to be invoked every time a new matching is found
    # :Arg n: Size of max matching
    # :Ret: None.
    #
    def enum_max_matchings_bf( self, callback, n ):
        self.__callback = callback                  # save callback function
        self.__n        = n                         # size of max matching

        if self.__mode != 'register':               # this only available in register mode
            fatal("Brute force matching is not supported in variable mode")

        self.__max_matchings_recursion(self.__G, 0, [])


# -------------------------------------------------------------------------------------------------


# -------------------------------------------------------------------------------------------------
# map: This class finds all matchings between virtual and host registers and between variables and 
#   addresses. This is mostly a wrapper of _match class. 
#
class map( object ):
    ''' ======================================================================================= '''
    '''                                   INTERNAL FUNCTIONS                                    '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __intrl_callback_var(): This callback is invoked every time that a new variable matching is
    #       found. This function is implicitly invoked by __intrl_callback_reg() which means that
    #       at this point there is already a register mapping. This function is actually a wrapper
    #       for the original callback of enum_mappings().
    #
    # :Arg match: A new matching, as a list of tuples
    # :Ret: If function wants to be invoked again with a new matching, it should return a non
    #   negative value. Otherwise returns 0.
    #
    def __intrl_callback_var( self, match ):

        # invoke the real callback
        return self.__callback(self.__reg_match, match)
        

    # ---------------------------------------------------------------------------------------------
    # __intrl_callback_reg(): This callback is invoked every time that a new register matching is
    #       found. At this point we have a maximum matching for registers (register mapping). 
    #       Given this matching, create the variable graph and enumerate all possible variable 
    #       matchings.
    #
    # :Arg match: A new matching, as a list of tuples
    # :Ret: If function wants to be invoked again with a new matching, it should return a non
    #   negative value. Otherwise returns 0.
    #
    def __intrl_callback_reg( self, match ):
        self.__reg_match = match                    # save matching for later

        vG = nx.Graph()                             # variable graph        
        
        for u, v in match:                          # for each edge in register mapping
            try:
                for a,b in self.__g.get_edge_data(u, v)['var']:
                    vG.add_node(a, bipartite=0)
                    vG.add_node(b, bipartite=1)
                    vG.add_edge(a, b)
            except KeyError: pass                   # edge has no weights
        
        match = _match(vG, 'variable')              # create a 2nd matching object


        # enumerate all variable matchings, using an 2nd internal callback
        if match.enum_max_matchings(self.__intrl_callback_var, self.__nvars) < 0:           
            del match                               # free object   
            return -1                               # no more matchings

        del match                                   # free object
        return 0                                    # normal return


    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor.
    #
    # :Arg graph: Graph to work on
    # :Arg nregs: Total number of virtual registers
    # :Arg nvars: Total number of variables
    #
    def __init__( self, graph, nregs, nvars ):
        self.__g     = graph                        # store arguments
        self.__nregs = nregs
        self.__nvars = nvars


    # ---------------------------------------------------------------------------------------------
    # enum_mappings(): Enumerate all possible register and variable mappings.
    #
    # :Arg callback: A callback function to be invoked, every time a mapping is found
    # :Ret: None.
    #
    def enum_mappings( self, callback ):        
        dbg_prnt(DBG_LVL_1, "Enumerating all mappings between virtual and hardware registers")
        dbg_prnt(DBG_LVL_1, "\tand all mappings between variables and addresses...")

        self.__callback = callback                  # get callback

        try:        
            match = _match(self.__g, 'register')    # create a matching object
        except Exception: return                    # catch exception

        # enumerate all register matchings, using an internal callback
        ret = match.enum_max_matchings(self.__intrl_callback_reg, self.__nregs)

        del match                                   # free object
        
        return ret

# -------------------------------------------------------------------------------------------------
'''
if __name__ == '__main__':                          # DEBUG ONLY
    G = nx.Graph()
    
    G.add_nodes_from(['__r0', '__r1', '__r2', '__r3'], bipartite=0)
    G.add_nodes_from(['rax', 'rdx', 'rcx', 'rbx', 'rsi', 'rdi'], bipartite=1)   
    
    G.add_edges_from([ 
        ('__r0', 'rax'), ('__r0', 'rcx'), ('__r0', 'rsi'),
        #('__r1', 'rax'), ('__r1', 'rdx'), ('__r1', 'rcx'), ('__r1', 'rbx'),
        ('__r2', 'rcx'), ('__r2', 'rdi'), ('__r2', 'rsi'),
        ('__r3', 'rdx'), ('__r3', 'rdi'), ('__r3', 'rsi')

    ])  
    
#   G.add_nodes_from(['$loc_2'], bipartite=0)
#   G.add_nodes_from([576460752303358032L, 576460752303358048L, 576460752303358064L], bipartite=1)  
#
#   G.add_edges_from([ 
#       ('$loc2', 576460752303358032L),
#       ('$loc2', 576460752303358048L),
#       ('$loc2', 576460752303358064L)
#   ])
    
    def callback( m ):
        print 'Got matching: ', m
        return 0                                    # must return an non negative value

    m = _match( G, 'register' )
    m.enum_max_matchings( callback )

    print '----------------------------------------'
    m.enum_max_matchings_bf( callback, 4 )
'''
# -------------------------------------------------------------------------------------------------

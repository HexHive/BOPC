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
# capability.py
#
# This module measures the capability of the program. That is, program's capability gives a good
# indication, on "what the program is capable of executing" in terms of SPL payloads. However, all
# these metrics, aim to identify *upper bounds*; that is, they overestimate the set of SPL programs
# that can be truly executed on this binary.
# -------------------------------------------------------------------------------------------------
from coreutils import *
from calls     import *
import path as P

import networkx as nx
import textwrap
import datetime
import pickle
import math
import numpy



# -----------------------------------------------------------------------------
# Capability Options
# -----------------------------------------------------------------------------
CAP_ALL             = 0x00FF                        # all types of statements
CAP_REGSET          = 0x0001                        # register assignments 
CAP_REGMOD          = 0x0002                        # register modifications
CAP_MEMRD           = 0x0004                        # memory reads
CAP_MEMWR           = 0x0008                        # memory writes
CAP_CALL            = 0x0010                        # system and library calls
CAP_COND            = 0x0020                        # conditional statements
CAP_LOAD            = 0x0100                        # load the capability graph from a file
CAP_SAVE            = 0x0200                        # save the capability graph to a file
CAP_NO_EDGE         = 0x0400                        # don't calculate edges in capability graph

# types of analyses
CAP_STMT_COMB_CTR   = 'STMT_COMB_CTR'               # Count combinations of statements
CAP_STMT_MIN_DIST   = 'STMT_MIN_DIST'               # Count min distance between statements
CAP_LOOPS           = 'LOOPS'                       # Analyze loops



# -------------------------------------------------------------------------------------------------
# capability: This class is responsible for performing several measurements in the target binary.
#
class capability( object ):
    ''' ======================================================================================= '''
    '''                                   INTERNAL VARIABLES                                    '''
    ''' ======================================================================================= '''
    __cap = nx.DiGraph()                            # the capability graph (CAP)
    __uid = 0                                       # a unique ID
    


    ''' ======================================================================================= '''
    '''                                   INTERNAL FUNCTIONS                                    '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __add(): Add a node to the capability graph.
    #
    # :Arg addr: Address of the basic block tha contains the statement
    # :Arg ty: Statement type: regset / regmod / call / cond
    # :Arg reg: Register name (for regset/regmod/cond)
    # :Arg val: Statement's value (for regset/regmod/cond)
    # :Arg mode: Statement mode (const/deref for regset and syscall/libcall for call)
    # :Arg isW: A flag indicating whether "val" points to a writable address (for regset)
    # :Arg op: Statement operator (for regmod/cond)
    # :Arg mem: Memory address (for memrd/memwr)
    # :Arg name: Function name (for call)
    # :Ret: None.
    #
    def __add( self, addr, ty, reg=None, val=None, mode=None, isW=None, op=None, name=None, mem=None, size=None ):
        # NOTE: We assume that arguments are not malformed, so we don't do any checks
        cap = {
            'regset' : {'addr':int(addr), 'type':ty, 'reg':reg, 'val':val, '+W':isW, 'mode':mode},
            'regmod' : {'addr':int(addr), 'type':ty, 'reg':reg, 'op':op, 'val':val},
            'memrd'  : {'addr':int(addr), 'type':ty, 'reg':reg, 'mem':mem, 'size':size},
            'memwr'  : {'addr':int(addr), 'type':ty, 'mem':mem, 'val':val, 'size':size},
            'call'   : {'addr':int(addr), 'type':ty, 'name':name, 'mode':mode},
            'cond'   : {'addr':int(addr), 'type':ty, 'reg':reg, 'op':op, 'val':val}
        }[ ty ]                                     # nicely "switch" the appropriate statement
     
        self.__cap.add_node(self.__uid, **cap)      # add statement to the graph
        self.__uid += 1                             # update UID counter



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor. Simply initialize private variables.
    #
    # :Arg cfg: Program's CFG.
    # :Arg name: Program's filename
    #
    def __init__( self, cfg, name ):       
        self.__cfg  = cfg                           # save cfg to internal variables
        self.__name = name                          # program's filename



    # ---------------------------------------------------------------------------------------------
    # build(): Build the Capability Graph. This is a very slow process, so it's possible to save
    #       the graph once its generated, thus without having to re-calculate it the next time.
    #       
    # :Arg options: An integer that describes how the capability graph should be built. It can be
    #       the logical OR of one or more of the following:
    #
    #       CAP_ALL     | Include all types of statements in the graph
    #       CAP_REGSET  | Include register assignments in the graph
    #       CAP_REGMOD  | Include register modifications in the graph
    #       CAP_CALL    | Include system and library calls in the graph
    #       CAP_COND    | Include conditional statements in the graph
    #       CAP_LOAD    | Load the capability graph from a file
    #       CAP_SAVE    | Save the capability graph to a file
    #
    # :Ret: None.
    #
    def build( self, options=CAP_ALL ):
        dbg_prnt(DBG_LVL_1, "Exploring program's capability...")

        # ---------------------------------------------------------------------
        # Load Capability Graph from file ?
        # ---------------------------------------------------------------------       
        if options & CAP_LOAD:
            dbg_prnt(DBG_LVL_1, "Loading the Capability Graph from file...")

            try:
                self.__cap = nx.read_gpickle(self.__name + '.cap')

                dbg_prnt(DBG_LVL_1, "Done.")            

                return                              # your job is done here

            except IOError, err:
                # if you can't load it, simply re-calculate it ;)

                error("Cannot load Capability Graph: %s" % str(err))


        # ---------------------------------------------------------------------
        # Iterate over abstracted basic blocks
        # ---------------------------------------------------------------------       
        dbg_prnt(DBG_LVL_1, "Searching CFG for 'interesting' statements...")

        nnodes  = len(nx.get_node_attributes(self.__cfg.graph, 'abstr').items())
        counter = 1
        
        p = P._cfg_shortest_path(self.__cfg)


        for node, abstr in nx.get_node_attributes(self.__cfg.graph,'abstr').iteritems():
            addr = node.addr

            dbg_prnt(DBG_LVL_3, "Analyzing block at 0x%x (%d/%d)..." % (addr, counter, nnodes))
        

            if options & CAP_REGSET:
                for reg, data in abstr['regwr'].iteritems():

                    if data['type'] == 'concrete':
                        self.__add(addr, ty='regset', reg=reg, val=data['const'], mode='const',
                                         isW=data['writable'])

                    elif data['type'] == 'deref':
                        self.__add(addr, ty='regset', reg=reg, val=data['addr'], mode='deref')
          

            if options & CAP_REGMOD:
                for reg, data in abstr['regwr'].iteritems():
                    if data['type'] == 'mod':                                               
                        self.__add(addr, ty='regmod', reg=reg, op=data['op'], val=data['const'])


            if options & CAP_MEMRD:
                for reg, data in abstr['regwr'].iteritems():
                    if data['type'] == 'deref' and data['memrd']:
                        loadreg = data['deps'][0]

                        self.__add(addr, ty='memrd', reg=reg, mem=loadreg, size=data['memrd'])
        
            
            if options & CAP_MEMWR:
                for memwr in abstr['splmemwr']:
                    self.__add(addr, ty='memwr', mem=memwr['mem'], val=memwr['val'], size=memwr['size'])



            if options & CAP_CALL and abstr['call'] and find_call(abstr['call']['name']):
                self.__add(addr, ty='call', name=abstr['call']['name'], mode=abstr['call']['type'])


            elif options & CAP_COND and abstr['cond']:
            
                # elif because we can't have call and cond at the same basic block
                self.__add(addr, ty='cond', reg=abstr['cond']['reg'], op=abstr['cond']['op'],
                                 val=abstr['cond']['const'])


                '''
                # -----------------------------------------------------------------------
                # hacky way to quickly find a loop
                # -----------------------------------------------------------------------
                for length, loop in p.k_shortest_loops(addr, 0, 10):
                    length, loop = p.shortest_loop(addr)

                    R = abstr['cond']['reg']

                    regmod = 0
                    regset = 0
                    step = 0

                    if length < INFINITY:

                        for l in loop[:-1]:
                            try:
                                X = self.__cfg.graph.node[ADDR2NODE[l]]['abstr']
                            except KeyError:
                                continue
                
                            for reg, data in X['regwr'].iteritems():
                                if data['type'] == 'mod' and reg == R:
                                    regmod += 1
                                    step = data['const']

                                elif reg == R:
                                    regset += 1


                        if regmod == 1 and regset == 0:
                            emph(bolds('GOOD LOOP (%d - %d - %s) %s' % 
                                    (abstr['cond']['const'], step, abstr['cond']['op'], 
                                    pretty_list(loop))))

                        # else:
                        #    print 'BAD LOOP (mod: %d, set: %d) (%d - %d - %s) %s' % \
                        #        (regmod, regset, abstr['cond']['const'], step, abstr['cond']['op'],
                        #        pretty_list(loop))
                '''

            counter += 1                            # update counter

        dbg_prnt(DBG_LVL_1, "Done.")


        # ---------------------------------------------------------------------
        # Show some statistics
        # ---------------------------------------------------------------------       
        emph("Binary has %s interesting statements:" % bold(self.__cap.order()))

        stmt_ctr = { 'regset' : 0, 'regmod' : 0, 'memrd' : 0, 'memwr' : 0, 'call' : 0, 'cond' : 0 }
        
        for _, data in self.__cap.nodes(data=True):
             stmt_ctr[ data['type'] ] += 1          # count statements


        emph("\t%s register assignments"   % bold(stmt_ctr['regset'], pad=5))
        emph("\t%s register modifications" % bold(stmt_ctr['regmod'], pad=5))
        emph("\t%s memory reads     "      % bold(stmt_ctr['memrd'], pad=5))
        emph("\t%s memory writes    "      % bold(stmt_ctr['memwr'], pad=5))
        emph("\t%s system/library calls"   % bold(stmt_ctr['call'], pad=5))
        emph("\t%s conditional jumps"      % bold(stmt_ctr['cond'], pad=5))


        # ---------------------------------------------------------------------
        # Add edges to the Capability Graph
        # ---------------------------------------------------------------------

        # don't calculate edges if asked (it's time consuming)
        if options & CAP_NO_EDGE:
            dbg_prnt(DBG_LVL_1, "Skipping edge calculation of capability graph.")
            return


        dbg_prnt(DBG_LVL_1, "Building the Capability Graph...")


        # list of node addresses
        node_list = [ d['addr'] for _, d in self.__cap.nodes_iter(data=True) ]    
        SPT       = nx.DiGraph()                    # create the Shortest Path Tree
        completed = 0                               # % completed

        csp = P._cfg_shortest_path(self.__cfg)      # create the CFG Shortest Path object


        warn("This can be a very slow process ('-dd' and '-ddd' options show a progress bar)")

        # for each node u_ in Capability Graph
        for u_, du in self.__cap.nodes_iter(data=True):            
            v_ = -1                                 # v_ is the uid of the target node (u_ -> v_)            

            SPT.clear()                             # clear Shortest Path Tree

            # Find the shortest paths (in CFG) to every other statement. Unfortunately, shortest
            # paths in CFG are not like regular shortest paths, as we explain in path.py. Thus we
            # have to re-calculate all shortest paths for every node in the capability graph.
            for length, path in csp.shortest_path(du['addr'], node_list):
                v_ += 1                             # the uid of the current node (it's linear)

                if length == INFINITY:
                    continue                        # skip nodes with non-existing paths

                # ---------------------------------------------------------------------------------
                # Now, if we directly add the edges with shortest path lengths to the capability
                # graph, we'll have an interesting problem: Consider the path A - x - x - B - x - C
                # in CFG. The Capability Graph should contain the edges (A, B, 3) and (B, C, 2). 
                # However the naive approach, will also add the edge (A, C, 5) to the graph. The
                # problem here is that we cannot accurately measure chains of statements due to the
                # direct edges.
                #
                # To fix this issue we build the Shortest Path Tree (SPT). That is, we merge all
                # shortest paths, into a single graph. The resulting graph will be tree as it
                # consists only of single source shortest paths (without loops), with all edges
                # having weight = 1. SPT has two types of nodes: Black and White. Black nodes 
                # contain statements (should appear on capability graph) while White nodes are used
                # for transitions. The first and the last nodes of each shortest path are Black
                # while every other node between is White. Our goal is to remove all White nodes
                # and merge the resulting SPT with the capability graph.
                #
                # We remove the White nodes one by one. When we remove a White node, we also update
                # the weights in SPT.
                # ---------------------------------------------------------------------------------
               
                # add first and last nodes (Black) to the SPT (if already exists, make them Black)
                SPT.add_nodes_from([path[0], path[-1]], color='Black')

                # keep track of the statement uids that use this node (map address to UID)
                SPT.node[path[0] ].setdefault('uid', set()).add(u_)
                SPT.node[path[-1]].setdefault('uid', set()).add(v_)

                # convert nodes [1,2,3,4], into edges [(1,2),(2,3),(3,4)] and add them to SPT
                SPT.add_edges_from(zip(path, path[1:]), weight=1)

                # color the intermediate nodes White (if they're not Black)
                for p in path[1:-1]:
                    if 'color' not in SPT.node[p] or SPT.node[p]['color'] != 'Black':
                         SPT.node[p]['color'] = 'White'


            # iteratively delete the White nodes
            for n in [node for node, data in SPT.nodes(data=True) if data['color'] == 'White']:

                # for each pair of (incoming, outgoing) edges
                for src, _, d1 in SPT.in_edges(n, data=True):
                    for _, dst, d2 in SPT.out_edges(n, data=True):
                        # add a new edge that bypasses the White node
                        SPT.add_edge(src, dst, weight=d1['weight']+d2['weight'])


                SPT.remove_node(n)                  # delete White node (along with its edges)


            ''' at this point, SPT will only contain Black nodes '''

            # merge SPT to the capability graph
            for e1, e2, data in SPT.edges_iter(data=True):
                # copy it edge-by-edge
                for u in SPT.node[e1]['uid']:       # move from addresses back to UIDs
                    for v in SPT.node[e2]['uid']:   
                        if u != v:                  # that's to avoid self-loops
                            self.__cap.add_edge(u, v, weight=data['weight'])
                            

            # show current progress (%)
            percent = math.floor(100. / len(self.__cap) * u_)
            if completed < percent:
                completed = percent            
                dbg_prnt(DBG_LVL_2, "%d%% completed" % completed)

        del SPT                                     # we don't need the SPT anymore

        dbg_prnt(DBG_LVL_1, "Done. Capability Graph generated successfully.")
      
        visualize(self.__cap)

     

        # ---------------------------------------------------------------------
        # Save Capability Graph to a file ?
        # ---------------------------------------------------------------------       
        if options & CAP_SAVE:
            dbg_prnt(DBG_LVL_1, "Saving Capability Graph...")

            try:
                nx.write_gpickle(self.__cap, self.__name + '.cap')
                dbg_prnt(DBG_LVL_1, "Done. Capability Graph saved as %s" % self.__name + '.cap')

            except IOError, err:
                error("Cannot save Capability Graph: %s" % str(err))



    # ---------------------------------------------------------------------------------------------
    # get(): Return the Capability Graph. Just in case ;)
    #
    # :Ret: The Capability Graph
    #
    def get( self ):
        return self.__cap



    # ---------------------------------------------------------------------------------------------
    # save(): Save the nodes of the Capability Graph (i.e., the interesting statements) to a file.
    #
    # :Ret: None.
    #
    def save( self ):
        now    = datetime.datetime.now()            # get current timestamp
        banner = textwrap.dedent("""\
            #
            # This file has been created by BOPC at %s
            # '%s' has %d interesting statements. Each line shows a statement.
            #
            # The columns are: address | type | register | value | mode | +W | operator | name
            # When an attribute is not available, a dot '.' is presented.
            #
            #
            # Attribute list:
            #
            #   address  : Address of the basic block tha contains the statement
            #   type     : Statement type: regset / regmod / call / cond
            #   register : Register name (for regset / regmod / cond)
            #   memory   : Memory address (for memrd / memwr)
            #   value    : Statement's value (for regset / regmod / cond)
            #   mode     : Statement mode (const / deref for regset and syscall / libcall for call)
            #   +W       : A flag indicating whether "val" points to a writable address (for regset)
            #   operator : Statement operator (for regmod / cond)
            #   name     : Function name (for call)
            #
        """ % (now.strftime("%d/%m/%Y %H:%M"), self.__name, self.__cap.order()))


        dbg_prnt(DBG_LVL_1, "Dumping interesting statments to a file...")    
         
        try:    
            cap = open(self.__name + '.stmt', 'w')

            cap.write(banner)                       # write banner first

            # write statements one by one
            for _, d in self.__cap.nodes_iter(data=True):                  
                opt  = '%10s'   % (d['reg']  if 'reg'  in d else '.')
                opt += '%10s'   % (d['mem']  if 'mem'  in d else '.')
                opt += ' %32s ' % (d['val']  if 'val'  in d else '.')
                opt += '%10s'   % (d['mode'] if 'mode' in d else '.')
                opt += '%10s'   % (d['+W']   if '+W'   in d else '.')
                opt += '%10s'   % (d['op']   if 'op'   in d else '.')
                opt += '%16s'   % (d['name'] if 'name' in d else '.')
                opt += '%10s'   % (d['size'] if 'size' in d else '.')

                cap.write( "0x%08x %10s %s\n" % (d['addr'], d['type'], opt) )
                       
            cap.close()
           
            dbg_prnt(DBG_LVL_1, "Done. Capability Graph saved as %s" % self.__name + '.stmt')

        except IOError, err:
            error("Cannot create statements file: %s" % str(err))



    # ---------------------------------------------------------------------------------------------
    # explore(): Explore the Capability Graph and look for "islands".
    #    
    # :Ret: None.
    #
    def explore( self ):        
        dbg_prnt(DBG_LVL_1, "Exploring the Capability Graph...")

        self.__islands = []                         # store islands here
        n_inslands     = 0                          # number of islands
        size, diam     = [], []                     # size and diameter lists
        

        # ---------------------------------------------------------------------
        # The first step is to extract the "islands" from the Capability Graph,
        # which are essentially the Strong Connected Components (SCC) of the
        # undirected version of the graph.
        # ---------------------------------------------------------------------
        capU      = self.__cap.to_undirected()      # make Capability Graph undirected
        unvisited = set(capU.nodes())               # initially, no node is visited

        while len(unvisited):                       # while there are unvisited nodes
            root = unvisited.pop()                  # pick a random node
            unvisited.add( root )                   # and remove it from set
            
            nodeset = []                            # nodes in the current island

            # explore the island using DFS and obtain the node set
            for u in nx.dfs_preorder_nodes(capU, root):            
                unvisited.remove(u)                 # mark u as visited
                nodeset.append(u)                   # and add it to node set

                self.__cap.node[ u ]['island'] = n_inslands
            

            # get island as induced (directed) subgraph and relabel nodes in [0, order(G)-1] range
            graph   = self.__cap.subgraph(nodeset)    
            relabel = dict(zip(graph.nodes(), range(graph.order())))
            graph   = nx.relabel_nodes(graph, relabel)
            

            # ---------------------------------------------------------------------
            # Calculate island's diameter. Although the island is fully connected
            # in the undirected version, it's not in the directed version. Thus,
            # nx.diameter(graph) throws an exception. The diameter of the island,
            # is the longest shortest path between any two nodes.
            # ---------------------------------------------------------------------
            D = 0                                   # island's diameter

            for n in graph.nodes_iter():
                # caclulate all shortest paths from the given node
                length = nx.single_source_shortest_path_length(graph, n)
                maxlen = max(length.values())       # get the longest shortest path

                if D < maxlen: D = maxlen           # keep track of the longest among all nodes


            size.append(len(nodeset))               # island size
            diam.append( D)                         # island's diameter

            self.__islands.append( {                # store island's information
                'root'     : root,
                'size'     : graph.order(),
                'diameter' : D,
                'graph'    : graph
            } )
   
            n_inslands += 1                         # total # islands

        dbg_prnt(DBG_LVL_1, "Done.")


        # ---------------------------------------------------------------------
        # Show some statistics
        # ---------------------------------------------------------------------      
        warn("'-dd' and '-ddd' options show the 'size' and 'diameter' lists")

        emph("Capability Graph has %s islands" % bold(n_inslands))

        emph("Island sizes: max = %s, min = %s, avg = %s" % 
            (bold(max(size)), bold(min(size)), bold(1.*sum(size)/n_inslands, 'float')))

        dbg_arb(DBG_LVL_2, "Island size list", size)

        emph("Island diameters: max = %s, min = %s, avg = %s" % 
            (bold(max(diam)), bold(min(diam)), bold(1.*sum(diam)/n_inslands, 'float')))

        dbg_arb(DBG_LVL_2, "Island diameter list", diam)



    # ---------------------------------------------------------------------------------------------
    # analyze(): Perform various analyses to the islands of the Capability Graph.
    #
    # :Arg analyses: The analyses to perform (can be many)
    # :Ret: None.
    #
    def analyze( self, *analyses ):
        dbg_prnt(DBG_LVL_1, "Analyzing the Capability Graph...")

        for analysis in analyses:                   # for every different analysis
            try:
                # based on the analysis, select the appropriate function and invoke it
                func = {
                    CAP_STMT_COMB_CTR : self.__analyze_stmt_comb_ctr,
                    CAP_STMT_MIN_DIST : self.__analyze_stmt_min_dist,
                    CAP_LOOPS         : self.__analyze_loops
                }[ analysis ]


                for island in self.__islands:       # perform the analysis to every island
                    func( island['graph'] )

            except KeyError, err:
                fatal('Unknow analysis %s' % str(err))



    # ---------------------------------------------------------------------------------------------
    # analyze_island(): Analyze a specific island.
    #
    # :Arg addr: An address of any node of the island
    # :Arg analyses: The analyses to perform (can be many)
    # :Ret: None.
    #
    def analyze_island( self, addr, *analyses ):
        # ---------------------------------------------------------------------
        # Search for the island to analyze
        # ---------------------------------------------------------------------
        island_id = -1

        for _, d in self.__cap.nodes_iter(data=True):
            if d['addr'] == addr:
                island_id = d['island']
                break

        if island_id < 0:
            fatal("Node '0x%x' does not contained in any island" % addr)

        dbg_prnt(DBG_LVL_1, "Analyzing the Island %d..." % island_id)


        # ---------------------------------------------------------------------
        # Perform the analyses
        # ---------------------------------------------------------------------
        for analysis in analyses:                   # for every different analysis
            try:
                # based on the analysis, select the appropriate function and invoke it
                func = {
                    CAP_STMT_COMB_CTR : self.__analyze_stmt_comb_ctr,
                    CAP_STMT_MIN_DIST : self.__analyze_stmt_min_dist,
                    CAP_LOOPS         : self.__analyze_loops
                }[ analysis ]

                func( self.__islands[ island_id ]['graph'] )

            except KeyError, err:
                fatal('Unknow analysis %s' % str(err))



    # ---------------------------------------------------------------------------------------------
    # callback(): Invoke a callback function for every island.
    #
    # :Arg cbfunc: The callback function to invoke
    # :Ret: None.
    #
    def callback( self, cbfunc ):
        for island in self.__islands:
            cbfunc( island['graph'] )

    
    # TODO: Move these to private function sections


    # ---------------------------------------------------------------------------------------------
    # __analyze_stmt_comb_ctr(): Count the total number of combinations that K SPL statements can
    #       be chained together (repetitions of statements are allowed) on a given island.
    #    
    # :Arg island: The island graph to work on
    # :Ret: None.
    #
    def __analyze_stmt_comb_ctr( self, island ):
        dbg_prnt(DBG_LVL_1, "Starting Analysis: Statement Combinations...")


        # TODO: Check this again. Too many combinations :\
        K = 20


        # ---------------------------------------------------------------------
        # Find the total number of paths between any 2 nodes that use exactly
        # K edges. We calculate that using Dynamic Programming. Let C^k_{ij} be
        # the total number of paths from i to j with exactly k edges. Then we
        # have:
        #
        #              C^0_{ii} = 1, forall i in V
        #   C^k_{ij} = C^1_{ij} = 1, iff (i,j) in E
        #              C^k_{ij} = SUM(C^{k-1}_[xj]),  for all x adjacent to i
        #
        # We build this table in a bottom-up fashion. Time/Space Complexity is 
        # O(|V|^2 * K). We can improve space complexity by storing only the
        # last 2 K's (K and K-1).
        # ---------------------------------------------------------------------
        C = numpy.zeros((K, island.order(), island.order()), dtype=numpy.int64)
        
        for i in range(island.order()):             # initialize for K = 0
            C[0][i][i] = 1
        
        for i,j, d in island.edges_iter(data=True): # initialize for K = 1
            C[1][i][j] = 1
        
        for k in range(2, K):                       # main loop
            for i in island.nodes():
                for j in island.nodes():
                    for x in island.neighbors(i):
                        C[k][i][j] += C[k-1][x][j]

        # ---------------------------------------------------------------------
        for k in range(K):
            dbg_arb(DBG_LVL_1, "Combinations with up to %d statements:", sum(sum(C[k][:][:])))



    # ---------------------------------------------------------------------------------------------
    # __analyze_stmt_min_dist(): Calculate the minimum distance with between any two statements
    #       that have exactly K edges between on a given island.
    #
    # :Arg island: The island graph to work on
    # :Ret: None.
    #
    def __analyze_stmt_min_dist( self, island ):
        '''
        B = { }

        # enumerate all simple paths from i to j 
        # WARNING: O(n!) complexity !!!
        for i in island.nodes_iter():
            for j in island.nodes_iter():
                if i == j: continue

                for x in nx.all_simple_paths(island, i, j):
 
                    A = [island[a][b]['weight'] for a,b in zip(x, x[1:])]

                    B.setdefault(len(x), []).append(sum(A))
        '''


        dbg_prnt(DBG_LVL_1, "Starting Analysis: Statement Minimum Distances...")


        K = 20

        # ---------------------------------------------------------------------
        # Find the minimum distance between any 2 nodes that use exactly K edges.
        # This is very similar with the algorithm in __analyze_stmt_comb_ctr(),
        # but with different Dynamic Programming equations:
        #
        #              M^0_{ii} = 0, forall i in V
        #   M^k_{ij} = M^1_{ij} = weight[i][j], iff (i,j) in E
        #              M^k_{ij} = MIN(M^k_[ij], weight[i][x] + M^{k-1}_{xj}), 
        #                                              for all x adjacent to i
        # ---------------------------------------------------------------------
        M = numpy.full((K, island.order(), island.order()), dtype=numpy.int32, fill_value=INFINITY)
        

        for i in range(island.order()):             # initialize for K = 0
            M[0][i][i] = 0
        
        for i,j, d in island.edges_iter(data=True): # initialize for K = 1
            M[1][i][j] = d['weight']
        
        for k in range(2, K):                       # main loop
            for i in island.nodes():
                for j in island.nodes():
                    for x in island.neighbors(i):                        

                        M[k][i][j] = min(M[k][i][j], island[i][x]['weight'] + M[k-1][x][j])

        # ---------------------------------------------------------------------
        for k in range(K):
            m = numpy.min(M[k][:][:])            
            if m == INFINITY: break

            dbg_prnt(DBG_LVL_1, "Min shortest path with up to %d statements: %d" % (k, m))


    # ---------------------------------------------------------------------------------------------
    # __analyze_loops(): Analyze the loops on an a given island.
    #    
    # :Arg island: The island graph to work on
    # :Ret: None.
    #
    def __analyze_loops( self, island ):
        warn('Loop analysis is not supported yet')
       

# -------------------------------------------------------------------------------------------------

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
# coreutils.py:
#
# This module contains basic declarations and functions that are being used by all other modules.
#
# -------------------------------------------------------------------------------------------------
from config import *                                # load configuration options

from graphviz import Digraph
import networkx as nx
import datetime
import random
import re
import angr
import textwrap




# -------------------------------------------------------------------------------------------------

''' =========================================================================================== '''
'''                                    CONSTANT DECLARATIONS                                    '''
''' =========================================================================================== '''

# -------------------------------------------------------------------------------------------------
RETURN_SUCCESS     = 0                              # return code for success
RETURN_FAILURE     = -1                             # return code for failure

DBG_LVL_0          = 0                              # debug level 0: Display no information
DBG_LVL_1          = 1                              # debug level 1: Display minimum information
DBG_LVL_2          = 2                              # debug level 2: Display basic information
DBG_LVL_3          = 3                              # debug level 3: Display detailed information
DBG_LVL_4          = 4                              # debug level 3: Display all information

INFINITY           = 9999999                        # value of infinity

START_PC           = 0                              # PC of the for the 1st statement

ADDR2NODE          = { }                            # map addresses to basic block nodes
ADDR2FUNC          = { }                            # map basic block addresses to their functions
STR2BV             = { }                            # map strings to bitvectors


# WARNING: be very careful how to set rbp
FRAMEPTR_BASE_ADDR = RSP_BASE_ADDR + 0xc00          # base address of rbp (when it's used)

HARDWARE_REGISTERS = [                              # x64 hardware registers
    'rax', 'rdx', 'rcx', 'rbx', 'rdi', 'rsi', 'rsp', 'rbp',
    'r8',  'r9',  'r10', 'r11', 'r12', 'r13', 'r14', 'r15' 
]

SYM2ADDR = { }

SYMBOLIC_FILENAME = 'foo.txt'                       # filename for the symbolic execution to use



# -------------------------------------------------------------------------------------------------

''' =========================================================================================== '''
'''                                     AUXILIARY FUNCTIONS                                     '''
''' =========================================================================================== '''

# -------------------------------------------------------------------------------------------------
dbg_lvl = DBG_LVL_0                                 # initially, debug level is set to 0


# -------------------------------------------------------------------------------------------------
# set_dbg_lvl(): Set the current debug level. This is a small trick to share a variable between
#   modules. We set the debug level once during startup, so we don't have to carry it around the
#   modules.
# 
# :Arg lvl: Desired debug lebel.
# :Ret: None.
#
def set_dbg_lvl( lvl ):
    global dbg_lvl                                  # use the global var     
    if lvl: dbg_lvl = lvl                           # set it accordingly (if lvl is proper)



# ---------------------------------------------------------------------------------------------
# to_uid(): Cast program counter (PC) to unique ID (UID).
#
# :Arg pc: The program counter
# :Ret: The uid.
#
def to_uid( pc ):
    if not re.match(r'^@__[0-9]+$', pc):            # verify pc
        raise Exception("Invalid Program counter '%s'." % pc)

    return int(pc[3:])                              # simply drop the first 3 characters



# ---------------------------------------------------------------------------------------------
# pretty_list(): Cast a list into a pretty string, for displaying to the user. This can be
#       also done using join(), but code starts getting ugly when we have to cast each element.
#
# :Arg uglylist: The list to work on
# :Ret: A string containing a pretty "join" of the list.
#
def pretty_list( uglylist, delimiter=' - '):
    pretty = ''                                     # the final string

    for elt in uglylist:
        if isinstance(elt, int) or isinstance(elt, long):
            pretty += delimiter + '%x' % elt

        elif isinstance(elt, str):
            pretty += delimiter + elt

        elif isinstance(elt, angr.analyses.cfg.cfg_node.CFGNode):
            pretty += delimiter + '%x' % elt.addr

        else:
            fatal("Unsupported list element type'%s'" % str(type(elt)))


    # drop the first delimiter (if exists) and return string
    return pretty[len(delimiter):] if pretty else ''



# -------------------------------------------------------------------------------------------------
# to_edges(): Convert a path to edges. That is, given the path P = ['A', 'B', 'C', 'D', 'E'],
#       return its edges: [('A', 'B'), ('B', 'C'), ('C', 'D'), ('D', 'E')]. Function is a 
#       generator, so it returns one edge at a time.
#
#       Note that function can be implemented with a single line: "return zip(path, path[1:])".
#       However, the problem with zip() is that it creates 2 more copies of the list, which is
#       not very efficient, when paths are long and all we want is to iterate over the edges.
#
# :Arg path: A list that contains a path
# :Arg direction: Edge direction (forward/backward)
# :Ret: Function is a generator. Each time the next edge from the path is returned.
#
def to_edges( path, direction='forward' ):
    if len(path) < 2: return                        # nothing to do

    u = path[0]                                     # get the 1st node
    for v in path[1:]:
        if   direction == 'forward':  yield (u, v)  # return the previous and the current node
        elif direction == 'backward': yield (v, u)  # or return the backward edge

        u = v                                       # update previous node



# -------------------------------------------------------------------------------------------------
# mk_reverse_adj(): Given an Adjacency List, make the Reverse Adjacency List.
#
# :Arg adj: The Adjacency List
# :Ret: Function returns a dictionary which encodes the Reverse Adjacency List.
#
def mk_reverse_adj( adj ):        
        radj = { }

        for a, b in adj.iteritems():
            for c in b:
                radj.setdefault(c, []).append(a)

        return radj



# -------------------------------------------------------------------------------------------------
# disjoint(): Check whether two sets are disjoint or not.
#
# :Arg set_a: The first set
# :Arg set_b: The second set
# :Ret: If sets are disjoint, function returns True. Otherwise it returns False.
#
def disjoint( set_a, set_b ):
    for a in set_a:
        for b in set_b:
            if a == b: 
                return False

    return True



# -------------------------------------------------------------------------------------------------
# log(): Log execution statistics to a file.
#
# :Arg msg: Message to log
# :Ret: None.
#
def log( msg ):
    pass                                            # not used.



# -------------------------------------------------------------------------------------------------

''' =========================================================================================== '''
'''                                     PRINTING FUNCTIONS                                      '''
''' =========================================================================================== '''

# -------------------------------------------------------------------------------------------------
# now(): Get current time. Time is prepended to every print statement.
#
# :Ret: A string containing the current time.
#
def now():
    return '[%s]' % datetime.datetime.now().strftime("%H:%M:%S,%f")[:-3]



# -------------------------------------------------------------------------------------------------
# dbg_prnt(): Display a debug message to the user.
#
# :Arg lvl: Message's debug level
# :Arg msg: Message to print
# :Arg pre: Message prefix (OPTIONAL)
# :Ret: None.
#
def dbg_prnt( lvl, msg, pre='[+] ' ):
    if dbg_lvl >= lvl:                              # print only if you're in the right level
        print now(), pre + msg



# -------------------------------------------------------------------------------------------------
# dbg_arb(): Display a debug message followed by an arbitrary data structure to the user.
#
# :Arg lvl: Message's debug level
# :Arg msg: Message to print
# :Arg arb: The arbitrary data struct (e.g., list, dict) to print
# :Arg pre: Message prefix (OPTIONAL)
# :Ret: None.
#
def dbg_arb( lvl, msg, arb, pre='[+] ' ):
    if dbg_lvl >= lvl:                              # print only if you're in the right level
        print now(), pre + msg, arb
    


# -------------------------------------------------------------------------------------------------
# func_name(): Convert an address to the name of its function, or
# "__unknown" if it cannot be found.
#
# :Arg addr: The address to lookup
# :Ret: Returns a string with the name of the function containing the address, or "__unknown".
#
def func_name ( addr ):
    if addr in ADDR2FUNC:
        return ADDR2FUNC[addr].name
    else:
        return "__unknown"



# -------------------------------------------------------------------------------------------------
# fatal(): This function is invoked when a fatal error occurs. It prints the error and terminates
#       the program.
#
# :Arg err: Error message to print
# :Ret: None.
#
def fatal( err ):
    print '\033[91m%s [FATAL]' % now(), err + '.\033[0m'
    exit( RETURN_FAILURE )



# -------------------------------------------------------------------------------------------------
# error(): This function is invoked when a non-fatal error occurs. It prints the error without
#       terminating the program.
#
# :Arg err: Error message to print
# :Ret: None.
#
def error( err ):
    print '\033[91m%s [ERROR]' % now(), err + '.\033[0m'
    


# -------------------------------------------------------------------------------------------------
# warn(): Print a warning.
#
# :Arg warning: Warning to print
# :Ret: None.
#
def warn( warn, lvl=DBG_LVL_0 ):
    if dbg_lvl >= lvl:                              # print only if you're in the right level
        print  '\033[93m%s [WARNING]' % now(),  warn + '.\033[0m'
    


# -------------------------------------------------------------------------------------------------
# warn(): Print an emphasized message.
#
# :Arg msg: Message to pring
# :Arg lvl: Message's debug level
# :Arg pre: Message prefix (OPTIONAL)# :Ret: None.
# :Ret: None.
#
def emph( msg, lvl=DBG_LVL_0 , pre='[*] '):
    # default mode is to print always
    if dbg_lvl >= lvl:                              # print only if you're in the right level
        print  '\033[0;32m%s' % now(), pre + msg + '\033[0m'



# -------------------------------------------------------------------------------------------------
# bold(): Emphasize a number (bold).
#
# :Arg num: Number to make bold
# :Arg ty: The type of the number (int / float)
# :Arg pad: Zero padding size (OPTIONAL)
# :Ret: The emphasized number.
#
def bold( num, ty='int', pad=None ):
    fms = 'd' if ty == 'int' else '.2f'           # select the format string (int / float)

    if not pad:
        return ("\033[1m%" + fms + "\033[21m") % num
    else:
        # this is a double format string (recursive)        
        return ("\033[1m" + (("%%%d" + fms) % pad) + "\033[21m") % num 



# -------------------------------------------------------------------------------------------------
# bolds(): Emphasize a string (bold).
#
# :Arg string: Message to make bold
# :Ret: The emphasized string.
#
def bolds( string ):
    return "\033[1m%s\033[21m" % string             # print in bold (and unbold)



# -------------------------------------------------------------------------------------------------
# rainbow(): Print a string with rainbow colors.
#
# :Arg string: Message to make rainbow.
# :Ret: None.
#
def rainbow( string ):
    RED     = lambda key : "\033[91m%c\033[0m" % key
    GREEN   = lambda key : "\033[92m%c\033[0m" % key
    YELLOW  = lambda key : "\033[93m%c\033[0m" % key
    MAGENTA = lambda key : "\033[95m%c\033[0m" % key
    CYAN    = lambda key : "\033[96m%c\033[0m" % key
   
    return ''.join([{ 0 : RED, 
                      1 : CYAN, 
                      2 : YELLOW, 
                      3 : MAGENTA, 
                      4 : GREEN 
                    }[ ctr % 5 ](ch) for ctr, ch in enumerate(string)])



# -------------------------------------------------------------------------------------------------

''' =========================================================================================== '''
'''                                GRAPH VISUALIZATION FUNCTIONS                                '''
''' =========================================================================================== '''

# -------------------------------------------------------------------------------------------------
# Visualizing Options (VO)
# -------------------------------------------------------------------------------------------------
VO_NONE            = 0x0000                         # no visualization
VO_TYPE_CFG        = 'cfg'                          # visualizion mode: CFG
VO_TYPE_DELTA      = 'delta'                        # visualizion mode: delta graph
VO_TYPE_CAPABILITY = 'cap'                          # visualizion mode: capability graph
VO_CFG             = 0x0080                         # visualize CFG
VO_CAND            = 0x0040                         # visualize candidate blocks
VO_ACC             = 0x0010                         # visualize accepted blocks
VO_CLOB            = 0x0020                         # visualize clobbering blocks
VO_PATHS           = 0x1000                         # draw execution paths (i.e., dispathcers)
VO_DRAW_INF_EDGES  = 0x2000                         # draw edges with infinite weight



# -------------------------------------------------------------------------------------------------
# _node_colors(): Color a node properly.
#
# :Arg graph: The name of the generated file.
# :Ret: If the graph is visualized successfully function returns True. Otherwise it returns
#       False.
#
class _node_colors( object ):

    # ---------------------------------------------------------------------------------------------
    #
    #
    #
    def __init__( self ):
        self.__colormap = dict()

    # ---------------------------------------------------------------------------------------------
    # 
    #
    #
    def __setitem__( self, color, nodeset ):
        for node in nodeset:
            self.__colormap[ node ] = color

    # ---------------------------------------------------------------------------------------------
    # 
    #
    #
    def __iter__( self ):
        for node, color in self.__colormap.iteritems():
            yield (node, color)

    # ---------------------------------------------------------------------------------------------
    # 
    #
    #
    def __contains__( self, node ):
        return node in self.__colormap

    # ---------------------------------------------------------------------------------------------
    # 
    #
    #
    def get_nodes( self ):
        return self.__colormap.keys()


# -------------------------------------------------------------------------------------------------



# -------------------------------------------------------------------------------------------------
# __get_dg_layers(): Get delta graph layers.
# 
# :Arg delta_graph: The delta graph
# :Ret: the list of the layers.
#
def __get_dg_layers( delta_graph ):
    return sorted( list(set([uid for uid,_ in delta_graph.nodes()])) )
    

 
# -------------------------------------------------------------------------------------------------
# __get_dg_layer_nodes(): Get the nodes from a delta graph layer.
#
# :Arg delta_graph: The delta graph
# :Arg layer_id: Layer to return
# :Ret: the list of nodes for the specified layer.
#
def __get_dg_layer_nodes( delta_graph, layer_id ):
    return sorted([addr for uid, addr in delta_graph.nodes() if uid == layer_id])
      


# -------------------------------------------------------------------------------------------------
# visualize(): Visualize a graph and save it into a (pdf) file. This function supports a
#       number of options to customise the visualization.
#
# :Arg filename: The name of the generated file.
# :Arg entry: The entry point that trace searching algorithm starts
# :Arg options: An integer that describes how the CFG should be visualized. It can be the 
#       logical OR of one or more of the following:
#
#       VO_NONE            | Do not do anything (Default)
#       VO_DRAW_CFG        | Draw the CFG
#       VO_DRAW_CANDIDATE  | Draw all candidate blocks
#       VO_DRAW_ACCEPTED   | Draw all accepted blocks
#       VO_DRAW_CLOBBERING | Draw all clobbering blocks
#       VO_DRAW_SE_PATHS   | Draw the symbolic execution paths (if any)
#       VO_SHOW_LABELS     | Show labels for blocks (their address in hex)
#       VO_HIDE_EDGES      | Do not draw any edges
#       VO_NO_FAKERET      | Do not draw the "fakeret" edges
#
# :Arg paths: If VO_DRAW_SE_PATHS is set, this argument is a list of the paths to draw
# :Ret: If the CFG is visualized successfully function returns True. Otherwise it returns
#       False.
#
def visualize( graph, gtype='', options=VO_NONE, entry=-1, filename=None, paths=set(), cur_uid=0, 
               func=None ):
                   
    G = Digraph('G', format='svg', filename=filename)

    nodes      = _node_colors()
    nodeset    = set()
    path_edges = { }
    path_nodes = set()

    '''
    if options & VO_DRAW_SE_PATHS:              # show 
        edges = []

        # convert paths (a, b, c, d) to edge sets ((a,b), (b,c), (c,d))
        for path in paths:
            u = path[0]
            
            for v in path[1:]:
                edges.append( (u, v) )
                u = v


        # draw all edges 
        nx.draw_networkx_edges(G, pos, edgelist=edges,
             edge_color='red', style='solid', arrows=False, width=1, alpha=1)
    '''

    if options & VO_PATHS:
        #   for path in paths:
        #       for u in path:
        #           path_nodes.add(u)
        #
        #   for u, v in zip(path, path[1:]):
        #        path_edges[ (u, v) ] = 1

        path_edges = paths


    # ---------------------------------------------------------------------
    # Control Flow Graph
    # ---------------------------------------------------------------------
    if gtype == VO_TYPE_CFG:
        # -------------------------------------------------------------------------------
        # First identify the set of nodes (along with the color) to visualize
        # -------------------------------------------------------------------------------

        # -------------------------------------------------------------------------------
        if options & VO_CFG:
            for node in graph.nodes():
                if func and node.addr not in func.block_addrs:
                    continue

                G.node('%x' % node.addr, fillcolor='white', shape='box', style='filled')
                nodeset.add(node.addr)

        # -------------------------------------------------------------------------------
        if options & VO_CAND:
            # nodes['yellow' ] = get_nodes('cand')
            # (<CFGNode frame_dummy+0x1f 0x40078fL[6]>, [(14, [...]), (16, [...])]),

            for node, attr in nx.get_node_attributes(graph, 'cand').iteritems():

                if func and node.addr not in func.block_addrs:
                    continue

                G.node('%x' % node.addr, label='%x' % node.addr,
                        # label='%x\n%s' % (node.addr, ', '.join(['%d' % uid[0] for uid in attr])),
                        fillcolor='yellow', shape='box', style='filled')

                nodeset.add(node.addr)

        # -------------------------------------------------------------------------------
        if options & VO_ACC:
            # nodes['lawngreen'] = ['0x%x\n%s' % (n.addr, ', '.join([str(x) for x in s]))
            #                           for n, s in get_attr('acc')]
            #
            # (<CFGNode main+0x141 0x4009c6L[17]>, [14])
            # print [(n,s) for n, s in get_attr('acc')]
           
            for node, attr in nx.get_node_attributes(graph, 'acc').iteritems():
                if func and node.addr not in func.block_addrs:
                    continue

                G.node('%x' % node.addr, label='%x' % node.addr,
                        # label='%x\n%s' % (node.addr, ', '.join(['%d' % uid for uid in attr])),                            
                        # fillcolor='lawngreen',
                        shape='doubleoctagon', style='filled, bold')

                nodeset.add(node.addr)

        # -------------------------------------------------------------------------------
        if options & VO_CLOB:        
            # nodes['orangered'] = ['0x%x\n%s' % (n.addr, ', '.join([str(x) for x in s])) 
            #                           for n, s in get_attr('clob')]
            #
            # (<CFGNode _init 0x4005d0[16]>, set([16, 14])),
            # print [(n,s) for n, s in get_attr('clob')]

            for node, attr in nx.get_node_attributes(graph, 'clob').iteritems():

                if func and node.addr not in func.block_addrs:
                    continue

                G.node('%x' % node.addr, label='%x' % node.addr,
                        # label='0x%x\n%s' % (node.addr, ', '.join(['%d' % uid for uid in attr])),                            
                        fillcolor='orangered', shape='box', style='filled')

                nodeset.add(node.addr)


        # -------------------------------------------------------------------------------
        # Entry point
        # -------------------------------------------------------------------------------
        if entry != -1:
            G.node('%x' % entry, shape='box')  #, style='filled', fillcolor='gray')                
            


        # -------------------------------------------------------------------------------
        # Then, draw the edges
        # -------------------------------------------------------------------------------

        # subgraph = graph.subgraph( nodes.get_nodes() )    
        # print graph.nodes()

        for u, v in graph.edges_iter():
            #   if u.addr in nodes and v.addr in nodes:
            #       G.edge('0x%x' % u.addr, '0x%x' % v.addr)

            if u.addr in nodeset and v.addr in nodeset:
                if (u.addr, v.addr) in path_edges:
                    pass
                    # G.edge('0x%x' % u.addr, '0x%x' % v.addr, #label='%d' % path_edges[u.addr, v.addr],
                    #        color='deepskyblue', style='setlinewidth(3)', font='Arial Black', 
                    #        fontsize='30'#, fontcolor='purple'
                    # )
                else:
                    G.edge('%x' % u.addr, '%x' % v.addr)


        for (u, v) in path_edges:
            path_nodes.add( u )
            path_nodes.add( v )

        for (u, v) in path_edges:
            G.edge('%x' % u, '%x' % v, # label='%d' % path_edges[u.addr, v.addr],
                    color='blue', style='setlinewidth(5)', font='Arial Black', 
                    fontsize='30', fontcolor='purple'
            )
  
        '''
        G.node('foo', label='', shape='doubleoctagon', fillcolor='white', style='filled, bold')
        G.node('bar', label='      ', shape='ellipse')
        G.node('baz', label='', shape='box')

        G.node('A', label='', color='white', fillcolor='white')
        G.node('B', label='', color='white', fillcolor='white')

        G.edge('A', 'B', color='blue', style='setlinewidth(5)')
        '''


    # -----------------------------------------------------------------------------------
    # Delta Graph
    # -----------------------------------------------------------------------------------
    elif gtype == VO_TYPE_DELTA:
        # add invisible edges between layers to align them
        for layer_from, layer_to in to_edges(__get_dg_layers(graph)):
            nodes_1 = __get_dg_layer_nodes(graph, layer_from)
            nodes_2 = __get_dg_layer_nodes(graph, layer_to)            

            # skip some nodes from the first layer (too many)
            # whitelist = [0x41dfe3, 0x41e02a, 0x407a1c, 0x403d4b, 0x403d6c, 0x407887, 0x404D5A]

            if layer_from == 2:
                nodes_1 = [n for n in nodes_1 if n in whitelist]
           
            if layer_to == 2:
                nodes_2 = [n for n in nodes_2 if n in whitelist]
 
            for n in nodes_1:
                for m in nodes_2:                      
                    G.edge('%d-%x' % (layer_from, n), '%d-%x' % (layer_to, m), color='transparent')


        # test edges
        #
        # G.edge('6-403e4e', '16--1', color='transparent')
        # G.edge('6-403fd9', '16--1', color='transparent')
        #
        # G.node('6-999999', color='transparent', fontcolor='transparent')

        for node in graph.nodes():
            print node, graph.in_degree(node), graph.out_degree(node)
            uid, addr = node

            # skip some nodes from the first layer (too many)
            if uid == 2 and addr not in whitelist:
                print '\tDROP!'
                continue

            with G.subgraph(name='cluster_%d' % uid) as c:
                
                c.node_attr.update(style='filled', color='white')

                # c.edges([('a0', 'a1'), ('a1', 'a2'), ('a2', 'a3')])
                # c.attr(label='UID: %d' % uid, labelloc='t' if uid == 0 else 'b' )
                c.attr(label='Statement #%d' % uid, style='setlinewidth(3)', color='gray35',
                        labeljust='l', labelloc='t', fontcolor='gray35')

                ''' 
                good = 0

                for n in graph.in_edges(node):
                    if graph[n[0]][node]['weight'] != INFINITY:
                        good += 1
                
                for n in graph.out_edges(node):
                    if graph[node][n[1]]['weight'] != INFINITY:
                        good += 1

                if good:
                    c.node('%d-%x' % (uid, addr), label='0x%x' % addr)
                '''
               
                c.node('%d-%x' % (uid, addr), font='Arial Black', 
                        label=('%x' % addr) if addr > 0 else '    -1    ')


                # G.node('%d-%x' % (uid, addr), fillcolor='white', shape='box', style='filled')                
                

        dbg_arb(DBG_LVL_2, "Path Edges:", path_edges)

        for u, v, w  in graph.edges(data=True):
            print 'Edge', u, ' -> ', v
            
            if (u, v) in path_edges:
                G.edge('%d-%x' % u, '%d-%x' % v, label=('%d' % w['weight']) if v[0] != 16 else '0',
                        color='blue', style='setlinewidth(3)', font='Arial Black', 
                        fontsize='14', fontcolor='blue', constraint='false' 
                )

                G.node('%d-%x' % u, color='blue', fontcolor='blue', style='setlinewidth(3)')
                G.node('%d-%x' % v, color='blue', fontcolor='blue', style='setlinewidth(3)')

            else:
                if u[0] == 2 and u[1] not in whitelist:
                    continue

                if v[0] == 2 and v[1] not in whitelist:
                    continue

                if v[0] == 16:
                    G.edge('%d-%x' % u, '%d-%x' % v, fontsize='14', label='0', constraint='false' )    
                
                elif w['weight'] != INFINITY:
                    G.edge('%d-%x' % u, '%d-%x' % v, fontsize='14', label='%d' % w['weight'], 
                            constraint='false' )    

                elif options & VO_DRAW_INF_EDGES:
                    G.edge('%d-%x' % u, '%d-%x' % v, label='INF', constraint='false' )    
        pass



    # -------------------------------------------------------------------------
    # Capability Graph
    # ------------------------------------------------------------------------- 
    elif gtype == VO_TYPE_CAPABILITY:
        # TODO: 1. Elaborate on call, etc.
        #       2. No edge with weigth=0 on stmt on the same addr

        get_attr  = lambda attr  : nx.get_node_attributes(graph, attr).iteritems()
        get_nodes = lambda blkty : set([n.addr for n, _ in get_attr(blkty)])
        get_stmt  = lambda stmt  : set([n for n, s in get_attr('type') if s == stmt])


        for node, attr in graph.nodes(data=True):            
            color = {
                'regset' : 'whitesmoke',
                'regmod' : 'limegreen',
                'call'   : 'turquoise2',
                'cond'   : 'maroon1'
            }[ attr['type'] ]

            G.node('%d' % node, label='0x%x\n%d - %s' % (attr['addr'], node, attr['type']),
                fillcolor=color, shape='box', style='filled')
     
        for u, v, w in graph.edges_iter(data=True):
            G.edge('%d' % u, '%d' % v, label='%d' % w['weight'])
   

    # ---------------------------------------------------------------------
    # Save results to file
    # --------------------------------------------------------------------- 
    #  G.view()
    
    try:
        G.save(filename + '.dot')
        G.render(filename, view=True)
    except IOError, err:
        error("Cannot save figure: %s" % str(err))
        return False                            # failure

    dbg_prnt(DBG_LVL_1, "Done. Graph saved as %s" % filename + '.pdf')
 
    return True



# -------------------------------------------------------------------------------------------------

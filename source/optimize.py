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
# optimize.py
#
# This module performs several optimizations to the generated IR that aim to increase the chances
# of finding a trace (for the given IR) on the target CFG.
#
# -------------------------------------------------------------------------------------------------
from coreutils import *

import compile  as C
import calls
import networkx as nx
import itertools
import struct
import copy


# -------------------------------------------------------------------------------------------------
# optimize: This is the main class (derived from "compile") that optimizes the generated IR.
#
class optimize( C.compile ):
    ''' ======================================================================================= '''
    '''                                   INTERNAL FUNCTIONS                                    '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __get_stmt_regs(): This function gets all registers that are being used in a statement.
    #
    # :Arg stmt: The statement to get registers from.
    # :Ret: A list of all registers (int) that are being used by the statemet
    
    def __get_stmt_regs( self, stmt ):
        if   stmt['type'] == 'varset': return []
        elif stmt['type'] == 'regset': return [stmt['reg']]
        elif stmt['type'] == 'regmod': return [stmt['reg']]
        elif stmt['type'] == 'memrd' : return [stmt['reg'], stmt['mem']]
        elif stmt['type'] == 'memwr' : return [stmt['mem'], stmt['val']]
        elif stmt['type'] == 'call'  : return stmt['args']
        elif stmt['type'] == 'cond'  : return [stmt['reg']]
        else:
            return []



    # ---------------------------------------------------------------------------------------------
    # __depends(): This function checks whether statement s2 depends on statement s1. Dependencies
    #       occur at the registers and they are defined as follows:
    #           [0]. entry  -> *            (depends on everything)
    #           [1]. varset -> varset 
    #           [2]. regset -> regset / varset
    #           [3]. regmod -> regset / memrd
    #           [4]. memrd  -> regset / regmod
    #           [5]. memwr  -> regset / regmod / memrd
    #           [6]. call   -> regset / regmod / memrd
    #           [7]. cond   -> regset / regmod / memrd
    #           [8]. *      -> return       (everything depends on it)
    #
    # :Arg s1: First statement
    # :Arg s2: Second statement
    # :Ret: True if s2 depends on s1. False otherwise.
    #
    def __depends( self, s1, s2 ):
        s1_regs = set(self.__get_stmt_regs(s1))
        s2_regs = set(self.__get_stmt_regs(s2))


        # ---------------------------------------------------------------------
        # Case 0: Check whether s1 is the entry (pseudo)statement (and avoid cycles)
        if s1['type'] == 'entry' and s2['type'] != 'entry':
            return True


        # ---------------------------------------------------------------------
        # Case 1: Check whether any of the reference names matches
        elif s1['type'] == 'varset' and s2['type'] == 'varset':
            for val in s2['val']:                
                if isinstance(val, tuple) and val[0] == s1['name']:           
                    return True                     # yes, it depends


        # ---------------------------------------------------------------------
        # Case 2: Check whether any of the reference names matches
        elif s1['type'] == 'varset' and s2['type'] == 'regset':
            if isinstance(s2['val'], tuple):
                for val in s1['val']:               # value dependency
                    if isinstance(val, tuple) and val[0] == s2['val'][0]:
                        return True

                if s1['name'] in s2['val'][0]:      # name dependency
                    return True
        

        # ---------------------------------------------------------------------
        # Case 8: Check whether s2 is the return (pseudo)statement (and avoid cycles)
        elif s1['type'] != 'return' and s2['type'] == 'return':
            return True


        # ---------------------------------------------------------------------
        # Other Cases: Check whether register matches and s2 assigment happens
        #       *after* s1 (we can compare UIDs as we're within a group).
        elif (s1_regs & s2_regs) and s2['uid'] > s1['uid']:
            return True


        # ---------------------------------------------------------------------
        # Case 7: These are already handled, as conditional statements are not
        #       moving. Furthermore. semantic analysis has already taken care
        #       of it.

     
        return False                                # statements are independent



    # ---------------------------------------------------------------------------------------------
    # __ooo_intrl(): This is the internal function that performs the actual rearrangement of the
    #       statements. It first builds the dependence graph for the statements and then it uses
    #       a modified version of Kahn's topological sorting algorithm, to find which statements
    #       can be executed out of order. These statements are packed in the same list, so each
    #       IR statement now contains a list of statements.
    #
    # :Arg stmt_l: A list of statements to make out of order
    # :Ret: A new list with out of order statements
    #
    def __ooo_intrl( self, stmt_l ):
        if len(stmt_l) == 0: return []              # base check

        G = nx.DiGraph()                            # create a directed graph
        for s in stmt_l: G.add_node( s[0] )

        # At this point, IR has passed the semantic checks so a statement only depends on the
        # statements above it. Therefore we only care about distinct pairs (i,j).
        for i in range(0, len(stmt_l)):
            for j in range(0, len(stmt_l)):
                si = stmt_l[i]
                sj = stmt_l[j]

                if i == j:                          # a statement can't depend on itself
                    continue

                # print self.__depends(si[1][0], sj[1][0]), si[1][0], sj[1][0]
                if self.__depends(si[1][0], sj[1][0]):
                    G.add_edge( sj[0], si[0])       # if j depends on i, then add an edge


        # Now, use a modified version of Kahn's topological sorting algorithm to find out the 
        # out of order statements. At each step we extract all nodes (statements) with no
        # incoming edges and we bucket them together (these statements can be executed in any 
        # order). Then we remove these nodes (along with their edges) and we repeat, until 
        # graph becomes empty.
        # 
        # Each statement from the 2nd set depends on some statement from the 1st set and therefore,
        # it must be executed _after_ all statements from previous set.
        new_l = []                                  # ooo list
        
        dbg_arb(DBG_LVL_3, "Dependence Graph edges:", G.edges())

        while len(G) > 0:                           # while there are nodes in the dependence graph
            tG     = G.copy()                       # get a temporary copy of the graph
            stmt   = ['@__', []]                    # initialize next statement
            min_pc = INFINITY                       # min PC (start with a huge value)


            # for each node with no incoming edges
            for n in [n for n in tG.nodes() if tG.in_degree(n) == 0]:
                G.remove_node(n)                    # remove node 
                                                    # (and all adjacent edges from original graph)
                # keep track of the minimum pc
                min_pc = int(n[3:]) if int(n[3:]) < min_pc else min_pc

                # append statement to the ooo list
                stmt[1].append([s[1][0] for s in stmt_l if s[0] == n][0])

            # A jcc will jump to the first instruction of the ooo statements, so we need the min pc
            stmt[0] = stmt[0] + str(min_pc)         # update pc

            new_l.insert(0, stmt)                   # append list of statement to the new list

        return new_l                                # return that list



    # ---------------------------------------------------------------------------------------------
    # __ooo(): This optimization finds which statements can be executed out of order. By allowing 
    #       two statements to be executed out of order, we make our trace searching algorithm more 
    #       flexible, thus giving it more chances to succeed.
    #
    #       However, if we rearrange a label or a jump statement, or if we move a statement at a 
    #       different scope of a label or jump, then we'll destroy payload's execution flow. 
    #       Therefore, we fix labels and conditional jumps at their positions and we only rearrange
    #       the statements that are between them (so, we use labels and jumps as _delimiters_; this
    #       is why we need labels in the IR at this point)
    #
    # :Ret: None.
    #
    def __ooo( self  ):
        dbg_prnt(DBG_LVL_2, "Searching for Out-Of-Order statements...")
        jumps     = ['cond', 'jump']
        oldir     = copy.deepcopy(self.__ir)        # take a backup of original IR
        self.__ir = []
        cstmt_l   = []                              # current statement list


        for stmt in oldir:                          # for each statement
            s = stmt[1][0]                          # get the core statement (no ooo yet)

            if s['type'] == 'label' or s['type'] in jumps:  # we have hit a delimiter. Slice.

                # make statements out of order (also put conditional back to IR)
                self.__ir = self.__ir + self.__ooo_intrl(cstmt_l) + \
                            ([stmt] if s['type'] in jumps else [])

                cstmt_l   = []                      # clear current list

            else: cstmt_l.append(stmt)              # append any statement to current list


        if cstmt_l:                                 # do not forget the leftovers (if any)
            self.__ir += self.__ooo_intrl(cstmt_l)

        del oldir                                   # free memory

        dbg_prnt(DBG_LVL_2, "Done.")



    # ---------------------------------------------------------------------------------------------
    # __label_remove(): In case that __ooo is not invoked, we should remove the labels from the IR.
    #
    # :Ret: None.
    #
    def __label_remove( self ):
        dbg_prnt(DBG_LVL_2, "Removing labels...")

        oldir     = copy.deepcopy( self.__ir )      # no ooo => 1 tuple per IR entry
        self.__ir = []

        for stmt in oldir:                          # for each statement
            # if we have a LABEL (no ooo yet), don't copy it to the new list
            if stmt[1][0]['type'] != 'label': self.__ir.append( stmt )

        del oldir                                   # free memory

        dbg_prnt(DBG_LVL_2, "Done.")



    # ---------------------------------------------------------------------------------------------
    # __rewrite(): This optimization rewrites some function calls from equivalent groups. Thus,
    #       it increases the likelihood of finding a solution (e.g., when puts() is not available,
    #       BOPC searches for print()).
    #
    # :Ret: None.
    #
    def __rewrite( self ):
        dbg_prnt(DBG_LVL_2, "Rewriting library and system calls...")

        for stmt in self.__ir :                     # for each statement            
            if stmt[1][0]['type'] == 'call': 
            
                for group in calls.call_groups__:
                    name = stmt[1][0]['name']

                    if name in group:
                        stmt[1][0]['alt'] = [f for f in group if f != name]

        dbg_prnt(DBG_LVL_2, "Done.")

        error("Rewrite optimiazation is incomplete")



    # ---------------------------------------------------------------------------------------------
    # __future(): This function is reserved for future optimizations. 
    #
    # :Ret: None.
    #
    def __future( self ):
        warn("Add future optimizations...")



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor.
    #
    # :Ret: A class object.
    #
    def __init__( self, ir ):
        self.__ir = ir                              # IR to optimize

        super(self.__class__, self).__init__('')    # invoke base class constructor



    # ---------------------------------------------------------------------------------------------
    # __getitem__(): Get i-th statement from IR. Out-of-order statements are groups in the same 
    #       list entry, so we cannot find them in O(1) without an auxiliary data struct. For now,
    #       we simply perform a linear search.
    #
    #       This function overloads compile.__getitem__()
    #
    # :Arg idx: Index of the IR statement
    # :Ret: The requested IR statement
    # 
    def __getitem__( self, idx ):
        assert( idx >= 0 )                          # bounds checks

        for _, stmt_r in self.__ir:                 # for each IR statement list
            for stmt in stmt_r:                     # for each "parallel" statement
                if stmt['uid'] == idx: return stmt  # if index found return statement

        raise IndexError("No statement with uid = %d found" % idx )
        # return []                                 # failure. Statement not found


 
    # ---------------------------------------------------------------------------------------------
    # optimize(): Optimize the generated IR
    #
    # :Arg mode: Mode that optimizer should operate on.
    # :Ret: None.
    #
    def optimize( self, mode ):
        dbg_prnt(DBG_LVL_1, "Optimizer started. Mode: '%s'" % mode)

        try:
            # Each optimization mode, executes some functions. Based on the mode execute the 
            # appropriate sequence of functions.
            for opt in {
                'none'    : [self.__label_remove],
                'ooo'     : [self.__ooo],
                'rewrite' : [self.__rewrite],
                'full'    : [self.__ooo, self.__future]
            }[ mode ]: opt()

        except KeyError: 
            fatal("Invalid mode '%s'" % mode )      # invalid mode

        dbg_prnt(DBG_LVL_1, "Optimization completed.")


        self._calc_stats()                          # re-calculate statistics

        # At this point we can make IR immutable, as we won't make any changes to it.

        dbg_prnt(DBG_LVL_2, 'Optimized IR:')

        for pc, group in self.__ir:                 # print optimized IR
            dbg_prnt(DBG_LVL_2, '%s %s %s' % ('-'*32, pc, '-'*32))
            
            for stmt in group:
                dbg_arb(DBG_LVL_2, '', stmt)


 
    # ---------------------------------------------------------------------------------------------
    # itergroup(): Iterate over all group statements.
    #
    # :Ret: Every time function returns a different group of statement.
    # 
    def itergroup( self ):        
        for _, stmt_r in self.__ir:                 # for each IR statement list
            yield stmt_r                            # return next statement



    # ---------------------------------------------------------------------------------------------
    # get_ir(): Return the compiled IR.
    #
    # :Ret: The IR.
    #
    def get_ir( self ):
        return self.__ir



    # ---------------------------------------------------------------------------------------------
    # emit(): Emit IR and save it into a file
    #
    # :Ret: None.
    #
    def emit( self, filename ):
        dbg_prnt(DBG_LVL_1, "Writing SPL IR to a file...")    
         
        try:    
            file = open(filename + '.ir', 'w')

            for pc, stmt_l in self.__ir:
                for stmt in stmt_l:
                    opt  = '%s %s ' % (pc, stmt['type'])

                    # -------------------------------------------------------------------
                    if stmt['type'] == 'varset':
                        opt += '%s ' % stmt['name']
                        
                        for val in stmt['val']:
                            if isinstance(val, tuple): 
                                opt += 'var %s ' % val[0]
                            else:                      
                                if len(val) != 8:
                                    for i in range(0, len(val), 8):
                                        opt += 'num %s ' % val[i:i+8].encode("hex")
                                        print val[i:i+8],val[i:i+8].encode("hex")
                                else:
                                    opt += 'num %s ' % val.encode("hex")
                    # -------------------------------------------------------------------
                    elif stmt['type'] == 'regset':
                        opt += '%d %s ' % (stmt['reg'], stmt['valty'])
                        if stmt['valty'] == 'num': opt += '%d' % stmt['val']
                        else:                      opt += '%s' % stmt['val'][0]

                    # -------------------------------------------------------------------
                    elif stmt['type'] == 'regmod':
                        opt += '%d %c %d' % (stmt['reg'], stmt['op'], stmt['val'])

                    # -------------------------------------------------------------------
                    elif stmt['type'] == 'memrd':
                        opt += '%d %d' % (stmt['reg'], stmt['mem'])

                    # -------------------------------------------------------------------
                    elif stmt['type'] == 'memwr':
                        opt += '%d %d' % (stmt['mem'], stmt['val'])

                    # -------------------------------------------------------------------
                    elif stmt['type'] == 'label':
                        pass

                    # -------------------------------------------------------------------
                    elif stmt['type'] == 'call':
                        # dirty is not used at all
                        opt += '%s %s' % (stmt['name'], ' '.join('%d' % a for a in stmt['args']))

                    # -------------------------------------------------------------------
                    elif stmt['type'] == 'cond':
                        opt += '%d %s %d %s' % (stmt['reg'], stmt['op'], stmt['num'], stmt['target'])

                    # -------------------------------------------------------------------
                    elif stmt['type'] == 'jump':
                        opt += '%s' % stmt['target']

                    # -------------------------------------------------------------------
                    elif stmt['type'] == 'return':
                        # dirty is not used at all
                        opt += '%x' % stmt['target']


                    file.write( "%s\n" % opt )
                       
            file.close()
           
            dbg_prnt(DBG_LVL_1, "Done. SPL IR saved as %s" % filename + '.ir')

        except IOError, err:
            fatal("Cannot create file: %s" % str(err))    

# -------------------------------------------------------------------------------------------------

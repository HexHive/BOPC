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
# mark.py:
#
# This module is responsible for marking the CFG. To mark a basic block, this has to be abstracted
# first (otherwise marking process is still possible but very compilcated). A basic block can be
# marked as "candidate", "accepted", or "clobbering". Below are the preconditions for each 
# marking type:
#
#   candidate  : A basic block fulfils the requirements to execute one (or more) SPL statements,
#                but there is not enough information to determine whether it can truly execute
#                that statement(s).
#
#   accepted   : A basic block that can truly be used to execute one (or more) SPL statements.
#
#   clobbering : A basic block that "clobbers" (i.e., interferes) with the execution of an 
#                accepted block and therefore needs to be avoided.
#
#   failed     : Analysis on that basic block failed and therefore it should be treated as 
#                clobbering at all times.
#
# -------------------------------------------------------------------------------------------------
from coreutils import *
from calls     import *

import absblk as A

import angr
import claripy
import simuvex

import networkx as nx

import struct
import copy
import cPickle as pickle
import pprint
import math
import re



# -------------------------------------------------------------------------------------------------
# mark: This class is responsible for marking the CFG.
#
class mark( object ):
    ''' ======================================================================================= '''
    '''                                   INTERNAL FUNCTIONS                                    '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __blk_cnt(): Count the number of "functional" basic blocks in the CFG.
    #
    # :Arg avoid: A list of function names to avoid (optional)
    # :Arg which: Which basic blocks to count (default: 'all')
    # :Ret: The number of basic blocks in the CFG.
    # 
    def __blk_cnt( self, avoid=[], which='all'):     
        # ---------------------------------------------------------------------
        # Abstract method
        #
        # Count only abstracted basic blocks
        # ---------------------------------------------------------------------
        if which == 'abstract':
            return len(nx.get_node_attributes(self.__cfg.graph, 'abstr').items())

        # ---------------------------------------------------------------------
        # All method
        #
        # Count all basic blocks
        # ---------------------------------------------------------------------
        elif which == 'all':
            cnt = 0                                 # initialize counter

            for addr, func in self.__cfg.kb.functions.iteritems():
                # skip functions that are outside of the main_object, e.g.:
                #   <ExternObject Object cle##externs, maps [0x1000000:0x1008000]>,
                #   <KernelObject Object cle##kernel,  maps [0x3000000:0x3008000]>
                if addr < self.__proj.loader.main_object.min_addr or \
                   addr > self.__proj.loader.main_object.max_addr:
                        continue

                if func.name in avoid:              # you may need to exclude some functions
                    continue            
                

                for bb in func.block_addrs:         # count them 1 by 1 (len() doesn't work)
                    cnt += 1

            return cnt

        # ---------------------------------------------------------------------
        # Any other method should raise an error
        # ---------------------------------------------------------------------
        else: 
            fatal("Unknown method")



    # ---------------------------------------------------------------------------------------------
    # __blk_iter(): Iterate over basic blocks. This function is a generator over "all" basic
    #       blocks in the CFG.
    #
    # :Arg avoid: A list of function names to avoid (optional)
    # :Arg method: Iteration method (block/node/abstracted)
    # :Ret: Every time function returns with either the address of the next basic block 
    #       ('block' method), or with a tuple (node, attributes) of the next basic block in the
    #       CFG ('node' and 'abstracted' methods).
    # 
    def __blk_iter( self, avoid=[], method='block' ):
        # ---------------------------------------------------------------------
        # Block method
        #
        # Iterate over each function and for each function iterate over block
        # addresses.
        # ---------------------------------------------------------------------
        if method == 'block':
            # iterate over each function
            for addr, func in self.__cfg.kb.functions.iteritems():
                # skip functions that are outside of the main_object, e.g.:
                #   <ExternObject Object cle##externs, maps [0x1000000:0x1008000]>,
                #   <KernelObject Object cle##kernel,  maps [0x3000000:0x3008000]>
                if addr < self.__proj.loader.main_object.min_addr or \
                   addr > self.__proj.loader.main_object.max_addr:
                        continue

                if func.name in avoid:              # you may need to exclude some functions
                    dbg_prnt(DBG_LVL_3, "Skipping function '%s'!" % func.name)
                    continue            


                # iterate over basic blocks for each function (sort them to ease debugging)
                for bb in sorted(func.block_addrs):                                
                    yield bb                        # return address of the next block


        # ---------------------------------------------------------------------
        # Node method
        #
        # Iterate over all nodes in CFG directly.
        # ---------------------------------------------------------------------
        elif method == 'node':
            avoid_addr = { }                        # set of avoided functions

            # iterate over each function
            for addr, func in self.__cfg.kb.functions.iteritems():
                if func.name in avoid:
                    avoid_addr[ addr ] = 1          # mark blocks that you want to avoid


            # now iterate over nodes
            for node, attr in self.__cfg.graph.nodes_iter(data=True):
                # skip functions that are outside of the main_object, e.g.:
                #   <ExternObject Object cle##externs, maps [0x1000000:0x1008000]>,
                #   <KernelObject Object cle##kernel,  maps [0x3000000:0x3008000]>
                if node.addr < self.__proj.loader.main_object.min_addr or \
                   node.addr > self.__proj.loader.main_object.max_addr:
                        continue

                if node.addr in avoid_addr:         # if block is blacklisted,
                    continue                        # skip it

                yield node, attr                    # return tuple for that node


        # ---------------------------------------------------------------------
        # Abstract method
        #
        # Iterate over abstracted basic blcoks
        # ---------------------------------------------------------------------
        elif method == 'abstract':
            for node, attr in nx.get_node_attributes(self.__cfg.graph, 'abstr').iteritems(): 
                yield node, attr                    # return tuple for the abstracted block


        # ---------------------------------------------------------------------
        # Any other method should raise an error
        # ---------------------------------------------------------------------
        else: 
            fatal("Unknown method")



    # ---------------------------------------------------------------------------------------------
    # __reg_filter(): Apply a filter to a given hardware register. Although tt's better to apply
    #       this function on absblk, it's harder to make changes once abstractions are generated.
    #
    # :Arg reg: A register to check
    # :Ret: If filter discards register, function returns False. Otherwise it returns True.
    #
    def __reg_filter( self, reg ):
        # drop register mappings that use rsp (or rbp if configured)
        if reg == 'rsp' or reg == 'rbp' and not MAKE_RBP_SYMBOLIC:
            dbg_prnt(DBG_LVL_4, "A virtual register cannot be mapped to '%s'" % 
                                bolds(reg))

            return False                            # can't pass through the filter

        return True                                 # register not discarded



    # ---------------------------------------------------------------------------------------------
    # __imm_addr(): Check if an address dereference stays immutable during block execution.
    #       Consider the following example:
    #
    #           .text:00000000004008C0 add     eax, ebx
    #           .text:00000000004008C2 mov     cs:foo, eax
    #           .text:00000000004008C8 mov     eax, cs:foo
    #
    #       Here, although the value of eax is loaded from memory, we have no control over it, as
    #       the same memory cell is being written by another register
    #
    #
    # :Arg address: Address to check
    # :Arg abstr: The whole block abstractions
    # :Ret: If address is immutable function returns True. Otherwise it returns False.
    #
    def __imm_addr( self, address, abstr ):
        if isinstance(address, int):
            for addr, _ in abstr['conwr']:          # check concrete writes
                if addr == address:
                    dbg_prnt(DBG_LVL_3, "Address 0x%x is not immutable." % address)
                    return False 

        else:
            for addr, _ in abstr['memwr']:          # check other writes
                if addr.shallow_repr() == address.shallow_repr():
                    dbg_prnt(DBG_LVL_3, "Address '%s' is not immutable." % addr.shallow_repr())
                    return False

        return True



    # --------------------------------------------------------------------------------------------- 
    # __mk_unique(): Make an adress string unique.
    #
    # :Arg addrstr: Address string
    # :Arg sym: Symbolic variable
    # :Ret: A unique address
    #
    def __mk_unique(self, addrstr, sym):

        addrstr_orig = addrstr
        sym_orig     = sym


        if not sym:
            # we don't care about non-register addresses as their shallow_reprs are identical
            return addrstr_orig, sym_orig


        orig = addrstr
        for reg in HARDWARE_REGISTERS:
            # This is tooooo slow!
            #   orig = re.sub(r'%s_[0-9]+_64' % reg, '%s_64' % reg, orig)

            # use the compiled version instead
            orig = self.__regex[reg].sub('%s_64' % reg, orig)


        # if dereference is already there, use it
        if orig in self.__unique_derefs:
            return self.__unique_derefs[orig] # (addr, sym)


        # if unique, add it to the dictionary and return it as it is
        self.__unique_derefs[orig] = (addrstr_orig, sym_orig)

        return addrstr_orig, sym_orig



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''
   
    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor. Simply initialize variables that are required for the CFG
    #      . marking process.
    #
    # 
    # :Arg project: Instance of angr project
    # :Arg cfg: Program's CFG
    # :Arg ir: Compiled IR of the SPL payload
    # :Arg avoid: Any functions that should be avoided during marking process
    #
    def __init__( self, project, cfg, ir, avoid=[] ):
        self.__proj  = project                      # save arguments to internal variables
        self.__cfg   = cfg
        self.__ir    = ir
        self.__avoid = avoid


        self.vartab = { }                           # variable table
        self.varmap = { }                           # candidate addresses for variables        

        self.__m  = { }                             # index basic block using their entry point


        # Mapping Optimization
        self.__unique_derefs = { }                  # unique derefences
        self.__regex = { }
        for reg in HARDWARE_REGISTERS:              # boost regex computations
            self.__regex[reg] = re.compile(r'%s_[0-9]+_64' % reg)


        self.__rg = nx.Graph()

        self.__rg.add_nodes_from(['__r%d' % i for i in range(8)], bipartite=0)      
        self.__rg.add_nodes_from(HARDWARE_REGISTERS, bipartite=1)

        # create a mapping between basic blocks (nodes) and their entry points (addresses)
        for node, _ in self.__cfg.graph.node.iteritems():
            self.__m[ node.addr ] = node



    # --------------------------------------------------------------------------------------------- 
    # abstract_cfg(): Iterate over CFG and "abstract" its basic blocks.
    #
    # :Ret: None. Any operations are directly applied to the CFG.
    #
    def abstract_cfg( self ):
        dbg_prnt(DBG_LVL_1, "Basic block abstraction process started.")

        nnodes    = self.__blk_cnt(self.__avoid)    # total number of nodes
        counter   = 1
        completed = 0


        # for each basic block in cfg
        for addr in self.__blk_iter(self.__avoid, 'block'):  
            dbg_prnt(DBG_LVL_3, "Abstracting block at 0x%x (%d/%d)..." % (addr, counter, nnodes))

            try:
                # apply abstraction to the basic block that starts at "addr"
                abstr = A.abstract_ng(self.__proj, addr)

                # print 'ADDR', hex(addr)
                # for a,b in abstr:
                #     print '\t', a, b
                # 
                # exit()


                # Abstraction is a process that needs to be done only once. 
                # Cache all abstractions, to avoid recalculating them later on.
                self.__cfg.graph.add_node(ADDR2NODE[addr], abstr={n:a for n,a in abstr})

                del abstr                           # release object to save memory

            except Exception, err:
                warn("Symbolic Execution at block 0x%x failed: '%s' Much sad :( "
                     "Skipping current block..." % (addr, str(err)))

                # because we don't know what's going on in this block, we simply discard it
                self.__cfg.graph.add_node(ADDR2NODE[addr], fail=1)

            counter += 1


            # show current progress (%)
            percent = math.floor(100. / nnodes * counter)
            if completed < percent:
                completed = percent            
                dbg_prnt(DBG_LVL_2, "%d%% completed" % completed)

        dbg_prnt(DBG_LVL_1, "Done.")



    # --------------------------------------------------------------------------------------------- 
    # save_abstractions(): Doing a symbolic execution on every basic block in the CFG is a very
    #       time consuming operation. The abstraction process is independent of the SPL program,
    #       saving the abstractions can save a lot of time when testing multiple SPL programs on
    #       the same binary. This function dumps all abstractions into a file
    #
    # :Arg filename: Name of the file
    # :Ret: If saving was successful, function returns True. Otherwise an error message is 
    #       displayed and function returns False.
    #
    def save_abstractions( self, filename ):
        dbg_prnt(DBG_LVL_1, "Saving basic block abstractions to a file...")

        abstr = { }                                 # place abstractions here
        fail  = set()                               # and failures here


        # collect all abstractions
        for node, attr in nx.get_node_attributes(self.__cfg.graph,'abstr').iteritems(): 
            abstr[node.addr] = attr

        # collect all failures
        for node, _ in nx.get_node_attributes(self.__cfg.graph,'fail').iteritems(): 
            fail.add(node.addr)

        try:
            output = open(filename + '.abs', 'wb')  # create the file
            pickle.dump(abstr, output, 0)           # pickle dictionary using protocol 0.
            pickle.dump(fail,  output, 0)
            output.close()

        except IOError, err:                        # error is not fatal, so don't abort program
            warn("Cannot save abstractions: %s" % str(err))
            return False

    
        dbg_prnt(DBG_LVL_1, "Done.")

        return True                                 # success!


        
    # --------------------------------------------------------------------------------------------- 
    # load_abstractions(): Load abstractions from a file that was created by save_abstractions().
    #
    # :Arg filename: Name of the file
    # :Ret: If loading was successful, function returns True. Otherwise a fatal error is generated.
    #
    def load_abstractions( self, filename ):
        dbg_prnt(DBG_LVL_1, "Loading basic block abstractions from file...")

        abstr = { }                                 # place abstractions here
        fail  = set()                               # and failures here


        try:
            pklfile = open(filename + '.abs', 'rb') # open the file
            abstr = pickle.load(pklfile)            # load dictionary
            fail  = pickle.load(pklfile)            # and failures

            # pprint.pprint(abstr)
            pklfile.close()

        except IOError, err:                        # error is fatal, as we can't proceed
            fatal("Cannot load abstractions: %s" % str(err))
            

        # now iterate over nodes and place abstractions to the file
        for node, attr in self.__cfg.graph.nodes(data=True):
            if node.addr in abstr:
                # dbg_arb(DBG_LVL_3, "Abstractions for block 0x%x:" % node.addr, abstr[node.addr])
                self.__cfg.graph.add_node(ADDR2NODE[node.addr], abstr=abstr[node.addr])
            

            if node.addr in fail:
                dbg_prnt(DBG_LVL_3, "Analysis for block 0x%x failed :(" % node.addr)

                self.__cfg.graph.add_node(ADDR2NODE[node.addr], fail=1)


        dbg_prnt(DBG_LVL_1, "Done.")

        return True                                 # success!



    # ---------------------------------------------------------------------------------------------
    # mark_candidate(): Iterate over abstracted basic blocks and identify all candidate ones. A 
    #       basic block is a candidate when it can potentially execute any IR statement(s). However
    #       at this point we don't know yet whether this block can be really used to execute any
    #       statements; it only fulfils the requirements.
    #
    # :Arg forced_mapping: TODO
    # :Ret: If marking is possible (i.e., enough candidate blocks), then function returns True. 
    #       Otherwise it returns False. Also any operations are directly applied to the CFG.
    #
    def mark_candidate( self, forced_mapping=[] ):
        dbg_prnt(DBG_LVL_1, "Searching CFG for candidate basic blocks...")


        # ---------------------------------------------------------------------
        # Create vartab from 'varset' statements
        # ---------------------------------------------------------------------
        dbg_prnt(DBG_LVL_2, "Creating vartab...")

        for stmt in [s for s in self.__ir if s['type'] == 'varset']:
            self.vartab[ stmt['name'] ] = stmt['val']

        dbg_prnt(DBG_LVL_2, "Done.")       


        nnodes  = self.__blk_cnt(self.__avoid, 'abstract')
        counter = 1
        

        # ---------------------------------------------------------------------
        # Check for forced mappings first
        # ---------------------------------------------------------------------
        if forced_mapping:
            dbg_prnt(DBG_LVL_1, "Applying forced mapping ...")

            warn("No check is made against arguments! %s" % str(forced_mapping))


            # self.__rg is empty
            for vr, hw in forced_mapping:
                # TODO: check if vr is in the form __r[0-7]

                if not re.search(r'^__r.*', vr):    # check registers only
                    continue

                # make node immutable
                nx.set_node_attributes(self.__rg, 'immutable', {vr:1})        
                self.__rg.add_edge(vr, hw, var=set())


        # ---------------------------------------------------------------------
        # iterate over abstracted basic blocks
        for node, abstr in self.__blk_iter(self.__avoid, 'abstract'):  
            addr = node.addr

            dbg_prnt(DBG_LVL_3, "Analyzing block at 0x%x (%d/%d)..." % (addr, counter, nnodes))

            cand = []                               # set of statement for that block

            for stmt in self.__ir:                  # check for which statements block is candidate
                match = []

                # -----------------------------------------------------------------------
                # Statement 'varset'
                #
                # Variable assignments do not require candidate blocks. Instead
                # we leverage the AWP, to store variables anywhere in the
                # memory.
                #
                # {'type': 'varset', 'uid': 6, 'val': ['a1'], 'name': 'test'}
                # {'type': 'varset', 'uid': 8, 'val': ['\xeb\x17\x00\x00\x00\x00\x00\x00'], 
                #                   'name': 'foo'}
                # {'type': 'varset', 'uid': 10, 'val': ['\xd2\x04\x00\x00\x00\x00\x00\x00', 
                #           ('foo',), ('test',)], 'name': 'bar'}
                # -----------------------------------------------------------------------
        

                # -----------------------------------------------------------------------
                # Statement 'regset'
                #
                # {'reg': 0, 'type': 'regset', 'valty': 'num', 'val': -10, 'uid': 2}
                # {'reg': 6, 'type': 'regset', 'valty': 'var', 'val': ('bar',), 'uid': 12}
                # -----------------------------------------------------------------------
                if stmt['type'] == 'regset' and not isinstance(stmt['val'], tuple):
                    
                    for reg, data in abstr['regwr'].iteritems():
                     #   print '{',  reg, data

                        # apply register filter
                        if not self.__reg_filter(reg): continue


                        if data['type'] == 'concrete' and stmt['val'] == data['const']:
                            dbg_prnt(DBG_LVL_3, "Statement match! (__r%d) %%%s = 0x%x" % 
                                                (stmt['reg'], reg, data['const']) )

                            if 'immutable' not in self.__rg.node['__r%d' % stmt['reg']]:
                                self.__rg.add_edge('__r%d' % stmt['reg'], reg)
                            
                            # a candidate block has found
                            match.append( {'reg':reg, 'deps':[]} )


                        # if there's no concrete value, check for dereferences
                        elif data['type'] == 'deref' and self.__imm_addr(data['addr'], abstr):

                            dbg_prnt(DBG_LVL_3, "Statement match! (__r%d) %%%s = [%s]" % 
                                                (stmt['reg'], reg, data['addr']) )

                            if 'immutable' not in self.__rg.node['__r%d' % stmt['reg']]:
                                self.__rg.add_edge('__r%d' % stmt['reg'], reg)

                            # a candidate block has found
                            match.append( {'reg':reg, 'addr':data['addr'].shallow_repr(), 
                                            'sym':data['sym'],
                                            'deps':data['deps'], # 'mem':(data['addr'], stmt['val'])                                            
                                            } )


                            for a, b in abstr['symvars'].iteritems():
                                # SYM2ADDR[a] = b

                                SYM2ADDR[a.shallow_repr()] = b
                                STR2BV[a.shallow_repr()] = a

                            # Initially, varmap was designed to work with integers as addresses and
                            # all modules operate under this assumption. However, when we store
                            # bitvectors instead of integers, code starts throwing exceptions.
                            #
                            # To fix that, we do a very nasty trick: We store bitvectors as strings
                            # (so there are no exceptions anymore) and we map those strings to the
                            # real bitvectors in a global dictionary, so later on we can recover 
                            # the initial bitvectors.
                            STR2BV[ data['addr'].shallow_repr() ] = data['addr']


                            # ok forget about dependencies for now...

                
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'regset' and isinstance(stmt['val'], tuple):

                    #
                    for reg, data in abstr['regwr'].iteritems():
                    #    print '&&',  reg, data

                        # apply register filter
                        if not self.__reg_filter(reg): continue


                        if data['type'] == 'concrete' and data['writable'] == True:


                            dbg_prnt(DBG_LVL_3, "Statement match! (__r%d) %%%s = 0x%x (%s)" % 
                                                (stmt['reg'], reg, data['const'], stmt['val'][0]))

                            '''
                            dbg_prnt(DBG_LVL_0, "Statement match! (__r%d) %%%s = 0x%x (%s)" % 
                                                (stmt['reg'], reg, data['const'], stmt['val'][0]))
                            print '\t', 'ADDR', hex(addr)                            
                            print '\t', data
                            print '\t', abstr['conwr']
                            print '\t', abstr['memwr']
                            print '\n\n'

                            # apply abstraction to the basic block that starts at "addr"
                            abstr = A.abstract_ng(self.__proj, 0x403fa2)

                            print '^^^^^^^^^^^^^^^^^^^^^^'
                            abstr = A.abstract_ng(self.__proj, 0x40400A)
                            
                            exit()

                            '''

                            # Abstraction is a process that needs to be done only once. 
                            if not self.__rg.has_edge('__r%d' % stmt['reg'], reg):
                                var = set()
                            else:               
                                # get edge dict (if no edge dict = None)
                                var = self.__rg.get_edge_data('__r%d' % stmt['reg'], reg)
                                var = var['var']


                            # print '============================>', var
                            var.add( (stmt['val'][0], data['const']) )


                            if 'immutable' not in self.__rg.node['__r%d' % stmt['reg']] or\
                                self.__rg.has_edge('__r%d' % stmt['reg'], reg):
                                    self.__rg.add_edge('__r%d' % stmt['reg'], reg, var=var)

                            # a perfect match has found (with this address)
                            match.append( {'reg':reg, 'addr':data['const'], 'deps':[]} )


                            # use a set because we don't want duplicate addresses
                            self.varmap.setdefault( data['const'], 
                                        set([])).add( (data['const'], reg) )

   
                        # if there's no concrete value, check for dereferences
                        elif data['type'] == 'deref' and self.__imm_addr(data['addr'], abstr):
                            pass
                            
                            dbg_prnt(DBG_LVL_3, "Statement match! (__r%d) %%%s = [%s] (%s)" % 
                                                (stmt['reg'], reg, data['addr'], stmt['val'][0]))

                            # ----------------------------------------------------------- 
                            # Apply an optimization to reduce the large number of derefs.
                            # Ignore weird addresses that very unlikely to give a solution
                            # Yes we may miss some solutions, but the probability is very
                            # small.
                            # -----------------------------------------------------------
                            blacklist = ['SignExt', 'symbolic_read_unconstrained', 'Reverse', 'stack_']
                            skip = False

                            for word in blacklist:
                                if word in data['addr'].shallow_repr():
                                    skip = True
                                    dbg_prnt(DBG_LVL_3, "blacklisted address '%s'" % 
                                                            data['addr'].shallow_repr())
                                    break


                            # Initially, varmap was designed to work with integers as addresses and
                            # all modules operate under this assumption. However, when we store
                            # bitvectors instead of integers, code starts throwing exceptions.
                            #
                            # To fix that, we do a very nasty trick: We store bitvectors as strings
                            # (so there are no exceptions anymore) and we map those strings to the
                            # real bitvectors in a global dictionary, so later on we can recover 
                            # the initial bitvectors.
                            if not skip:
                                STR2BV[ data['addr'].shallow_repr() ] = data['addr']

                                # here we a have a double pointer...
                                addrstr = '*' + data['addr'].shallow_repr()


                                if not self.__rg.has_edge('__r%d' % stmt['reg'], reg):
                                    var = set()
                                else:               
                                    # get edge dict (if no edge dict = None)
                                    var = self.__rg.get_edge_data('__r%d' % stmt['reg'], reg)

                                    # var['var'] can be empty on regmod
                                    var = var['var'] if 'var' in var else set()


                                # -------------------------------------------------------
                                # Optimization #2:
                                #
                                # The same variables can have mappings to many different addresses,
                                # that are essentially the same. For example:
                                #   argv <-> '*<BV64 rsi_22784_64>' 
                                #            '*<BV64 rsi_41354_64>' 
                                #            '*<BV64 rsi_29142_64>'
                                #
                                # IN a
                                # -------------------------------------------------------
                                sym = data['sym']

                                addrstr, sym = self.__mk_unique(addrstr, data['sym'])


                                # store addrstr as a tuple to distinguish it from variables
                                # print '============================>', var
                                var.add( (stmt['val'][0], (addrstr,)) )


                                if 'immutable' not in self.__rg.node['__r%d' % stmt['reg']] or\
                                    self.__rg.has_edge('__r%d' % stmt['reg'], reg):
                                        self.__rg.add_edge('__r%d' % stmt['reg'], reg, var=var)


                                # a match has found (with this address)
                                match.append( {'reg':reg, 'addr':addrstr, 'deps':data['deps'], 
                                                'sym':sym
                                                # 'mem':(data['addr'], stmt['val'])
                                                } )

                                for a, b in abstr['symvars'].iteritems():
                                    SYM2ADDR[a.shallow_repr()] = b

                                    STR2BV  [a.shallow_repr()] = a


                                # use a set because we don't want duplicate addresses
                                self.varmap.setdefault(addrstr, set([])).add( (addrstr, reg) )


                # -----------------------------------------------------------------------
                # Statement 'regmod'
                #
                # {'uid': 18, 'type': 'regmod', 'reg': 6, 'op': '+', 'val': 17712}
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'regmod':

                    for reg, data in abstr['regwr'].iteritems():
                     #   print '{',  reg, data

                        # apply register filter
                        if not self.__reg_filter(reg): continue

                        if data['type'] == 'mod' and data['op'] == stmt['op'] and \
                           data['const'] == stmt['val']:

                                # match!
                                dbg_prnt(DBG_LVL_3, "Statement match! (__r%d) %%%s %s= 0x%x" % 
                                                (stmt['reg'], reg, data['op'], data['const']))
                                               

                                if 'immutable' not in self.__rg.node['__r%d' % stmt['reg']]:
                                    self.__rg.add_edge('__r%d' % stmt['reg'], reg)

                                match.append( reg ) # a perfect match has found


                # -----------------------------------------------------------------------
                # Statement 'memrd'
                #
                #  {'mem': 0, 'type': 'memrd', 'uid': 6, 'reg': 1}
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'memrd':
                
                    for reg, data in abstr['regwr'].iteritems():

                        # apply register filter
                        if not self.__reg_filter(reg): continue

                        # TODO: data['memrd'] == MEMORY_LOADSTORE_SIZE
                        if data['type'] == 'deref' and data['memrd']:

                            loadreg = data['deps'][0]

                            # match!
                            dbg_prnt(DBG_LVL_3, "Statement match! (__r%d) %%%s = *(__r%d) %%%s" % 
                                            (stmt['reg'], reg, stmt['mem'], loadreg))
                                  

                            if 'immutable' not in self.__rg.node['__r%d' % stmt['reg']] and \
                               'immutable' not in self.__rg.node['__r%d' % stmt['mem']]:
                                    self.__rg.add_edge('__r%d' % stmt['reg'], reg)
                                    self.__rg.add_edge('__r%d' % stmt['mem'], loadreg)


                            # a perfect match has found
                            match.append( (reg, loadreg) )
        

                # -----------------------------------------------------------------------
                # Statement 'memwr'
                #
                # {'uid': 6, 'type': 'memwr', 'mem': 2, 'val': 1}
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'memwr':
                    
                    for memwr in abstr['splmemwr']:
                        print 'MEMWR', memwr
                        # apply register filters
                        if not self.__reg_filter(memwr['mem']) or \
                           not self.__reg_filter(memwr['val']):
                                continue


                        # TODO: memwr['size'] == MEMORY_LOADSTORE_SIZE
                    
                        # match!
                        dbg_prnt(DBG_LVL_3, "Statement match! *(__r%d) %%%s = (__r%d) %%%s" % 
                                        (stmt['mem'], memwr['mem'], stmt['val'], memwr['val']))
                              

                        if 'immutable' not in self.__rg.node['__r%d' % stmt['mem']] and \
                           'immutable' not in self.__rg.node['__r%d' % stmt['val']]:
                                self.__rg.add_edge('__r%d' % stmt['mem'], memwr['mem'])
                                self.__rg.add_edge('__r%d' % stmt['val'], memwr['val'])


                        # a perfect match has found
                        match.append( (memwr['mem'], memwr['val']) )
        

                # -----------------------------------------------------------------------
                # Statement 'call'
                #
                # {'uid': 22, 'type': 'call', 'name': 'puts', 'args': [0], 'dirty': ['rax']}
                #
                # TODO: Comment is from old SPL
                #
                # for SYSCALL and LIBCALL statements, we only care about the name:If name 
                # matches with this one in IL statement then we have a match. We assume that
                # library calls, follow the standard calling convetions and all of their 
                # arguments are stored on registers. Therefore both syscalls and libcalls 
                # use fixed registers native registers, that we can take their values from
                # REGSET/REGMOD statements.
                #
                # However, how do we check if the arguments have the desired value? Consider
                # for example the following basic block:
                #       ...
                #       mov  rdi, 7
                #       call exit
                #
                # Also assume that we have the following SPL statement:
                #       __r0 = 5;
                #       exit( __r0 );
                #
                # In this case this basic block cannot be used for this system call as the
                # argument (7) is different from the desired (5). However this basic block
                # is marked as good for the 2nd statement and as bad for 1st. Thus, we can't
                # really use this block for the call, as it destroys the 1st statement.
                #
                # Thus all we have to do is to match the call name and let the route building
                # algorithm to decide whether this block can be actually used for the call.
                # This small demonstration shows how different parts of the algorithm
                # integrate each other, thus giving us an elegant design :)
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'call':

                    # WARNING: ab.funcall() returns the name of the function. If binary is not 
                    # stripped, ab.funcall() returns also names from user defined functions. Thus,
                    # we may have some confusion betwee library function names and user defined 
                    # functions.
                    if abstr['call'] and abstr['call']['name'] == stmt['name']:
                        dbg_prnt(DBG_LVL_3, "%s match! %s()" % (abstr['call']['type'], stmt['name']))

                        match = [ stmt['name'] ]    # make it a list for mark_accepted()
                        


                        # A call reveals a register mapping. For example the only way to 
                        # execute the SPL statement "puts(__r2)", is by mapping __r2 to rdi
                        # 
                        # So we go back to the register graph (__rg) and we drop all unnecessary
                        # edges from it (otherwise, we'll try mappings that are impossible to
                        # give a solution),
                        #
                        # To prevent future candidate blocks to add new mappings for that register,
                        # we mark the register node in __rg as 'immutable', so no new edges can
                        # be added.
                        #
                        
                        # Callign conventions:
                        #       System V AMD64 ABI: rdi, rsi, rdx, rcx, r8, r9
                        #       x64 Syscall       : rdi, rsi, rdx, r10, r8, r9

                        # get calling convention (syscalls have different CC)
                        if find_syscall(stmt['name']):
                            rsv = ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9']
                        else:
                            rsv = ['rdi', 'rsi', 'rdx', 'r10', 'r8', 'r9']

                        for hw, vr in zip(rsv, stmt['args']):
                            
                            # make node immutable
                            nx.set_node_attributes(self.__rg, 'immutable', {'__r%d' % vr:1})

                            # drop all edges but the one used by calling convention
                            for reg in self.__rg.neighbors('__r%d' % vr):
                                if reg != hw:
                                    self.__rg.remove_edge('__r%d' % vr, reg)

                        
                            # if there's no edge, add it
                            if not self.__rg.has_edge('__r%d' % vr, hw):
                                self.__rg.add_edge('__r%d' % vr, hw, var=set())

                            # a perfect match has found (with this address)


                # -----------------------------------------------------------------------
                # Statement 'cond'
                #
                # {'uid':30, 'type':'cond', 'reg':0, 'op':'>=', 'num':'0x3243', 'target':'@__26'}
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'cond':
                    # print abstr['cond']
                    try:
                        if abstr['cond'] and abstr['cond']['op'] == stmt['op'] and \
                            abstr['cond']['const'] == stmt['num']:

                                # apply register filter
                                if self.__reg_filter(abstr['cond']['reg']):

                                    dbg_prnt(DBG_LVL_3, "Conditional jump match! (__r%d) %%%s" % 
                                                        (stmt['reg'], abstr['cond']['reg']))

                                    # make it a list
                                    match = [ abstr['cond']['reg'] ]

                    except KeyError:
                        pass
                
                # -----------------------------------------------------------------------
                # Statement 'jump' or 'return'
                #
                # Just ignore them
                # -----------------------------------------------------------------------
                else: 
                    pass

                if len(match) > 0:                  # if statement was good add it to the good set
                    cand.append( (stmt['uid'], match) )
        

            if len(cand) > 0:                       # if block is good for at least 1 statement
                dbg_arb(DBG_LVL_3, "Block 0x%x is candidate when:" % addr, cand )

                # add "cand" attribute to that block (node)
                self.__cfg.graph.add_node(self.__m[addr], cand=cand)


            counter += 1

          #  break          


        # ---------------------------------------------------------------------
        # Check for forced variable mappings last
        # ---------------------------------------------------------------------
        if forced_mapping:
            dbg_prnt(DBG_LVL_1, "Applying forced (variable) mapping ...")

            warn("No check is made against arguments! %s" % str(forced_mapping))

            # self.__rg is empty
            for fvar, fval in forced_mapping:
                # TODO: check if vr is in the form __r[0-7]
                if re.search(r'^__r.*', fvar):       # check variables only
                    continue

                
                # iterate over edges
                for _, _, Vg in self.__rg.edges(data=True):                        
                    if 'var' not in Vg:
                        continue        

                    for var, val in set(Vg['var']):
                        # print var, fvar, val, fval
                        if var == fvar:
                            if isinstance(val, tuple) and val[0] != fval:
                                Vg['var'].remove( (var, val) )

                            elif isinstance(val, long) and str(val) != fval:                                
                                Vg['var'].remove( (var, val) )



        # -------------------------------------------------------------------------------
        # check if you have a sufficient number of candidate blocks
        # -------------------------------------------------------------------------------
        print '%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%', len(self.__ir)
        # for i,j in self.__rg.edge.iteritems(): print i, j

        cnt = set()

        for n, c in nx.get_node_attributes(self.__cfg.graph,'cand').iteritems(): 
            # print '0x%x' % n.addr, c

            for a, _ in c:
                cnt.add( a )


        if len(cnt) < self.__ir.nreal:
            print len(cnt), cnt 
            print self.__ir.nreal
            error("Not enough candidate blocks")
            return False



        # print self.vartab
        # print self.varmap
        # for i,j in self.varmap.iteritems():
        #       print i, [(hex(j), k) for j, k in j]

        self.map_graph = self.__rg
        
        # for edge in self.map_graph.edges(data=True):
        #     print edge

        # for node in self.map_graph.nodes(data=True):
        #     print node

        # print self.__rg.edges()

        # print variable mappings 
        for u, v, w in self.__rg.edges(data=True):
            if 'var' not in w:
                continue

            dbg_prnt(DBG_LVL_3, 'Variable mappings for register mapping %s <-> %s' % (u,v))
            for ctr, (var, val) in enumerate(w['var']):
                dbg_prnt(DBG_LVL_3, "\t#%03d '%s' <-> '%s'" % (ctr, var, val))

        return True



    # --------------------------------------------------------------------------------------------- 
    # mark_accepted(): Given a register and a variable mapping, this function identifies the
    #       subset of candidate basic blocks that can be truly used to execute SPL statements
    #       (i.e., accepted basic blocks).
    #
    # :Arg rmap: A list of (virtual reguster, hardware register) mappings
    # :Arg vmap: A list of (variable, address) mappings
    # :Ret: If there are enough accepted blocks, function returns a tuple with:
    #       1) a dictionary that has a list of all accepted basic blocks for each "real" statement. 
    #       2) rsvp. TODO: Fill in.
    #
    # Otherwise, function returns None.
    #
    def mark_accepted( self, rmap, vmap ):
        dbg_prnt(DBG_LVL_1, "Searching for accepted basic blocks...")

        # clear potential leftovers from previous attempts
        for node, _ in nx.get_node_attributes(self.__cfg.graph,'acc').items(): 
            del self.__cfg.graph.node[node]['acc']


        rmap = { vr:hw    for vr,hw    in rmap }    # cast them to dictionaries to ease searching
        vmap = { var:addr for var,addr in vmap }

        cnt = set()
    

        accepted = { }                              # dictionary of lists
        rsvp = { }                                  # reserved memory slots
        

        # iterate over candidate basic blocks
        #
        # <CFGNode main+0xff 0x4007e6L[24]> [(4, ['rax']), (3, [('rsi', 576460752303358064L)])]
        for node, attr in nx.get_node_attributes(self.__cfg.graph,'cand').iteritems(): 
            # dbg_prnt(DBG_LVL_3, "Analyzing candidate block at 0x%x..." % node.addr)
       

            acc = []

            for stmt, cand in [(self.__ir[uid], c) for (uid, cand) in attr for c in cand]:

                # "varset", "label", "jump" and "return" are not real statements and therefore
                # they do not require an accepted block.

                # print '--->', cand, stmt, attr

                # -----------------------------------------------------------------------
                # Statement 'regset'
                #
                # Examples of 'cand':
                #   {'reg': 'rax', 'deps': ['rsi'], 'addr': '<BV64 rsi_674_64>'},
                #   {'reg': 'rsp', 'deps': [], 'addr': 576460752303357928L}]
                #   {'reg': 'rax', 'deps': []}
                # -----------------------------------------------------------------------
                if stmt['type'] == 'regset':
                    isok = False


                    # check if register matches
                    if rmap[ '__r%d' % stmt['reg'] ] == cand['reg']:
                        # case #1: rax = 10
                        if 'addr' not in cand:
                            # block is accepted
                            acc.append( stmt['uid'] )
                            isok = True


                        # case #2: rax = 0x7fffffffffeffe8
                        elif isinstance(cand['addr'], long):
                            if vmap[ stmt['val'][0] ] == cand['addr']:
                                acc.append( stmt['uid'] )
                                isok = True


                        # case #3: rax = [rsi + 0x10], *(rsi + 0x10) = 10
                        # case #4: rax = [rsi + 0x10], *(rsi + 0x10) = 0x7fffffffffeffe8                        
                        elif isinstance(cand['addr'], str):
                            acc.append( stmt['uid'] )
                            isok = True

                            rsvp.setdefault(node.addr, []).append( 
                                (stmt['uid'], cand['addr'], cand['sym'], stmt['val']) 
                            )

                        # print '   $ $ $ $ $ $ $ $ RSVP:   ', rsvp[node.addr]


                    # TODO: make dependencies time-sensitive &  explain why it doesn't work
                    if isok and cand['deps']:      # are there dependencies?
                        pass
                        # make sure that dependencies are not reserved registers
                        if filter(lambda reg: reg in cand['deps'], rmap.values()):
                            pass
 
                            # this block uses a reserved register. It cannot be accepted for that
                            # statement


                # -----------------------------------------------------------------------
                # Statement 'regmod'
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'regmod':
                    if rmap['__r%d' % stmt['reg']] == cand:
                        acc.append( stmt['uid'] )


                # -----------------------------------------------------------------------
                # Statement 'memrd'
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'memrd':                                      
                    if (rmap['__r%d' % stmt['reg']], rmap['__r%d' % stmt['mem']]) == cand:
                        acc.append( stmt['uid'] )

                
                # -----------------------------------------------------------------------
                # Statement 'memwr'
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'memwr':
                    if (rmap['__r%d' % stmt['mem']], rmap['__r%d' % stmt['val']]) == cand:
                        acc.append( stmt['uid'] )

                           
                # -------------------------------------------------------------------------                     
                # Statement 'call'
                #
                # Here, we make all 'call' candidate blocks accepted and we let the 
                # regset/regmod statements to make the clobbering
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'call':
                    acc.append( stmt['uid'] )


                # -----------------------------------------------------------------------
                # Statement 'cond'
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'cond':
                    # this basic block is already candidate so no need for further checks                    
                    if rmap[ '__r%d' % stmt['reg'] ] == cand:
                        acc.append( stmt['uid'] )
            

            if len(acc) > 0:
                dbg_prnt(DBG_LVL_4, "Block 0x%x is accepted for statement(s): %s" %
                                      (node.addr, ', '.join(sorted(map(str, acc))) ) )
                
                self.__cfg.graph.node[node]['acc'] = acc
                
                for a in acc:           
                    accepted.setdefault(a, []).append(node.addr)

                cnt |= set(acc)



        # print 'accepted', accepted


        # -------------------------------------------------------------------------------
        # check if there are accepted blocks for all statements
        # -------------------------------------------------------------------------------
        if len(cnt) < self.__ir.nreal:
            #fatal("Not enough candidate blocks")
            dbg_prnt(DBG_LVL_1, "There are not enough accepted basic blocks. Much sad :(")
            return None, None                       # failure x(

       
        dbg_prnt(DBG_LVL_1, "Done.")

        return accepted, rsvp                       # success!



    # ---------------------------------------------------------------------------------------------
    # mark_clobbering(): Given a register and a variable mapping, this function identifies the set
    #       of clobbering basic blocks. Note that an accepted block can also be clobbering.
    #
    # :Arg rmap: A list of (virtual reguster, hardware register) mappings
    # :Arg vmap: A list of (variable, address) mappings
    # :Ret: TODO!!
    #       
    def mark_clobbering( self, rmap, vmap ):
        dbg_prnt(DBG_LVL_1, "Searching for clobbering basic blocks...")

        rmap = dict( map(reversed, rmap) )          # cast them to dictionaries to ease searching
        vmap = dict( map(reversed, vmap) )          # (reverse mappings)


        # clear potential leftovers from previous attempts
        for node, _ in nx.get_node_attributes(self.__cfg.graph,'clob').items(): 
            del self.__cfg.graph.node[node]['clob']


        clobbering = { }

        nnodes  = self.__blk_cnt(self.__avoid)
        counter = 1
        
        # iterate over all abstracted basic blocks
        # (__blk_iter() might return different results for 'node and 'block' methods!)
        for node, abstr in self.__blk_iter(self.__avoid, 'abstract'):
            # dbg_prnt(DBG_LVL_3, "Analyzing block at 0x%x (%d/%d)..." % (addr, counter, nnodes))

            # if node.addr != 0x416A66 and node.addr != 0x404eec:
            #       continue

            clob = set()                            # set of clobbering statements

            #
            # Question: Is block B clobbering for statement S?
            #
            # Clobbering blocks are dynamic. Write more...
            #
            try:
                acc = self.__cfg.graph.node[node]['acc']
            except KeyError:
                acc = []


            for stmt in self.__ir:
                #
                # statements 'call', 'cond', 'jump' and 'return' never have clobbering blocks
                # only 'varset', 'regset' and 'regmod' affect the others (like 'call')
                #
                
                # -----------------------------------------------------------------------
                # Statement 'varset'
                #
                # Due to the AWP, all variables are set ahead, so any basic block that 
                # modified any of the reserved memory addreses is a clobbering block
                # -----------------------------------------------------------------------
                if stmt['type'] == 'varset':
                    # print '---------', vmap
                    # for addr, size in abstr['conwr']:
                    for addr, ex in abstr['memwr']:
                        # print addr, ex
                        if addr.shallow_repr() in vmap and vmap[addr.shallow_repr()] == stmt['name']:
                            # block is clobbering
                            print hex(node.addr), 'clob for varset'
                            clob.add(stmt['uid'])
                            fatal('I should come back to that')
                            '''
                            'memwr': set([
                                (<SAO <BV64 0x7fffffffffeffb0>>, <SAO <BV64 0x40f5a5>>), 
                                (<SAO <BV64 0x7fffffffffeffd0>>, <SAO <BV64 r12_48109_64>>), 
                                (<SAO <BV64 0x7fffffffffeffc0>>, <SAO <BV64 rbx_48100_64>>), 
                                (<SAO <BV64 0x7fffffffffeffe8>>, <SAO <BV64 r15_48112_64>>), 
                                (<SAO <BV64 0x7fffffffffeffc8>>, <SAO <BV64 0x7ffffffffff01f0>>), 
                                (<SAO <BV64 0x7fffffffffeffd8>>, <SAO <BV64 r13_48110_64>>), 
                                (<SAO <BV64 0x7fffffffffeffe0>>, <SAO <BV64 r14_48111_64>>)]), 

                            'conwr': set([
                                (576460752303357888L, 64), 
                                (576460752303357896L, 64), 
                                (576460752303357928L, 64), 
                                (576460752303357904L, 64), 
                                (576460752303357872L, 64), 
                                (576460752303357912L, 64), 
                                (576460752303357920L, 64)])}
                            '''
                        # Check rsvp here? (and not during search?) Not sure :\

                        #
                        # TODO: use 'size' and check for overlaps (e.g, vmap is X, but addr is X+1)
                        #


                # -----------------------------------------------------------------------
                # Statement 'regset' or 'regmod'
                #
                # register of 'clob' type are always clobbering
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'regset' or stmt['type'] == 'regmod':
                    #for reg in [r for r in abstr['regwr'].keys() if 1]:
                    for reg in abstr['regwr'].keys():

                       # print reg, stmt, acc

                        # if register is being written and block is not accepted, then it's 
                        # clobbering 
                        if reg in rmap and rmap[reg] == '__r%d' % stmt['reg'] \
                            and stmt['uid'] not in acc:
                        # rmap[reg] != '__r%d' % stmt['reg']:
                                clob.add(stmt['uid'])


                # -----------------------------------------------------------------------
                # Statement 'memrd'                
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'memrd':                    
                    for reg in abstr['regwr'].keys():
                        if reg in rmap and \
                            (rmap[reg] == '__r%d' % stmt['reg'] or \
                             rmap[reg] == '__r%d' % stmt['mem']) \
                             and stmt['uid'] not in acc:
                        
                                clob.add(stmt['uid'])

                
                # -----------------------------------------------------------------------
                # Statement 'memwr'
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'memwr':                    
                    for reg in abstr['regwr'].keys():
                        if reg in rmap and \
                            (rmap[reg] == '__r%d' % stmt['mem'] or \
                             rmap[reg] == '__r%d' % stmt['val'])\
                             and stmt['uid'] not in acc:                        
                                clob.add(stmt['uid'])


                # -----------------------------------------------------------------------
                # Statement 'call'
                #
                # Check dirty registers (optional)
                # -----------------------------------------------------------------------
                elif stmt['type'] == 'call':
                    pass


                # -----------------------------------------------------------------------
                # Other statements
                # -----------------------------------------------------------------------
                else:
                    pass


            # ---------------------------------------------------------------------------
            # In some cases, we have to relax the "clobbering" definition. For instance
            # if we set a register twice, or if when we modify a register (e.g. __r2 -= 1)
            # in an SPL payload, the 2nd assigment will be clobbering for the 1st according
            # to our definition of clobbering blocks. However, we will end up finding no 
            # solution as the 2nd accepted blocks will always be clobbering for
            # the first.
            #
            # Such SPL statements are clobbering by themselves, so we have to go back on
            # the list of clobbering blocks and remove them.
            # ---------------------------------------------------------------------------
            clob_l = list(clob)
            
            for s2 in clob_l:
                for s1 in acc:

                    if self.__is_clobbering(self.__ir[s1], self.__ir[s2]):    
                        clob.remove(s2)                
                        break




            # ---------------------------------------------------------------------------
            # Check dirty registers. 'dirty': ['rax', 'rcx', 'rdx']
            #
            # There will be a single basic block after syscall. Mark it as clobbering for
            #       all registers in 'dirty' list
            #
            # Update: This is not needed at all. If registers/memory gets modified inside
            # the lib/sys call then solution will be discarded by simulation, as these
            # addresses/registers are marked as immutable, so any violation will
            # result in discarding current solution.
            #
            # UPDATE 2: It is fixed :) (check immutable registers / simulation modes)
            # 
            # However, a check here, can be used as an optimization, as we can discard
            # solutions earlier.
            # ---------------------------------------------------------------------------
            if len(clob) > 0:
                dbg_prnt(DBG_LVL_4, "Block 0x%x (%d/%d) is clobbering for statement(s): %s" %
                                     (node.addr,  counter, nnodes, # pretty_list(clob, ', ', dec)))                
                                                         ', '.join(sorted(map(str, clob)))) )
                
                self.__cfg.graph.node[node]['clob'] = clob
                
                for c in clob:          
                    clobbering.setdefault(c, []).append(node.addr)


            counter += 1


        dbg_prnt(DBG_LVL_1, "Done.")

        # print clobbering
        # print self.rsvp
        # exit()

        return clobbering



    # ---------------------------------------------------------------------------------------------
    # __get_stmt_regs(): This function gets all registers that are being used in a statement.
    #
    # :Arg stmt: The statement to get registers from.
    # :Ret: A list of all registers (int) that are being used by the statemet
    
    def __get_stmt_regs( self, stmt ):
        if   stmt['type'] == 'regset': return [stmt['reg']]
        elif stmt['type'] == 'regmod': return [stmt['reg']]
        elif stmt['type'] == 'memrd' : return [stmt['reg'], stmt['mem']]
        elif stmt['type'] == 'memwr' : return [stmt['mem'], stmt['val']]
        elif stmt['type'] == 'call'  : return [] # stmt['args']
        elif stmt['type'] == 'cond'  : return [stmt['reg']]
        else:
            return []



    # ---------------------------------------------------------------------------------------------
    # __is_clobbering(): Check whether SPL statement s2 is clobbering for SPL statement s1.
    #
    # :Arg s1: The first SPL statement
    # :Arg s2: The second SPL statement
    # :Ret: If statement s2 is clobbering with statement s1 function returns True. Otherwise it
    #       returns False.
    #       
    def __is_clobbering( self, s1, s2 ):   
        # TODO: That's not totally correct for complex SPL payloads, but it works for now
        #
        #        if  (s1['type'] == 'regset' or s1['type'] == 'regmod') and \
        #            (s2['type'] == 'regset' or s2['type'] == 'regmod'):
        #                if s1['reg'] == s2['reg']:
        #                    return True
        #
        # TODO: Add statements for memrd/memwr!!! IMPORTANT!!!

        s1_regs = set(self.__get_stmt_regs(s1))
        s2_regs = set(self.__get_stmt_regs(s2))


        if (s1_regs & s2_regs): # and s2['uid'] > s1['uid']:
            return True

        return False

# -------------------------------------------------------------------------------------------------

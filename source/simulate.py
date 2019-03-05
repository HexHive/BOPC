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
# simulate.py:
#
# This module performs the concolic execution. That is it verifies a solution proposed by search
# module. For more details please refer to the paper.
#
#
# * * * ---===== TODO list =====--- * * *
#
#   [1]. Consider overlapping cases. For instance, when we write e.g., 8 bytes at address X and
#        then we write 4 bytes at address X+1, we may have issues
#
#
# -------------------------------------------------------------------------------------------------
from coreutils import *
import path

import angr
import archinfo
import struct
import signal
import copy
import time



# ------------------------------------------------------------------------------------------------
# Constant Definitions
# ------------------------------------------------------------------------------------------------

# WARNING: In case that relative addresses fail, adjust them.
# TODO: Add command line options for them.
MAX_MEM_UNIT_BYTES      = 8                         # max. memory unit size (for x64 is 8 bytes)
MAX_MEM_UNIT_BITS       = MAX_MEM_UNIT_BYTES << 3   # max. memory unit size in bits

ALLOCATOR_BASE_ADDR     = 0xd8000000                # the base address of the allocator
ALLOCATOR_GRANULARITY   = 0x1000                    # the allocation size
ALLOCATOR_CEIL_ADDR     = 0xd9000000                # the upper bound of the allocator
ALLOCATOR_NAME          = '$alloca'
                          
POOLVAR_BASE_ADDR       = 0xca000000                # the base address of the pool
POOLVAR_GRANULARITY     = 0x1000                    # (safe) offset between pools
POOLVAR_NAME            = '$pool'

SIM_MODE_INVALID        = 0xffff                    # invalid simulation mode
SIM_MODE_FUNCTIONAL     = 0x0001                    # simulation mode: Functional
SIM_MODE_DISPATCH       = 0x0000                    # simulation mode: Dispath

MAX_BOUND = 0x4000


# addresses that are not recognized as R/W but they are
_whitelist_ = [
    0x2010028,                                      # fs:0x28
    0xc0000000,                                     # __errno_location
    0xc0000070                                      # fopen() internal
]


# ALLOCATOR_BASE_ADDR     = 0x686180                # the base address of the allocator
# ALLOCATOR_CEIL_ADDR     = 0x686180+0x10000        # the upper bound of the allocator
# POOLVAR_BASE_ADDR       = 0x680040                # the base address of the pool
# MAX_BOUND = 0x400

EXTERNAL_UNINITIALIZED = -1

# -------------------------------------------------------------------------------------------------
# simulate: This class simulates the execution between a pair of accepted blocks
#
class simulate:
    ''' ======================================================================================= '''
    '''                             INTERNAL FUNCTIONS - AUXILIARY                              '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __sig_handler(): Symbolic execution may take forever to complete. To deal with it, we set
    #       an alarm. When the alarm is triggered, this singal handler is invoked and throws an
    #       exception that causes the symbolic execution to halt.
    #
    # :Arg signum: Signal number
    # :Arg frame: Current stack frame
    # :Ret: None.
    #
    def __sig_handler( self, signum, frame ):        
        if signum == signal.SIGALRM:                # we only care about SIGALRM

            # angr may ignore the exception, so let's throw many of them :P
            raise Exception("Alarm triggered after %d seconds" % SE_TRACE_TIMEOUT)
            raise Exception("Alarm triggered after %d seconds" % SE_TRACE_TIMEOUT)
            raise Exception("Alarm triggered after %d seconds" % SE_TRACE_TIMEOUT)
            raise Exception("Alarm triggered after %d seconds" % SE_TRACE_TIMEOUT)



    # ---------------------------------------------------------------------------------------------
    # __in_constraints(): This function checks whether a symbolic variable is part of the
    #       constraints.
    #
    # :Arg symv: The symbolic variable to check
    # :Arg state: Current state of the symbolic execution    
    # :Ret: If symv is in constraints, function returns True. Otherwise it returns False.
    #
    def __in_constraints( self, symv, state=None ):
        if not state:                               # if no state is given, use the current one
            state = self.__state


        # drop the "uninitialized" thing from everywhere
        symvstr = symv.shallow_repr().replace("{UNINITIALIZED}", "")

        # We may have this in the constraints: 
        #   <Bool Reverse(mem_801_64[7:0] .. Reverse(mem_801_64)[55:0]) != 0x0>
        #
        # But symvstr is:
        #   <BV64 Reverse(mem_801_64[7:0] .. Reverse(mem_801_64)[55:0])>  
        #
        # A quick fix is to drop the type:
        
        symvstr2 = symvstr[symvstr.find(' '):-1]
   
        # print 'symvstr2', symvstr2

        # this is the old style check 
        if symvstr2 in ' '.join([c.shallow_repr().replace("{UNINITIALIZED}", "") \
                                    for c in state.se.constraints]):
            return True

        
        # reinforce function with a stronger check
        for constraint in state.se.constraints:
        # print 'CONTRST', constraint

            try:
                # treat constraint as an AST and iterate over its leaves
                for leaf in constraint.recursive_leaf_asts:
                # print '\tLEAF', symv, symvstr, leaf, leaf.shallow_repr().replace("{UNINITIALIZED}", "")

                    # we can't compare them directly, so we cast them into strings first
                    # (not a very "clean" way to do that, but it works)
                    if leaf.shallow_repr().replace("{UNINITIALIZED}", "") == symvstr:
                        return True                 # symbolic variable found!

            except Exception, err:
                # fatal('__in_constraints() unexpected exception: %s' % str(err))
                pass

        return False                                # symbolic variable not found


    # ---------------------------------------------------------------------------------------------
    # __getreg(): Get the symbolic value of a register that has in the current state.
    #
    # :Arg reg: The name of the register
    # :Arg state: Current state of the symbolic execution
    # :Ret: The symbolic value for that register.
    #
    def __getreg( self, reg, state=None ):
        if not state:                               # if no state is given, use the current one
            state = self.__state

        try:
            return {    
                'rax' : state.regs.rax,
                'rbx' : state.regs.rbx,
                'rcx' : state.regs.rcx,
                'rdx' : state.regs.rdx,
                'rsi' : state.regs.rsi,
                'rdi' : state.regs.rdi,
                'rbp' : state.regs.rbp,
                'rsp' : state.regs.rsp,
                'r8'  : state.regs.r8,
                'r08' : state.regs.r8,
                'r9'  : state.regs.r9,
                'r09' : state.regs.r9,
                'r10' : state.regs.r10,
                'r11' : state.regs.r11,
                'r12' : state.regs.r12,
                'r13' : state.regs.r13,
                'r14' : state.regs.r14,
                'r15' : state.regs.r15,
            }[ reg ]
        except KeyError:
            fatal("Unknow register '%s'" % reg)



    # ---------------------------------------------------------------------------------------------
    # __mread(): This function reads from memory. The problem here is that we have to explicitly
    #       specify how to interpret memory (.uint8_t, .uint32_t, etc.), according to the number
    #       of bytes that we want to read. This results in cumbersome code, as we need a different
    #       case for every possible length, so we provide a simply interface through this function.
    #
    # :Arg state: Current state of the symbolic execution
    # :Arg addr: Address to read from
    # :Arg length: Number of bytes to read
    # :Ret: The contents of the desired memory "area".
    #
    def __mread( self, state, addr, length ):
       # dbg_prnt(DBG_LVL_3, "Reading %d bytes from 0x%x" % (length, addr))

        return state.memory.load(addr, length, endness=archinfo.Endness.LE)

        '''
        try:
            return {
                1 : state.mem[ addr ].uint8_t.resolved,
                2 : state.mem[ addr ].uint16_t.resolved,
                4 : state.mem[ addr ].uint32_t.resolved,
                8 : state.mem[ addr ].uint64_t.resolved
            }[ length ]
        except KeyError:
            dbg_prnt(DBG_LVL_3, "Reading %d bytes from 0x%x" % (length, addr))

            return state.memory.load(addr, length)  # for other sizes, just use load() 
        '''


    # ---------------------------------------------------------------------------------------------
    # __mwrite(): Similar to __mread() but this function writes to memory instead.
    #
    # :Arg state: Current state of the symbolic execution
    # :Arg addr: Address to write to
    # :Arg length: Number of bytes to write
    # :Ret: None.
    #
    def __mwrite( self, state, addr, length, value ):
        state.memory.store(addr, value, length, endness=archinfo.Endness.LE)

        '''        
        if   length == 1: state.mem[addr].uint8_t  = value
        elif length == 2: state.mem[addr].uint16_t = value
        elif length == 4: state.mem[addr].uint32_t = value
        elif length == 8: state.mem[addr].uint64_t = value
        else:
            dbg_prnt(DBG_LVL_3, "Writing %d bytes to 0x%x" % (length, addr))

            state.memory.store(addr, value, length)
        '''



    # ---------------------------------------------------------------------------------------------
    # __get_permissions(): Get 
    #
    # :Arg state: Current state of the symbolic execution
    # :Arg addr: Address to write to
    # :Arg length: Number of bytes to write
    # :Ret: None.
    #
    def __get_permissions( self, addr, length=1, state=None ):
        if not state:                               # if no state is given, use the current one
            state = self.__state

        # TODO: check permissions for addr+1, addr+2, ... addr+length-1
        #warn('POOL UPPER BOUND %x' % (POOLVAR_BASE_ADDR + self.__plsz))

        # special cases first
        if addr < 0x10000:
            return ''

        elif ALLOCATOR_BASE_ADDR <= addr and addr <= ALLOCATOR_CEIL_ADDR:
            return 'RW'   

        # TOOD:!!! 0x10000
        elif POOLVAR_BASE_ADDR <= addr and addr <= POOLVAR_BASE_ADDR + self.__plsz + 0x1000:
            return 'RW'

        # special case when a stack address is in the next page
        # TODO: make it relative from STACK_BASE_ADDR
        elif addr & 0x07ffffffffff0000 == 0x07ffffffffff0000:
            return 'RW'


        try:                    
            for _, sec in  self.__proj.loader.main_object.sections_map.iteritems():
                if sec.contains_addr(addr):                    
                    return ('R' if sec.is_readable   else '') + \
                           ('W' if sec.is_writable   else '') + \
                           ('X' if sec.is_executable else '')

            permissions = state.se.eval(state.memory.permissions(addr))

            return ('R' if permissions & 4 else '') + \
                   ('W' if permissions & 2 else '') + \
                   ('X' if permissions & 1 else '')

        except angr.errors.SimMemoryError:       
            return ''                               # no permissions at all
 


    # ---------------------------------------------------------------------------------------------
    # __symv_in(): Check whether a symbolic expression contains a given symbolic variable.
    #
    # :Arg symexpr: The symblolic expression
    # :Arg symv: The symbolic variable to look for
    # :Ret: If symexpr contains symv, function returns True. Otherwise it returns False.
    #
    def __symv_in( self, symexpr, symv ):
        if symexpr == None or symv == None:         # check special cases
            return False
            
#        if symexpr.shallow_repr() == symv.shallow_repr(): 
#            return True
        
        try:
            # treat symexpr as an AST and iterate over its leaves
            for leaf in symexpr.recursive_leaf_asts:
                
                # we can't compare them directly, so we cast them into strings first
                # (not a very "clean" way to do that, but it works)
                if leaf.shallow_repr() == symv.shallow_repr():  
                    return True                     # variable found!

            return False                            # variable not found

        except Exception, err:
            # This --> BOPC.py -ddd -b eval/nginx/nginx1 -s payloads/ifelse.spl -a load -f gdb -e -1
            # fatal('__symv_in() unexpected exception: %s' % str(err))

            raise Exception('__symv_in() unexpected exception: %s' % str(err))



    # ---------------------------------------------------------------------------------------------
    # __alloc_un(): "Allocate" memory for uninitialized symbolic variables (if needed).
    #
    # :Arg state: Current symbolic state of the execution
    # :Arg symv: The symbolic variable 
    # :Ret: If symv is uninitialized, function returns True; otherwise it returns False.
    #
    def __alloc_un( self, state, symv ):
        if symv == None:                            # make sure that variable is valid  
            return False

        # This code works fine for single variables but not for expressions:
        #
        # # nothing to do when variable is not uninitialized (i.e. initialized)
        # if "{UNINITIALIZED}" not in symv.shallow_repr():
        #     return False
        #
        # # After calling __alloc_un(), a variable will still have the UNINITIALIZED keyword
        # # even though, it has a single solution. Avoid initializing a variable twice.
        #
        # con = state.se.eval_upto(symv, 2)           # try to get 2 solutions
        # addr = state.se.eval(con[0])
        #
        # if len(con) > 1 or not (addr >= ALLOCATOR_BASE_ADDR and addr <= ALLOCATOR_CEIL_ADDR):
        #     # initialize variable
        addr = state.se.eval(symv)                  # try to concretize it


        #  print '***** ALLOC UN:', hex(addr), symv

        # we say < 0x1000, to catch cases with small offsets:
        # e.g., *<BV64 Reverse(stack_16660_262144[258239:258176]) + 0x68>
        # which gets concretized to 0x68 
        if addr < 0x1000 or addr > 0xfffffffffffff000:
        # if addr == 0: # < ALLOCATOR_BASE_ADDR or addr > ALLOCATOR_CEIL_ADDR

            alloca = ALLOCATOR_BASE_ADDR + self.__alloc_size

            # add the right contraint, to make variable, point where you want
            # address now becomes concrete (it has exactly 1 solution)

            # in case that addr > 0, make sure that symv is concretized from 0
            # (otherwise, we'll start before self.__alloc_size)
            x = state.se.BVS('x', 64)
            # print 'x is ', x, alloca + addr, symv

            # this indirection ensure that symv concretized to 64 bits
            state.add_constraints(x == alloca + addr)
            state.add_constraints(symv == x)

            # 
            # print '-->', symv, 'goes to ', hex(alloca + addr)

            self.__relative[alloca] = '%s + 0x%03x' % (ALLOCATOR_NAME, self.__alloc_size)

            
            self.__sym[ alloca ] = symv

            # shift allocator
            self.__alloc_size += ALLOCATOR_GRANULARITY

            
            return True                             # we had an allocation            
        
        return False                                # no allocation



    # ---------------------------------------------------------------------------------------------
    # __init_mem(): This function initializes (if needed) a memory cell. When we start execution
    #       from an arbitrary point, it's likely that the memory cell will be empty/uninitialized.
    #       Therefore, we need to assign a symbolic variable to it first.
    #
    #       A special case here is global variables from .bss and .data, which have a default value
    #       of 0. Therefore, these variables are actually uninitialized, but instead of containing
    #       a symbolic variable, they contain the default value (a bitvector of value 0). However,
    #       this can cause problems to the symbolic execution, as variables are already concrete.
    #
    # :Arg state: Current symbolic state of the execution
    # :Arg addr: Address of the variable
    # :Arg length: Length of the variable
    # :Ret: If memory was initialized, function returns True. Otherwise it returns False.
    #
    def __init_mem( self, state, addr, length=MAX_MEM_UNIT_BYTES ):
        if addr in self.__mem:                      # memory cell is already initialized
            return False
        
        self.__mem[addr] = length                   # simply mark used addresses

        # get ELF sections that give default values to their uninitialized variables
        bss  = self.__proj.loader.main_object.sections_map[".bss"]
        data = self.__proj.loader.main_object.sections_map[".data"]

        # print 'INIT MEMORY', hex(addr), self.__mread(state, addr, length)


        # if the memory cell is empty (None) or if the cell is initialized with a
        # default value, then we should give it a symbolic variable. You can also use: 
        #       state.inspect.mem_read_expr == None:
        #
        if  self.__mread(state, addr, length) == None             or \
            bss.min_addr        <= addr and addr <= bss.max_addr  or \
            data.min_addr       <= addr and addr <= data.max_addr or \
            ALLOCATOR_BASE_ADDR <= addr and addr <= ALLOCATOR_CEIL_ADDR:
            # bss.min_addr  <= addr and addr + length <= bss.max_addr  or \
            # data.min_addr <= addr and addr + length <= data.max_addr:

                # Alternative: state.memory.make_symbolic('mem', addr, length << 3) (big endian)
                symv = state.se.BVS("mem_%x" % addr, length << 3)


                # write symbolic variable to both states (current and original)
                self.__mwrite(state,         addr, length, symv)
                self.__mwrite(self.__origst, addr, length, symv)

                # get symbolic variable
                self.__sym[ addr ] = self.__mread(state, addr, length)

                return True                         # memory initialized


        # if it's uninitialized, simply add it variable to the __sym table
        # (but memory is not initialized at all)
        if "{UNINITIALIZED}" in self.__mread(state, addr, length).shallow_repr():
            self.__sym[ addr ] = self.__mread(state, addr, length)            



        return False                                # memory not initialized



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                          INTERNAL FUNCTIONS - EXECUTION HOOKS                           '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __dbg_read_hook(): This callback function is invoked when a memory "area" is being read.
    #
    # :Arg state: Current state of the symbolic execution
    # :Ret: None.
    #
    def __dbg_read_hook( self, state ):
        if self.__disable_hooks:                    # if hooks are disabled, abort
            return

        # if you read/write memory inside the hook, this operation will trigger __dbg_read_hook()
        # again, thus resulting in a endless recursion. We need "exclusive access" here, so we
        # disable hooks inside function's body. This is pretty much like a mutex.
        self.__disable_hooks = True

        # TODO: the idea of simulation modes is not perfect
        #   a block can modify the data unintentionally
        #
        # update simulation mode

#        if self.__blk_start <= state.addr and state.addr < self.__blk_end:
#            self.__sim_mode = SIM_MODE_FUNCTIONAL
#        else:
#            self.__sim_mode = SIM_MODE_DISPATCH

        print 'state.inspect.mem_read_address', state.inspect.mem_read_address


        # if the address is an uninitialized symbolic variable, it can point to any location,
        # thus, when it's being evaluated it gets a value of 0. To fix this, we "allocate" some
        # memory and we make the address point to it.
        self.__alloc_un(state, state.inspect.mem_read_address)

        # now you can safely, "evaluate" address and concretize it
        addr = state.se.eval(state.inspect.mem_read_address)

        # concretize size (newer versions of angr never set state.inspect.mem_read_length to None)
        if state.inspect.mem_read_length == None:
            size = MAX_MEM_UNIT_BYTES               # if size is None, set it to default
        else:
            size = state.se.eval(state.inspect.mem_read_length)


        self.__init_mem(state, addr, size)          # initialize memory (if needed)
        

        if state.inspect.instruction:
            insn_addr = state.inspect.instruction
        else:
            insn_addr = state.addr

        dbg_prnt(DBG_LVL_3, '\t0x%08x: mem[0x%x] = %s (%x bytes)' % 
                    (insn_addr, addr, self.__mread(state, addr, size), size), pre='[R] ')
        

        # make sure that the address that you read from has +R permissions
        # TODO: fs:0x28 (canary hits an error here) 0x2010028
        if 'R' not in self.__get_permissions(addr, state) and addr not in _whitelist_:
            raise Exception("Attempted to read from an non-readable address '0x%x'" % addr)


        self.__disable_hooks = False                # release "lock" (i.e., enable hooks again)



    # ---------------------------------------------------------------------------------------------
    # __dbg_write_hook(): This callback function is invoked when a memory "area" is being written.
    #
    # :Arg state: Current state of the symbolic execution
    # :Ret: None.
    #
    def __dbg_write_hook( self, state ):
        if self.__disable_hooks:                    # if hooks are disabled, abort
            return
        
        # as in __dbg_read_hook(), we need mutual exclusion here as well
        self.__disable_hooks = True


        # update simulation mode
#        if self.__blk_start <= state.addr and state.addr < self.__blk_end:
#            self.__sim_mode = SIM_MODE_FUNCTIONAL
#        else:
#            self.__sim_mode = SIM_MODE_DISPATCH

        if state.inspect.instruction:
            insn_addr = state.inspect.instruction
        else:
            insn_addr = state.addr


        # as in __dbg_read_hook(), fix uninitialized addresses first
        self.__alloc_un(state, state.inspect.mem_write_address)

        # now you can safely, "evaluate" address and concretize it
        addr = state.se.eval(state.inspect.mem_write_address)

        # concretize size (newer versions of angr never set state.inspect.mem_read_length to None)
        if state.inspect.mem_write_length == None:
            size = MAX_MEM_UNIT_BYTES               # if size is None, set it to default
        else:
            size = state.se.eval(state.inspect.mem_write_length)
        

        dbg_prnt(DBG_LVL_3, '\t0x%08x: mem[0x%x] = %s (%x bytes)' % 
                    (insn_addr, addr, state.inspect.mem_write_expr, size), pre='[W] ')
        

#        print 'BEFORE', self.__mread(state, addr, size),  state.inspect.mem_write_expr
#        ISPO = state.inspect.mem_write_expr
        

        if 'W' not in self.__get_permissions(addr, state) and addr not in _whitelist_:
            raise Exception("Attempted to write to an non-writable address '0x%x'" % addr)
            

        # if we are trying to write to an immutable cell, currect execution path must be discarded
        if self.__sim_mode == SIM_MODE_DISPATCH: 
            if addr in self.__imm:

                oldval = state.se.eval(state.memory.load(addr, size))
                newval = state.se.eval(state.inspect.mem_write_expr)

                
                # if the new value is the same with the old one, we're good :)                
                if oldval != newval:            # if value really changes
                    self.__disable_hooks = False
                    
                    raise Exception("Attempted to write to immutable address '0x%x'" % addr)



        if state.inspect.mem_write_expr in self.__ext:
            
            self.__ext[ state.inspect.mem_write_expr ] = addr

        
        # if it's not the 1st time that you see this address
        if not self.__init_mem(state, addr, size):

            # if address is not concretized already and it's in the symbolic variable set
            if not isinstance(self.__mem[addr], tuple) and addr in self.__sym:
                symv = self.__sym[ addr ]           # get symbolic variable

                # check whether symbolic variable persists after write
                if not self.__symv_in(state.inspect.mem_write_expr, symv):
                    # Variable gets vanished. We should concretize it now, because, after
                    # that point, memory cell is dead; that is it's not part of the constraints
                    # anymore, as its original value got lost.
                    #
                    # To better illustrate the reason, consider the following code:
                    #       a = input();
                    #       if (a > 10 && a < 20) {
                    #           a = 0;
                    #           /* target block */
                    #       }
                    #
                    # Here, if we concretize 'a' at the end of the symbolic execution if will
                    # get a value of 0, which of course is not the desired one. The coorect
                    # approach, is to concretize, right before it gets overwritten.


                    # if variable is part of the constraints, add it to the set
                    if self.__in_constraints(symv, state):
                        val = state.se.eval(symv) # self.__mread(state, addr, size))
                        self.__mem[addr] = (val, size)

                        emph('Address/Value pair found: *0x%x = 0x%x (%d bytes)' % 
                                (addr, val, size), DBG_LVL_2)

                    # if the contents of that cell get lost, we cannot use AWP to write to it
                    # anymore
                    #
                    # TODO: Not sure if this correct
                    # UPDATE: Immutables should be fine when we write them with the exact same valut
#                    for i in range(8):
#                        self.__imm.add(addr + i)

        
#        print 'AFTER', self.__mread(state, addr, size),  state.inspect.mem_write_expr
#        self.FOO[ self.__mread(state, addr, size) ]  = ISPO

        # All external inputs (sockets, file descriptors, etc.) should be first written somewhere
        # in memory / registers eventually, so we can concretize them afterwards   

        self.__disable_hooks = False                # release "lock" (i.e., enable hooks again)



    # ---------------------------------------------------------------------------------------------
    # __dbg_symv_hook(): This callback function is invoked when a new symbolic variable is being
    #       created.
    #
    # :Arg state: Current state of the symbolic execution
    # :Ret: None.
    #
    def __dbg_symv_hook( self, state ):
        name = state.inspect.symbolic_name          # get name of the variable

        # we're only interested in symbolic variables that come from external inputs (sockets, 
        # file descriptors, etc.), as register and memory symbolic variables are already been
        # handled. 
        if not name.startswith('mem_') and not name.startswith('reg_') \
            and not name.startswith('x_') and not name.startswith('cond_'):
            
            # x  and cond are our variable so they're discarded too
            dbg_prnt(DBG_LVL_3, " New symbolic variable '%s'" % name, pre='[S]')

            self.__ext[ state.inspect.symbolic_expr ] = EXTERNAL_UNINITIALIZED




    # ---------------------------------------------------------------------------------------------
    # __dbg_reg_wr_hook(): This callback function is invoked when a register is being modified.
    #
    # :Arg state: Current state of the symbolic execution
    # :Ret: None.
    #
    def __dbg_reg_wr_hook( self, state ):    
        if self.__disable_hooks:                    # if hooks are disabled, abort
            return

        # as in __dbg_read_hook(), we need mutual exclusion here as well
        self.__disable_hooks = True

  
        # update simulation mode
#        if self.__blk_start <= state.addr and state.addr < self.__blk_end:
#            self.__sim_mode = SIM_MODE_FUNCTIONAL
#        else:
#            self.__sim_mode = SIM_MODE_DISPATCH
        if state.inspect.instruction:
            insn_addr = state.inspect.instruction
        else:
            insn_addr = state.addr
        
        # get register name (no exceptions here)
        regnam = state.arch.register_names[ state.inspect.reg_write_offset ]
        if regnam in HARDWARE_REGISTERS:            # we don't care about all registers (rip, etc.)

            dbg_prnt(DBG_LVL_3, '\t0x%08x: %s = %s' % 
                        (insn_addr, regnam, state.inspect.reg_write_expr), pre='[r] ')


            # if simulation is in dispatch mode, check whether the modified register is immutable
            if self.__sim_mode == SIM_MODE_DISPATCH:

                # print 'IMM REGS', self.__imm_regs
                if regnam in self.__imm_regs:

                    # if the new value is the same with the old one, we're good :)

                    # we can concretize them as SPL registers always have integer values
                    oldval = state.se.eval(self.__getreg(regnam))
                    newval = state.se.eval(state.inspect.reg_write_expr)

                    # if value really changes (and it has changed in the past)
                    if oldval != newval and \
                        self.__getreg(regnam).shallow_repr() != self.__inireg[regnam].shallow_repr():
                        self.__disable_hooks = False

                        raise Exception("Attempted to write to immutable register '%s'" % regnam)

                    else:
                        print "immutable register '%s' overwritten with same value 0x%x" % (regnam, newval)


            # check whether symbolic variable persists after write
            if not self.__symv_in(state.inspect.reg_write_expr, self.__inireg[regnam]):
                if regnam not in self.__reg:        # if register is already concretized, skip it
                    # concretize register (after this point, its value will get lost)                
                    val = state.se.eval( self.__getreg(regnam, state) )


                    # if register is in the constraints, it should be part of the solution.
                    # But in any case we need the register to be in __reg, as its value is now
                    # lost, so we don't want any further register writes to be part of the
                    # solution.

                    if self.__in_constraints(self.__inireg[regnam], state):
                        self.__reg[ regnam ] = val

                        emph('Register found: %s = %x' % (regnam, val), DBG_LVL_2)
                    else:
                        # make it a tuple to distinguish the 2 cases
                        self.__reg[ regnam ] = (val,)


        self.__disable_hooks = False                # release "lock" (i.e., enable hooks again)



    # ---------------------------------------------------------------------------------------------
    # __dbg_call_hook(): This callback function is invoked when a function is invoked.
    #
    # :Arg state: Current state of the symbolic execution
    # :Ret: None.
    #
    def __dbg_call_hook( self, state ):
        if self.__disable_hooks:                    # if hooks are disabled, abort
            return

        # as in __dbg_read_hook(), we need mutual exclusion here as well
        self.__disable_hooks = True

        address = state.se.eval(state.inspect.function_address)
        name    = self.__proj.kb.functions[address].name

        # This function is called to solve a difficult problem: Crashes. 
        # TODO: elaborate.

        dbg_prnt(DBG_LVL_3, "\tCall to '%s' found." % name, pre='[C] ')

        # ---------------------------------------------------------------------
        # FILE *fopen(const char *path, const char *mode)
        # ---------------------------------------------------------------------
        if name == 'fopen':
            # print 'RDI', state.regs.rdi
            # print 'RSI', state.regs.rsi
            
            # if rdi is an expression then we may need to 

            # we work similarly with __mem_RSVPs, but our task here is simpler
            con_addr = state.se.eval(state.regs.rdi)
            # print 'ADDR', hex(con_addr)

            if 'W' not in self.__get_permissions(con_addr, state):
                self.__alloc_un(state, state.regs.rdi)
                #raise Exception("Attempted to write to an non-writable address '0x%x'" % addr)
        
            con_addr = state.se.eval(state.regs.rdi)
            # print 'ADDR', hex(con_addr)

            name = SYMBOLIC_FILENAME
          

            # if this address has already been written in the past, any writes will
            # be overwritten, so discard current path
            if con_addr in self.__mem or con_addr in self.__imm or (con_addr + 7) in self.__imm:
                raise Exception("Address 0x%x has already been written or it's immutable. "
                                "Discard current path." % con_addr)

            # write value byte-by-byte.
            for i in range(len(name)):
                self.__mwrite(state, con_addr + i, 1, name[i])
                self.__imm.add(con_addr + i)

            
            self.__inivar_rel[ con_addr ] = name
            self.__mem[ con_addr ] = 0
            dbg_prnt(DBG_LVL_2, "Writing call *0x%x = '%s'" % (con_addr, name))



        # ---------------------------------------------------------------------
        # int _IO_getc(_IO_FILE * __fp)
        #
        # TODO: Delete this code, or check for uninitialized FILE*
        # ---------------------------------------------------------------------
        elif name == '_IO_getc': 
            # print 'RDI', state.regs.rdi
            error('Oups!')   
            pass

        # ---------------------------------------------------------------------
        # TODO: Do the same for others open(), strcmp() (in wuftpd) and so on
        # ---------------------------------------------------------------------



        # ---------------------------------------------------------------------

        self.__disable_hooks = False                # release "lock" (i.e., enable hooks again)



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                         INTERNAL FUNCTIONS - MEMORY MANAGEMENT                          '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __get_var_values(): Get the values of an SPL variable (there can be >1)
    #
    # :Arg variable: The SPL variable
    # :Ret: The values of that variable.
    #
    def __get_var_values( self, variable ):
        # look for the declaration of "variable" (SPL compiler ensures it's uniqueness)
        for stmt in self.__IR:
            if stmt['type'] == 'varset' and stmt['name'] == variable:
                return stmt['val']

        # this should never be executed
        fatal("Searching for non-existing variable '%s'" % variable)



    # ---------------------------------------------------------------------------------------------
    # __pool_RSVP(): Reserve some address space in the pool, to store a variable.
    #
    # :Arg variable: The SPL variable
    # :Ret: The values of that variable.
    #
    def __pool_RSVP( self, variable ):        
        addr = POOLVAR_BASE_ADDR + self.__plsz      # make address pointing to the end of the pool
        

        self.__relative[ addr ] = '%s + 0x%03x' % (POOLVAR_NAME, self.__plsz)


        # reserve some space in the pool to hold variable's values (shift down self.__plsz)
        # (it's important as recursive calls in __init_variable_rcsv() can overwrite this space)
        #
        # NOTE: In current implementation, if there are >1 values, each of them has size 8.
        #       However we keep the code more general (i.e. independent of SPL compiler) so
        #       we don't use this observation.
        self.__plsz += sum(map(lambda v : len(v) if isinstance(v, str) else 8, 
                                self.__get_var_values(variable)))

        return addr                                 # return that address



    # ---------------------------------------------------------------------------------------------
    # __init_variable_rcsv(): Initialize a single SPL variable. This function writes the value(s)
    #       for that variable in memory. There are 2 types of variables. *Free* and *Register*.
    #       Free variables have no restrictions and therefore can be stored at any location (due
    #       to the AWP). Thus we reserve a "memory pool" somewhere in memory and we place all free
    #       variables there. Register variables are being passed to registers and therefore their
    #       address must be a valid (+RW) address that is being loaded to a register in a candidate
    #       block (they are usually on stack / heap).
    #
    #       SPL allows variables to get the address of another variable. That is, initializing a
    #       variable may require to initialize another variable first, and so on. Hence this
    #       function is recursive. For example consider the following variables (expressed in IR):
    #       
    #       {'type':'varset', 'uid':2, 'val':['aaa'],                                 'name':'aaa'}
    #       {'type':'varset', 'uid':4, 'val':['\x01\x00...\x00', ('aaa',)],           'name':'bbb'}
    #       {'type':'varset', 'uid':6, 'val':['\x02\x00...\x00', ('aaa',), ('bbb',)], 'name':'ccc'}
    #       {'type':'varset', 'uid':8, 'val':[('ccc',), '\x03\x00...\x00'],           'name':'ddd'}
    #
    #       Here initializing 'ddd', requires to initialize 'ccc' first and to initialize 'ccc' we
    #       have to initialize 'aaa' and 'bbb', but to initialize 'bbb' we have to also initialize
    #       'aaa'. The SPL compiler ensures that there not cycles.
    #
    # :Arg variable: The variable to initialize
    # :Ret: The address that the contents of this are stored.
    #
    def __init_variable_rcsv( self, variable, depth=0 ):
        dbg_prnt(DBG_LVL_3, "Initializing variable '%s' (depth: %d)" % (variable, depth))
        
        # ---------------------------------------------------------------------
        # Find the address for that variable
        # ---------------------------------------------------------------------       
        if variable in self.__vartab:               # register/used variable?
            addr = self.__vartab[ variable ]        # variable should be placed at a given location
            
            if addr in self.__inivar:               # if variable has already been initialized
                dbg_prnt(DBG_LVL_3, "'%s' is already initialized." % variable)
                return addr                         # just return it


            # addr can be a number, like 0x7ffffffffff01a0 or a string (dereference)
            # like "*<BV64 0x7ffffffffff0020>", or "*<BV64 rsi_713_64 + 0x18>".
            #
            # If the address gets dereferenced (*X), we store the values into the pool
            # and write pool's address into X (indirect) at runtime.
            if isinstance(addr, str):               # is addr a dereference?                
                addr = self.__pool_RSVP(variable)   # make address pointing to the pool                
                self.__vartab[ variable ] = addr    # and add it to the vartab

        else:
            # Variable is not in the vartab => Free. That is, variable can be stored
            # at any memory location, so we place it on the pool
            addr = self.__pool_RSVP(variable)
            self.__vartab[ variable ] = addr


        # ---------------------------------------------------------------------
        # Store the values to that address
        # ---------------------------------------------------------------------       
        orig_addr = addr                            # get a backup as address is being modified
        values    = ''                              # concatenated values
        relvals   = []                              # values in the relative form

        for val in self.__get_var_values(variable): # for each value

            if isinstance(val, tuple):
                # Value is a reference to another variable, Recursively initialize the
                # variable or get its address if it's already initialized. Recursion 
                # always halts, as SPL compiler ensures that variables aren't used before
                # they initialized so the following cases can't happen:
                #       int x = {&x};
                #       int a = {&b}; int b = 10; 

                # find the address for that variable and pack it
                address = self.__init_variable_rcsv( val[0], depth+1 )
                val     = struct.pack("<Q", address)

                relvals.append( address )           # relative value is an address

            else: 
                relvals.append( val )               # relative value is a string


            # at this point, value is a string (SPL compiler 'packs' integers)
           
            values += val

    
        # write value byte-by-byte. Memory address must be immutable;
        # any writes to it are not allowed
        for i in range(len(values)):
            self.__state.memory.store(addr + i, values[i])

            # check if it's already immutable
            if addr + i in self.__imm:
                raise Exception('Attempted to write an RSVP to an immutable address')


            self.__imm.add(addr + i)

        self.__inivar[ addr ] = values          # mark address as initialized        
        self.__inivar_rel[ addr ] = relvals     # values in the relative-form 

        addr += len(val)                        # and then shift index to the next value
        print 'INIVAR_REL:', hex(addr), relvals      

        dbg_prnt(DBG_LVL_3, "Done. '%s' has been initialized at 0x%x" % (variable, orig_addr))

        return orig_addr                            # return variable's original address
        


    # ---------------------------------------------------------------------------------------------
    # __init_vars(): Initialize the variables of the SPL payload. This function is essentially a
    #       wrapper of __init_variable_rcsv().
    #
    # :Arg varmap: The current variable mapping
    # :Ret: None.
    #
    def __init_vars( self, varmap ):
        dbg_prnt(DBG_LVL_2, 'Initializing SPL variables...')

        self.__vartab     = dict(varmap[:])         # create a dictionary out of varmap
        self.__plsz       = 0                       # our pool size
        self.__inivar     = { }                     # initialized memory locations 
        self.__inivar_rel = { }                     # values in the relative-form


        for var, addr in varmap:                    # for each SPL variable
            self.__init_variable_rcsv(var)          # recusively store it in memory 
                                                    # and update self.__vartab

        # ---------------------------------------------------------------------
        # Memory has been initialized. Print out variables (debugging only)
        # ---------------------------------------------------------------------
        dbg_prnt(DBG_LVL_2, 'Done. Pool Size: %s. Variable(s) memory layout:' % bold(self.__plsz))

        for addr, val in sorted(self.__inivar.iteritems()):
            dbg_prnt(DBG_LVL_2, '  %16x <- %s' % (addr, ' '.join(['%02x' % ord(v) for v in val])))
            
        # self.__vartab shows the address that each variable has been stored
        dbg_arb(DBG_LVL_3, 'Variable Table:', 
                                ['%s:0x%x' % (n,v) for n, v in self.__vartab.iteritems()])
        
        del self.__inivar                         # we don't need this guy anymore



    # ---------------------------------------------------------------------------------------------
    # __mem_RSVPs(): Initialize reserved memory locations that are being used as dereferences.
    #       This function is the continuation of __init_vars(). The problem here is that the
    #       address of an RSVP may change during the symbolic execution, or may be unknown until
    #       we reach the actual statement. For example:
    #
    #           UID:8       addr = [rsi + 10]
    #
    #       Here, rsi may be set at UID:6, so we don't know the address of [rsi + 10] and hence
    #       we cannot write a dereference, before we reach statement with UID:8. 
    #
    #       This function is invoked right before the execution of an accepted block and writes
    #       any dereferences "on the fly". We have to be careful though, as these addresses may
    #       be already written (we can't use AWP to set them at the beginning of the execution), 
    #       or marked as immutable. In both cases, reservation fails.
    #
    #
    # :Arg state: Current state of the symbolic execution    
    # :Arg cur_blk: Current basic block address
    # :Arg cur_uid: Current statement UID
    # :Ret: If reservation is successful, function returns True. If for some reason reservation 
    #       fails, False is returned.
    #
    def __mem_RSVPs( self, state, cur_blk, cur_uid ):
        dbg_prnt(DBG_LVL_2, "Applying memory RSVPs ...")

        # this is a static-style local variable
        if '_simulate__reserved_syms' not in self.__dict__:
            self.__reserved_syms = set()            # previous registers that were used in RSVPs


        # There's a problem when we concretize a symbolic variable that is already in 
        # __reserved_syms. For instance, if we set <BV64 rsi_713_64 + 0x30> at the 1st 
        # free slot of the pool, then <BV64 rsi_713_64 + 0x10> will point to a used area
        # in the pool. This memory has already been marked as immutable, so the reservation
        # will fail. To fix this, we "shift" the pool index to avoid these overlaps. Not a
        # perfect solution, but it works :)
        #
        # Although we can use a different memory area for that, we keep everything on the same
        # pool for simplicity.
        self.__plsz += POOLVAR_GRANULARITY

    
        self.__disable_hooks = True                 # disable hooks as we'll write to memory


        for blk, rsvp in self.__rsvp.iteritems():   # for each basic block reservation

            # check if it's the right time to do the reservation.
            #
            # (IMPORTANT) We can have >1 statements that use the same basic block, but the
            # current induced subgraph (Hk) might use only one statement from this block. 
            # So, we cannot make the reservations based just on block addresses. We have
            # to base our decisions on the UIDs as well, but then we can make one reservation
            # at a time. This is NOT an issue as long as Hk has multiple nodes that correspond
            # to the same basic block, so we'll have transitions from a block to itself.
            if blk != cur_blk:
                continue

            for (uid, addr, sym, val) in rsvp:      # for each statement reservation in this block         
                if uid != cur_uid:                  # check UID as well
                   continue


                print "RSVP ADDR',", addr, val

                
                reg = [r for v, r in self.__regmap if v == '__r%d' % self.__IR[uid]['reg']][0]



                self.unchecked_regsets.append( (reg, self.__IR[uid]['val']) )


                # If we have a double pointer, load variable's address from vartab (__init_vars() 
                # ensures that __vartab[val[0]] exists and is an valid integer address)                                
                if addr[0] == '*':                  
                    addr = addr[1:]                 # drop asterisk
                    val  = self.__vartab[ val[0] ]



                for leaf in STR2BV[addr].recursive_leaf_asts:
                    if leaf.shallow_repr() in SYM2ADDR:

                        print 'ADD contraint', leaf, hex(SYM2ADDR[leaf.shallow_repr() ][0])#, self.__mwrite(state, SYM2ADDR[leaf], 8, leaf)
                        #self.__state.add_constraints(leaf == self.__mwrite(state, SYM2ADDR[leaf], 8, leaf))
                        self.FOO.append(leaf)
                        self.__sym[ SYM2ADDR[leaf.shallow_repr() ][0] ] = leaf


                # check if address has dependencies on symbolic registers 
                # (e.g. <BV64 rsi_713_64 + 0x10>).
                #
                # Otherwise, address is constant so we directly write to that address.
                for reg, symreg in sym.iteritems(): # {'rsi': <BV64 rsi_713_64>} pairs

                    # if a register has already been used in a reservation, we don't add more
                    # constraints as we'll probably make it u n-satisfiable. For example, if
                    # we have the RSVPs <BV64 rsi_713_64 + 0x10> and <BV64 rsi_713_64 + 0x30>,
                    # we constrain rsi_713_64 only once.


                    if symreg not in self.__reserved_syms:
                        self.__reserved_syms.add( symreg )

                       # print 'add_constraints', symreg, STR2BV[addr]

                        # UPDATE: We may not need to add constraints. It's possible to already
                        #   have some constraints with addresses from the allocator, so when
                        #   we add pool addresses, we make them unsatisfiable. That is, we 
                        #   can implicitly have an address for a reservation outside of the pool.
                        #   For example:
                        #
                        #       <Bool mem_795_64 != 0x0>
                        #       <Bool (mem_795_64 + 0x10) == 0xd800100f>
                        #       <Bool mem_795_64 == r13_292906_64>
                        #
                        # If we now try to add the following constraint:
                        #       <Bool (r13_292906_64 + 0x38) == 0xca002028>
                        # 
                        # we'll make constraints unsatisfiable. Thus we don't have to add the
                        # last constraint, when has already a single solution



                        # The symbolic variable in symreg is different from this in state.regs.*.
                        # To deal with it, we add 2 constraints: 1st, we require that these two
                        # symbolic variables (symreg and state.regs.*) are equal and 2nd we 
                        # require that the symbolic address will point to an address on the pool.
                        state.add_constraints(self.__getreg(reg, state) == symreg)

                        state_copy = state.copy()                        

                        # this can be unsatisfiable. Try it on a copy of the state
                        x = state.se.BVS('x', 64)
                        
                        state_copy.add_constraints(x == POOLVAR_BASE_ADDR + self.__plsz)
                        state_copy.add_constraints(STR2BV[addr] == x)


                        print 'state.satisfiable():', state_copy.satisfiable(), state_copy.se.satisfiable()

                        if not state_copy.satisfiable():
                            dbg_prnt(DBG_LVL_2, "Reservation constraint was un-satisfiable. Rolling back...")

                            del state_copy
                        else:
                            # constraint ok. add it to the real state
                            x = state.se.BVS('x', 64)
                        
                            state.add_constraints(x == POOLVAR_BASE_ADDR + self.__plsz)
                            state.add_constraints(STR2BV[addr] == x)

                            # TODO: comment!
                            self.__relative[POOLVAR_BASE_ADDR + self.__plsz] = \
                                                                '$pool + 0x%03x' % self.__plsz

                            self.__plsz += 8            # update pool

                            del state_copy


                # print 'FINAL CONSTRAINTS', state.se.constraints

                try:
                    # 'addr' is string with a symbolic expression. Convert it back to bitvector
                    # and concretize it
                    con_addr = state.se.eval(STR2BV[addr])

                    print 'con_addr', hex(con_addr)

                    # The stack address in the basic block is different from the one in the
                    # current path. So readjust it (TODO: Do it in a less sloppy way)
                    # TODO: !!!!!!!
                    if abs(con_addr - RSP_BASE_ADDR) < 0x1000:
                        con_addr = (con_addr - RSP_BASE_ADDR) + state.se.eval(state.regs.rsp)
                        print 'CON', state.regs.rsp, hex(state.se.eval(state.regs.rsp))
                        print 'CONCON', hex(con_addr)
                        #  exit()



                    # -------------------------------------------------------------------------
                    # RSVPs like this: '<BV64 Reverse(stack_9618_262144[258175:258112]) + 0x18>'
                    #       get concretized to 0x18, so make sure that before you concretize
                    #       it's a +W memory
                    #
                    # Update: We miss solutions here. Instead of discarding them, initialize them
                    # somewhere __alloc_un
                    #
                    writable = True
                    in_section = False
                    try:                    
                        for _, sec in  self.__proj.loader.main_object.sections_map.iteritems():
                            if sec.contains_addr(con_addr):
                                print 'sec.is_writable', sec.is_writable
                                writable &= sec.is_writable
                                in_section = True
                        
                        if not in_section:
                            rwx = state.memory.permissions(con_addr)
                            print 'rwx', rwx
                            if state.se.eval(rwx) & 2 == 2:
                                writable = True
                            else:
                                writable = False                                
                    except Exception, e:
                        writable = False                        
                    # -------------------------------------------------------------------------

                    if writable == False:
                        warn("RSVP concretized but it has an invalid address '0x%x'" % con_addr)
                        # return False

                        # give it a second chance
                        self.__alloc_un(state, STR2BV[addr])
                        
                        con_addr = state.se.eval(STR2BV[addr])


                except angr.errors.SimUnsatError:   # un-satisfiable constraints
                    dbg_prnt(DBG_LVL_2, "Reservation was un-satisfiable. Discard current path.")
                    print 'SSSSS', self.__state.se.constraints
                    return False                    # reservation failed
                
                except Exception, e:
                    dbg_prnt(DBG_LVL_2, "Unknown Exception '%s'. Discard current path." % str(e))
                    return False                    # reservation failed


                # if this address has already been written in the past, any writes will
                # be overwritten, so discard current path                
                #if con_addr in self.__mem or con_addr in self.__imm or (con_addr + 7) in self.__imm:
                if con_addr in self.__imm or (con_addr + 7) in self.__imm:
                    dbg_prnt(DBG_LVL_2, "RSVP 0x%x has already been written or it's immutable. "
                                        "Discard current path." % con_addr)

                    return False                    # reservation failed


                # write value byte-by-byte. Memory address must also be immutable
                p_val = struct.pack("<Q", val)

                # print 'WRITING:', hex(val), 'at ', hex(con_addr)

                # this was problematic (endianess was fucked up)
                # self.__mwrite(state, con_addr, 8, p_val)
                

                # before you write the value, check if the contents of this address are already
                # in the contraints
                symv = self.__mread(state, con_addr, 8)
                print 'PRIOR VALUE at', hex(con_addr), '::', symv
                if self.__in_constraints(symv) or [V for V in self.__inireg.values() if V.shallow_repr() == symv.shallow_repr()]:
                    dbg_prnt(DBG_LVL_2, "RSVP already in constraints!")
                else:
                    symv = None


                for i in range(8):                    
                    state.memory.store(con_addr + i, p_val[i])
                    self.__imm.add(con_addr + i)    # mark immutable addresses at byte granularity


                # add reservation to memory
                self.__mem[ con_addr ] = (val, 8)

                dbg_prnt(DBG_LVL_2, "Writing RSVP *0x%x = 0x%x" % (con_addr, val))

                if symv != None:
                    # add the new contraint
                    state.add_constraints(symv == val)

                    if not state.satisfiable():
                        dbg_prnt(DBG_LVL_2, "RSVP caused constraints to be unsatisfiable. Discard Path")
                        return False

               # print '$$$$$$$$$$$$$$$$$$$$$$$$$', self.__mread(state, con_addr, 8)

        # print 'FINITO MEM_RSVPz', state.satisfiable(), state.se.satisfiable()
        # print 'CONSTRAINTS', state.se.constraints
        
        self.__disable_hooks = False                # enable hooks again

        return True                                 # reservation was successful



    # ---------------------------------------------------------------------------------------------
 
    ''' ======================================================================================= '''
    '''                          INTERNAL FUNCTIONS - TRACE MANAGEMENT                          '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __simulate_subpath(): This internal function performs the actual symbolic execution, for
    #       the candidate subpath. It guides symbolic execution through the specific subpath.
    #
    # :Arg sublen: The length of the subpath
    # :Arg subpath: The actual subpath
    # :Arg mode: The simluation mode for each step
    # :Ret: If the subpath can be simulated successfully, function returns the new state for the
    #       symbolic execution. Otherwise, function returns None.
    #
    def __simulate_subpath( self, sublen, subpath, mode ):
        emph("Trying subpath (%d): %s" % (sublen, 
                        ' -> '.join(['0x%x' % p for p in subpath])), DBG_LVL_2)
   
 
        self.__disable_hooks = False                # enable hooks

        # Register the signal function handler
        signal.signal(signal.SIGALRM, self.__sig_handler)

        # clone current state (so we can revert if subpath extension fails)
        self.stash_context()

        state = self.__state.copy()

        # create hte simulation manager object
        simgr = self.__proj.factory.simulation_manager(thing=state)
        # angr.manager.l.setLevel(logging.ERROR)
        

        found = simgr.active[0]                     # a.k.a. state
        
        dbg_arb(DBG_LVL_3, "BEFORE Constraints: ", found.se.constraints)

        # guide the symbolic execution: move from basic block to basic block
        for blk in subpath[1:]:
            simgr.drop(stash='errored')             # drop errored stashes
            signal.alarm(SE_TRACE_TIMEOUT)          # define a timeout for the SE engine


            self.__sim_mode = mode.pop(0)

            try:
                dbg_prnt(DBG_LVL_3, "Next basic block: 0x%x" % blk)
                # simgr.explore(find=blk)             # try to move on the next block
                # simgr.step()


                node = ADDR2NODE[found.addr]
                # print 'NODE ', node, len(node.instruction_addrs)

                num_inst = len(node.instruction_addrs) if node is not None else None
                if num_inst:
                    simgr.step(num_inst=num_inst)

                else:
                    NEW = simgr.step()
                    # print 'NEW', NEW, NEW.errored


            except Exception, msg:                   
                dbg_prnt(DBG_LVL_3, "Subpath failed. Exception raised: '%s'" % bolds(str(msg)))
                found = None                        # nothing found
                break                               # abort

            signal.alarm(0)                         # disable alarm

            if not simgr.active:
                # print 'Stashes', simgr.stashes
                dbg_arb(DBG_LVL_3, "Constraints: ", found.se.constraints)

                dbg_prnt(DBG_LVL_3, "Subpath failed (No 'active' stashes)")
                found = None                        # nothing found
                break                               # abort
        
    
            #print 'Stashes', simgr.stashes

            found = None                     # nothing found

            # print 'Stashes', simgr.stashes            
            # print 'state.satisfiable():', simgr.active[0].satisfiable()

            # drop any active stashes and make found stashes, active so you
            # can continue the search           
            simgr.move(from_stash='active', to_stash='found', \
                            filter_func=lambda s: s.addr == blk)
            
            simgr.drop(stash='active')
            simgr.move(from_stash='found', to_stash='active')
                    
            
            if simgr.active:
                found = simgr.active[0]             # TODO: Shall we use .copy() here?

                dbg_prnt(DBG_LVL_3, "Block 0x%x found!" % blk)
                dbg_arb(DBG_LVL_3, "Constraints: ", found.se.constraints)
                
            # print 'FOUND IS ', found
            # self.__sim_mode = SIM_MODE_DISPATCH
            

        if not found:                               # if nothing found, drop cloned state
            print 'Stashes', simgr.stashes

            self.unstash_context()
            del state
        else:            
            self.drop_context_stash()
            dbg_prnt(DBG_LVL_3, "Subpath simulated successfully!")

        signal.alarm(0)                             # disable alarm

        self.__disable_hooks = True                 # hooks should be disabled        

        return found                                # return state (if any)



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor. Create and initialize a blank state and prepare the
    #       environment for the symbolic execution.
    #
    # :Arg project: Instance of angr project
    # :Arg cfg: Binary's CFG
    # :Arg clobbering: Dictionary of clobbering blocks
    # :Arg adj: The SPL adjacency list
    # :Arg IR: SPL's Intermediate Representation (IR)
    # :Arg varmap: The register mapping
    # :Arg regmap: The variable mapping
    # :Arg rsvp: The reserved memory addresses for variables
    # :Arg entry: Payload's entry point
    #
    def __init__( self, project, cfg, clobbering, adj, IR, regmap, varmap, rsvp, entry ):
        self.__proj = project                       # store arguments internally
        self.__cfg  = cfg
        self.__IR   = IR
        self.__rsvp = rsvp
        self.__regmap = regmap

        self.__imm    = set()                       # immutable addresses
        self.__sym    = { }                         # symbolic variables
        self.__inireg = { }                         # initial register symbolic variables

        self.__reg = { }                            # final output for registers,
        self.__mem = { }                            # memory and
        self.__ext = { }                            # external data (from files, sockets, etc.)


        # 0xca00013b is actually pool_base + 0x13b
        self.__relative = { }
        
        self.condreg = ''
        # regsets that are not checked after block execution
        self.unchecked_regsets = []

        # even though we avoid all clobbering blocks from our path, this doesn't mean that
        # registers may not get clobbered. This usally happens inside system or library calls
        # where registers are being changed, even though there are no clobbering blocks.
        # 
        # to deal with it, we simply mark a register as immutable after 
        #
        # all register that used by SPL are immutable (only functional blocks can modify them)
        #        
        self.__imm_regs = set()                     # initially empty; add registers on the fly
        #self.__imm_regs = set([real for _, real in regmap])

        self.__sim_mode = SIM_MODE_INVALID

        self.FOO = []

#        print 'RSVPs', 
#        for addr, x in sorted(rsvp.iteritems()):
#            print hex(addr), x


        # the base adress that uninitialized symbolic variables should be allocated 
        # don't start form 0 to catch allocations that start BEFORE the initial (.e.g. if 
        # [rax + 0x20] = ALLOC, then rax will be below allocator)
        self.__alloc_size = 0x100          
        
        # create a CFG shortest path object
        self.__cfg_sp = path._cfg_shortest_path(self.__cfg, clobbering, adj)

        # create a symbolic execution state
        self.__state = self.__proj.factory.call_state(
                                    mode       = 'symbolic', 
                                    addr       = entry, 
                                    stack_base = STACK_BASE_ADDR, 
                                    stack_size = 0x10000
                        )


        # initialize all registers with a symbolic variable
        self.__state.regs.rax = self.__state.se.BVS("rax", 64)
        self.__state.regs.rbx = self.__state.se.BVS("rbx", 64)
        self.__state.regs.rcx = self.__state.se.BVS("rcx", 64)
        self.__state.regs.rdx = self.__state.se.BVS("rdx", 64)
        self.__state.regs.rsi = self.__state.se.BVS("rsi", 64)
        self.__state.regs.rdi = self.__state.se.BVS("rdi", 64)
        
        # rsp must be concrete and properly initialized
        self.__state.registers.store('rsp', RSP_BASE_ADDR, size=8)

        # rbp may also needed as it's mostly used to access local variables (e.g., 
        # rax = [rbp-0x40]) but some binaries don't use rbp and all references are
        # rsp related. In these cases it may worth to use rbp as well.
        if MAKE_RBP_SYMBOLIC:
            self.__state.regs.rbp = self.__state.se.BVS("rbp", 64)
        else:
            self.__state.registers.store('rbp', FRAMEPTR_BASE_ADDR, size=8)        

        self.__state.regs.r8  = self.__state.se.BVS("r08", 64)
        self.__state.regs.r9  = self.__state.se.BVS("r09", 64)
        self.__state.regs.r10 = self.__state.se.BVS("r10", 64)
        self.__state.regs.r11 = self.__state.se.BVS("r11", 64)
        self.__state.regs.r12 = self.__state.se.BVS("r12", 64)
        self.__state.regs.r13 = self.__state.se.BVS("r13", 64)
        self.__state.regs.r14 = self.__state.se.BVS("r14", 64)
        self.__state.regs.r15 = self.__state.se.BVS("r15", 64)


        # remember the initial symbolic variables for the registers
        self.__inireg = { r : self.__getreg(r) for r in HARDWARE_REGISTERS }


        # initialize SPL variables        
        self.__init_vars( varmap )  # this can trhow an exception
      

        # An alternative way to enable/disable hooks is this:
        #       s = state.inspect.b('mem_write', ...)
        #       s.enabled = False
        self.__disable_hooks = False                # enable breakpoints 
       
        self.__state.inspect.b('mem_write', when=angr.BP_BEFORE, action=self.__dbg_write_hook )
        self.__state.inspect.b('mem_read',  when=angr.BP_BEFORE, action=self.__dbg_read_hook  )  
        self.__state.inspect.b('reg_write', when=angr.BP_BEFORE, action=self.__dbg_reg_wr_hook)
        self.__state.inspect.b('symbolic_variable', 
                                            when=angr.BP_AFTER,  action=self.__dbg_symv_hook  )
        self.__state.inspect.b('call',      when=angr.BP_AFTER, action=self.__dbg_call_hook   )
        


        self.__origst = self.__state.copy()         # create a copy of the original state


        # deep copy 
        self.imm           = self.__imm
        self.sym           = self.__sym
        self.inireg        = self.__inireg
        self.reg           = self.__reg
        self.mem           = self.__mem
        self.ext           = self.__ext
        self.relative      = self.__relative
        self.imm_regs      = self.__imm_regs
        self.alloc_size    = self.__alloc_size
        self.state         = self.__state        
        self.disable_hooks = self.__disable_hooks = False                # enable breakpoints         


        self.project    = project
        self.cfg        = cfg
        self.clobbering = clobbering
        self.adj        = adj
        self.IR         = IR
        self.regmap     = regmap
        self.varmap     = varmap
        self.rsvp       = rsvp
        self.entry      = entry



    # ---------------------------------------------------------------------------------------------
    # __check_regsets(): TODO:
    #
    # Some RSVPs have weird addresses that we can't even concretize right before the block execution:
    #   <Bool (Reverse(symbolic_read_unconstrained_277383_64) + (r13_277379_64 << 0x3)) == x_472_64>
    #
    # This means that our reservation will be wrong and the register will never be assigned to the
    # right vaalue. A quick patch here, is to check whether register gets concretized to the right
    # value after the block execution and if not we add the desired constraint
    #
    # <Bool (0#32 .. (mem_d8003100_481_64[31:0] & 0xf8000000)) != 0x30000000>]
    #
    def __check_regsets( self, state=None ):
        if not state:
            state = self.__state

        # print '^^^^^^^^^^^^^^', self.unchecked_regsets


        for reg, val in self.unchecked_regsets:
            if isinstance(val, tuple):
                pass
                warn('Oups!')

            else:
                if state.se.eval( self.__getreg(reg, state) ) != val:
                    
                    warn('Wrong concretized value! Fixing it.... %x != %x' %                        
                            (state.se.eval( self.__getreg(reg, state) ), val))

                    # print '-----------> ',  reg, self.__getreg(reg, state)
                    state.add_constraints(self.__getreg(reg, state) == val)

                    if not state.satisfiable():
                        dbg_prnt(DBG_LVL_2, "Reservation constraint was un-satisfiable. Rolling back...")

                        self.unchecked_regsets = [] # all registers are checked!
                        return False                # check failed

        pass

        self.unchecked_regsets = []                 # all registers are checked!

        return True


    
    # ---------------------------------------------------------------------------------------------
    # simulate_edge(): This function is invoked for every edge in the induced subgraph Hk and it
    #       performs a symbolic execution from one accepted block to another. Essentially, its
    #       purpose is to find a "dispatcher gadget" (i.e., a sequence of non-clobbering blocks)
    #       between two SPL statements.
    #
    #       Unfortunately, the symbolic execution engine, may take forever to move from the one
    #       accepted block to the other To address this issue, we "guide" the symbolic execution,
    #       by selecting the exact subpath that will follow. This path however, is just an 
    #       estimation so it may not be correct. Therefore, simulate_edge() quickly generates
    #       candidate subpaths, starting from the shortest one.
    #
    #       simulate_edge() generates PARAMETER_P different subpaths. However, if we let it
    #       generate all possible paths, the result will be the same with the unguided symbolic
    #       execution.
    #
    # :Arg currb: Address of the current basic block
    # :Arg nextb: Address of the basic block that we want to reach
    # :Arg uid: Current UID of the payload
    # :Arg loopback: A boolean indicating whether we should simulate a path or a loop
    # :Ret: If function can extend the path, it returns the basic block path. Otherwise, it returns
    #   None.
    #
    def simulate_edge( self, currb, nextb, uid, loopback=False ):
        dbg_prnt(DBG_LVL_2, "Simulating edge (0x%x, 0x%x) for UID = %d" % (currb, nextb, uid))


        # indicate the boundaries 
#        self.__blk_start = currb
#        self.__blk_end   = currb + ADDR2NODE[currb].size
#
#        print 'BLK START', hex(self.__blk_start)
#        print 'BLK ENDDD', hex(self.__blk_end)


#        for a in self.__imm: print 'self.__imm', hex(a)        

        # Check if current basic block matches with the address of the current state
        if currb != self.__state.addr:              # base check            
            raise Exception('Illegal transition from current state ' 
                        '(starts from 0x%x, but state is at 0x%x)' % (currb, self.__state.addr))

        if loopback and currb != nextb:             # base check
            raise Exception('Loopback mode on distinct blocks')


        # apply any memory reservations (even if currb == nextb)   
        if not self.__mem_RSVPs( self.__state, cur_uid=uid, cur_blk=currb ):
            return None


        # print 'SELF CON', self.__state.se.constraints



        self.__disable_hooks = True
        
        for var in self.FOO:
            # print ' var', str(var)
            if var.shallow_repr() in SYM2ADDR:
                addr, size = SYM2ADDR[var.shallow_repr()]

                MEM = self.__mread(self.__state, SYM2ADDR[var.shallow_repr()][0], 
                                                 SYM2ADDR[var.shallow_repr()][1])

                if "mem_" not in MEM.shallow_repr():
                    self.__init_mem(self.__state, addr, size)
        
                    MEM = self.__mread(self.__state, SYM2ADDR[var.shallow_repr()][0], 
                                                     SYM2ADDR[var.shallow_repr()][1])


               # print 'QQ', SYM2ADDR[var.shallow_repr()], '%%%%', len(var), '==', len(MEM), '|', var, '?', MEM
                
                
                if len(var) != len(MEM):                                    
                    error('Symbolic variable alias found but size is inconsistent. Discard current path...')                    

                # if it's already a concreate value don't add a constraint
                else:
                    # print 'ADD CONSTRAINT FOO', var, MEM
                    self.__state.add_constraints(var == MEM)
                
            else:
                pass
            
        # print 'ok'


        # update immutable register set
        if self.__IR[uid]['type'] == 'regset':
            
            reg = [r for v, r in self.__regmap if v == '__r%d' % self.__IR[uid]['reg']][0]

            dbg_prnt(DBG_LVL_3, "Adding register '%s' to the immutable set." % reg)
            self.__imm_regs.add(reg)


        # ---------------------------------------------------------------------
        # Loopback mode
        # ---------------------------------------------------------------------
        if loopback:
            dbg_prnt(DBG_LVL_2, "Simluation a loop, starting from 0x%x ..." % self.__state.addr)
            
            # guide the symbolic execution: generate P shortest loops
            for length, loop in self.__cfg_sp.k_shortest_loops(currb, uid, PARAMETER_P):

                if length > MAX_ALLOWED_SUBPATH_LEN:    # if loop is too long, discard it
                    # This won't happen as the same check happens inside path.py, but we 
                    # should keep modules independent 

                    dbg_prnt(DBG_LVL_3, "Loop is too big (%d). Discard current path ..." % length)
                    break
            

                mode = [SIM_MODE_FUNCTIONAL] + [SIM_MODE_DISPATCH]*(len(loop)-2) + [SIM_MODE_FUNCTIONAL]

                # if we need to simulate loop multiple times, we unroll current loop by a constant
                # factor
                if SIMULATED_LOOP_ITERATIONS > 2:
                    loop = loop[:-1]*(SIMULATED_LOOP_ITERATIONS-1)
                    mode = mode[:-1]*(SIMULATED_LOOP_ITERATIONS-1)

                # warn('LOOP IS %s' % pretty_list(loop))

                # do the actual symbolic execution and verify that loop is correct
                nextst = self.__simulate_subpath(length, loop, mode)

                if nextst != None:                      # success!
                    emph("Edge successfully simulated.", DBG_LVL_2)

                    del self.__state                    # we don't need current state
                    self.__state = nextst               # update state

                    return loop                         # return subpath
            

        # ---------------------------------------------------------------------
        # Path mode
        # ---------------------------------------------------------------------                    
        else:
            # guide the symbolic execution: generate P shortest paths
            for slen, subpath in self.__cfg_sp.k_shortest_paths(currb, nextb, uid, PARAMETER_P):

                if slen > MAX_ALLOWED_SUBPATH_LEN:      # if subpath is too long, discard it
                    break


                mode = [SIM_MODE_FUNCTIONAL] + [SIM_MODE_DISPATCH]*(len(subpath)-1)

                # do the actual symbolic execution and verify if subpath is correct
                nextst = self.__simulate_subpath(slen, subpath, mode)

                if nextst != None:                      # success!
                    dbg_prnt(DBG_LVL_2, "Edge successfully simulated.")

                    if slen > 0:
                        # print 'unchecked_regsets', self.unchecked_regsets
                        self.__check_regsets(nextst)


                    del self.__state                    # we don't need current state
                    self.__state = nextst               # update state
            
                    return subpath                      # return subpath


                # TODO: !!!
                #   All paths that endup in some loop here get exeuted exactly once. #
                #   It's very hard to follow and simulate > 1 times here. We leave it
                #   as a future work.

        # we cannot simulate this edge. Try another induced subgraph
        dbg_prnt(DBG_LVL_2, "Cannot simulate egde. Discarding current induced subgraph...")
        
        return None                             # no subpath to return



    # ---------------------------------------------------------------------------------------------
    # finalize(): The symbolic variables that are part of the constraints and get overwritten
    #       are concretized during the symbolic execution (__dbg_write_hook). However there are 
    #       other symbolic variables that are part of the constraints, but they don't get
    #       overwritten. This function concretizes symbolic variables left in final staet.
    #
    # :Ret: None.
    #
    def finalize( self ):       
        # ---------------------------------------------------------------------
        # TODO: Having a primitive to set registers may be useless.
        #       Give the option to the attacker to be able to discard solutions
        #       that use apriori registers
        #
        # ---------------------------------------------------------------------
        dbg_prnt(DBG_LVL_0, 'Finalizing Apriori Register Assignments (if any):')

            # for reg, val in self.__reg.iteritems():
            #     # tuples are not part of the constraints and therefore are discarded
            #     if isinstance(val, tuple):
            #         pass

        for reg, symv in self.__inireg.iteritems():           
            
            # check if any of the original register is still in the constraints
            if self.__in_constraints(symv):
                val = self.__state.se.eval(symv)
                self.__inireg[ reg ] = val

                emph('Apriori register found: %s = 0x%x' % (reg, val), DBG_LVL_0)

            else:
                self.__inireg[ reg ] = None

        if self.condreg:
            symv = self.__getreg(self.condreg)           
            print '--------------- CONDREG', self.condreg, symv
            
            if self.__in_constraints(symv):
                val = self.__state.se.eval(symv)
                emph('Conditional register found: %s = 0x%x' % (self.condreg, val), DBG_LVL_0)

                self.condreg = (self.condreg, val)

            else:
                self.condreg = ''                

        # ---------------------------------------------------------------------
        # Concretize leftovers
        # ---------------------------------------------------------------------       
        dbg_prnt(DBG_LVL_2, 'Finalizing %d memory addresses...' % len(self.__mem))

        for addr, val in self.__mem.iteritems():
            dbg_prnt(DBG_LVL_3, 'Inspecting address 0x%x ...' % addr)

            # if __mem[addr] is in the form (value, size), then it's already concretized,
            # so don't take any actions            
            if isinstance(val, tuple):
                continue

            # if address is not concretized already and it's in the symbolic variable set
            if addr in self.__sym and val > 0:
                symv = self.__sym[ addr ]           # get symbolic variable

                if self.__in_constraints(symv):     # if part of the constraints, concretize it
                    realval          = self.__state.se.eval(symv)
                    self.__mem[addr] = (realval, val)

                    emph('\tAddress/Value pair found: *0x%x = 0x%x (%d bytes)' % 
                            (addr, realval, val), DBG_LVL_2)


                    if addr in self.__ext.values():
                        dbg_prnt(DBG_LVL_2, '\tAddress holds an external symbolic variable!')

                else:
                    dbg_prnt(DBG_LVL_3, '\tAddress is not in the constraints.')
                    self.__mem[ addr ] = None           # discard address

            else:
                self.__mem[ addr ] = None           # discard address
                dbg_prnt(DBG_LVL_3, '\tAddress is not needed.')


        # TODO: This case "SYM DICT: 0xd8001000 <BV64 __add__(0xa, r12_562_64, r14_564_64)>"
        # will give wrong results when concretized if r12 is relative

        # for a, b in self.__sym.iteritems():
        #     print 'SYM DICT:', hex(a), b
        

        # ---------------------------------------------------------------------
        # Concretize external input
        # ---------------------------------------------------------------------       
        dbg_prnt(DBG_LVL_0, 'External Input (if any): ')        

        for var, addr in self.__ext.items():                
            dbg_prnt(DBG_LVL_3, "Inspecting external input '%s'" % var.shallow_repr())

            # print var, addr


            # ---------------------------------------------------------------------
            # Some external variables may be part of the constraints, but not
            # written to memory
            # ---------------------------------------------------------------------       
            if addr == EXTERNAL_UNINITIALIZED:
                concr = False


                if self.__in_constraints(var):
                    concr = True
                    ext = var.shallow_repr()

                elif SYMBOLIC_FILENAME in var.shallow_repr():
                    # print 'insize ;)'

                    
                    # check again if it's in the constraints
                    for constraint in self.__state.se.constraints:
                        # treat constraint as an AST and iterate over its leaves
                        for leaf in constraint.recursive_leaf_asts:
                            # we can't compare them directly, so we cast them into strings first
                            # (not a very "clean" way to do that, but it works)
                            if SYMBOLIC_FILENAME in leaf.shallow_repr():
                                concr = True
                                ext = SYMBOLIC_FILENAME

                    
                if concr:
                    value = self.__state.se.eval(var)

                    dbg_prnt(DBG_LVL_3, 'External value (%s) found: 0x%x' % 
                                            (ext, value))

                    self.__ext[ var ] = (addr, value)

                else:
                    dbg_prnt(DBG_LVL_3, 'External value is not needed.')

                continue


            elif addr == None or addr not in self.__sym:
                warn('External symbolic variable is not set')

                del self.__ext[var]
                continue
            
                            
            value = self.__state.se.eval(self.__sym[addr])

             
            dbg_prnt(DBG_LVL_3, 'External value found: 0x%x' % value)

            self.__ext[ var ] = (addr, value)



    # ---------------------------------------------------------------------------------------------
    # step(): This function moves the execution forward by 1 basic block.
    #
    # :Arg stmty: The type of the last statement
    # :Ret: None.
    #
    def step( self, stmt ):
        dbg_prnt(DBG_LVL_2, "Moving one step forward from 0x%x ..." % self.__state.addr)


        # create hte simulation manager object
        simgr = self.__proj.factory.simulation_manager(thing=self.__state)
    

        self.__blk_start = self.__state.addr
        self.__blk_end   = self.__state.addr + ADDR2NODE[self.__state.addr].size

        # print 'BLK START STEP', hex(self.__blk_start)
        # print 'BLK ENDDD STEP', hex(self.__blk_end)


        self.__disable_hooks = False                # enable hooks to capture reads/writes

        # this should throw no exception (it was already successful in absblk.py)
        if stmt['type'] == 'call':
            self.__sim_mode = SIM_MODE_DISPATCH
        else:
            # step is in functional mode ;)
            self.__sim_mode = SIM_MODE_FUNCTIONAL
        try: 


            try:
                node = ADDR2NODE[self.__state.addr]

            except Exception, e:
                node = None

            num_inst = len(node.instruction_addrs) if node is not None else None
            if num_inst:
                simgr.step(num_inst=num_inst)
            else:
                simgr.step()
                

        except Exception, msg:                   
            dbg_prnt(DBG_LVL_3, "Step failed. Exception raised: '%s'" % bolds(str(msg)))
            return -1

        except angr.errors.SimUnsatError:   # un-satisfiable constraints
            dbg_prnt(DBG_LVL_2, "Step constraints were un-satisfiable. Discard current path.")            
            return -1


        dbg_prnt(DBG_LVL_2, "Step simulated successfully.")

        if not simgr.active:
            print 'Stashes', simgr.stashes
            
            dbg_prnt(DBG_LVL_3, "Stop failed (No 'active' stashes)")            

            # We may endup in deadended state if the last block is a retn
            # TODO: Fix that
            return [0xdeadbeef]
            # return -1


        self.__disable_hooks = True                 # disable hooks again
        

        # pick the state (if > 1) with satisfiable constraints
        for state in simgr.active:
            dbg_prnt(DBG_LVL_3, "Checking constraints from state: 0x%x" % state.addr)            

            state_copy = state.copy()
            unchecked = self.unchecked_regsets[:]

            if self.__check_regsets(state_copy):
    
                self.__state = state_copy

                dbg_prnt(DBG_LVL_2, "Done.")
                dbg_arb(DBG_LVL_3, "Constraints: ", self.__state.se.constraints)


                return [state.addr for state in simgr.active]

            del state_copy
            self.unchecked_regsets = unchecked[:]

        return -1
       
    # ---------------------------------------------------------------------------------------------
    # __deepcopy__():
    #
    # :Ret: An identical hardcopy of the current object.
    #
    '''
    def __deepcopy__(self, memo):

        print '__deepcopy__(%s)' % str(memo)
        return simulate(copy.deepcopy(self, memo))

        fatal('return ORM(copy.deepcopy(dict(self)))')
    '''




    # ---------------------------------------------------------------------------------------------
    # clone(): This function clones the current simulation object, once it reaches a conditional
    #       basic block. TODO: elaborate
    #
    # :Arg condreg: The register that is used in the condition (must be symbolic)
    # :Ret: An identical hardcopy of the current object.
    #
    def clone( self, condreg ):
        
        dbg_prnt(DBG_LVL_1, "Cloning current state at 0x%x ..." % self.__state.addr)

        print 'RBX', self.__state.regs.rbx, self.__inireg['rbx'], self.__getreg('rbx')
        

        # TODO: That's a bad way to do it. Nevermind it works.
        if   condreg == 'rax': self.__state.regs.rax = self.__state.se.BVS("cond_rax", 64)                                
        elif condreg == 'rbx': self.__state.regs.rbx = self.__state.se.BVS("cond_rbx", 64)
        elif condreg == 'rcx': self.__state.regs.rcx = self.__state.se.BVS("cond_rcx", 64)
        elif condreg == 'rdx': self.__state.regs.rdx = self.__state.se.BVS("cond_rdx", 64)
        elif condreg == 'rsi': self.__state.regs.rsi = self.__state.se.BVS("cond_rsi", 64)
        elif condreg == 'rdi': self.__state.regs.rdi = self.__state.se.BVS("cond_rdi", 64)
        elif condreg == 'rbp': self.__state.regs.rbp = self.__state.se.BVS("cond_rbp", 64)
        elif condreg == 'r8':  self.__state.regs.r8  = self.__state.se.BVS("cond_r08", 64)
        elif condreg == 'r9':  self.__state.regs.r9  = self.__state.se.BVS("cond_r09", 64)
        elif condreg == 'r10': self.__state.regs.r10 = self.__state.se.BVS("cond_r10", 64)
        elif condreg == 'r11': self.__state.regs.r11 = self.__state.se.BVS("cond_r11", 64)
        elif condreg == 'r12': self.__state.regs.r12 = self.__state.se.BVS("cond_r12", 64)
        elif condreg == 'r13': self.__state.regs.r13 = self.__state.se.BVS("cond_r13", 64)
        elif condreg == 'r14': self.__state.regs.r14 = self.__state.se.BVS("cond_r14", 64)
        elif condreg == 'r15': self.__state.regs.r15 = self.__state.se.BVS("cond_r15", 64)

        self.condreg = condreg
        # self.__inireg[ condreg ] = self.__state.regs.rbx


        state_copy = self.__state.copy()                        

        # create hte simulation manager object
        simgr = self.__proj.factory.simulation_manager(thing=state_copy)
  
        print 'Stashes', simgr.stashes
        print 'Constraints', self.__state.se.constraints

        
        # this should throw no exception (it was already successful in absblk.py)
        simgr.step()

        print 'Stashes', simgr.stashes


        # we should have exactly 2 active stashes
        print simgr.active[0].se.constraints
        print simgr.active[1].se.constraints

        if len(simgr.active) != 2:              
            print simgr.active
            raise Exception('Conditional jump state should have 2 active stashes')
       

        dbg_prnt(DBG_LVL_2, "Done.")
        
        self.entry = self.__state.addr
        newsim = simulate(self.project, self.cfg, self.clobbering, self.adj, self.IR,
                                        self.regmap, self.varmap, self.rsvp, self.entry)
       
        newsim.imm           = copy.deepcopy(self.__imm)
        newsim.sym           = copy.deepcopy(self.__sym)
        newsim.inireg        = copy.deepcopy(self.__inireg)
        newsim.reg           = copy.deepcopy(self.__reg)
        newsim.mem           = copy.deepcopy(self.__mem)
        newsim.ext           = copy.deepcopy(self.__ext)
        newsim.relative      = copy.deepcopy(self.__relative)
        newsim.imm_regs      = copy.deepcopy(self.__imm_regs)
        newsim.FOO           = copy.deepcopy(self.FOO)
        newsim.alloc_size    = copy.deepcopy(self.__alloc_size)
        newsim.state         = self.__state.copy() #copy.deepcopy(self.__state)
        newsim.inireg        = copy.deepcopy(self.__inireg)
        newsim.disable_hooks = copy.deepcopy(self.__disable_hooks)
        newsim.unchecked_regsets = copy.deepcopy(self.unchecked_regsets)

        newsim.copy_locally()

        print 'Constraints', self.__state.se.constraints

    
        self.__state.add_constraints( simgr.active[1].se.constraints[-1] )
        newsim.state.add_constraints( simgr.active[0].se.constraints[-1] )

        del state_copy
        
        return newsim
        # return copy.deepcopy(self)
    
    

    # ---------------------------------------------------------------------------------------------
    # stash_context(): Save current context to a stash.
    #
    # :Ret: None.
    #
    def copy_locally( self ):       
        self.__imm           = self.imm
        self.__sym           = self.sym
        self.__inireg        = self.inireg
        self.__reg           = self.reg
        self.__mem           = self.mem
        self.__ext           = self.ext
        self.__relative      = self.relative
        self.__imm_regs      = self.imm_regs
        # self.FOO             = self.FOO
        self.__alloc_size    = self.alloc_size
        self.__state         = self.state
        self.__disable_hooks = self.disable_hooks

        
        # state will have action to the parent object. We have to readjust them?
        self.__state.inspect.b('mem_write', when=angr.BP_BEFORE, action=self.__dbg_write_hook )
        self.__state.inspect.b('mem_read',  when=angr.BP_BEFORE, action=self.__dbg_read_hook  )  
        self.__state.inspect.b('reg_write', when=angr.BP_BEFORE, action=self.__dbg_reg_wr_hook)
        self.__state.inspect.b('symbolic_variable', 
                                            when=angr.BP_AFTER,  action=self.__dbg_symv_hook  )
        self.__state.inspect.b('call',      when=angr.BP_AFTER, action=self.__dbg_call_hook   )
  


    # ---------------------------------------------------------------------------------------------
    # stash_context(): Save current context to a stash.
    #
    # :Ret: None.
    #
    def update_globals( self ):       
        self.imm           = self.__imm
        self.sym           = self.__sym
        self.inireg        = self.__inireg
        self.reg           = self.__reg
        self.mem           = self.__mem
        self.ext           = self.__ext
        self.relative      = self.__relative
        self.imm_regs      = self.__imm_regs
        # self.FOO           = self.FOO
        self.alloc_size    = self.__alloc_size
        self.state         = self.__state
        self.disable_hooks = self.__disable_hooks
          
        

    # ---------------------------------------------------------------------------------------------
    # stash_context(): Save current context to a stash.
    #
    # :Ret: None.
    #      self.__state.inspect.b('mem_write', when=angr.BP_BEFORE, action=self.__dbg_write_hook )  
    def stash_context( self ):       
        self.__stash_imm           = copy.deepcopy(self.__imm)
        self.__stash_sym           = copy.deepcopy(self.__sym)
        self.__stash_inireg        = copy.deepcopy(self.__inireg)
        self.__stash_reg           = copy.deepcopy(self.__reg)
        self.__stash_mem           = copy.deepcopy(self.__mem)
        self.__stash_ext           = copy.deepcopy(self.__ext)
        self.__stash_relative      = copy.deepcopy(self.__relative)
        self.__stash_imm_regs      = copy.deepcopy(self.__imm_regs)
        self.__stash_FOO           = copy.deepcopy(self.FOO)
        self.__stash_alloc_size    = copy.deepcopy(self.__alloc_size)
        self.__stash_state         = self.__state.copy() #copy.deepcopy(self.__state)
        self.__stash_disable_hooks = copy.deepcopy(self.__disable_hooks)
        self.__stash_unchecked_regsets = copy.deepcopy(self.unchecked_regsets)



    # ---------------------------------------------------------------------------------------------
    # drop_context_stash(): Drop context stash.
    #
    # :Ret: None.
    #
    def drop_context_stash( self ):       
        del self.__stash_imm
        del self.__stash_sym 
        del self.__stash_inireg
        del self.__stash_reg
        del self.__stash_mem
        del self.__stash_ext 
        del self.__stash_relative
        del self.__stash_imm_regs
        del self.__stash_FOO
        del self.__stash_alloc_size
        del self.__stash_state 
        del self.__stash_disable_hooks
        del self.__stash_unchecked_regsets 



    # ---------------------------------------------------------------------------------------------
    # unstash_context(): Remove a context from stash and use it.
    #
    # :Ret: None.
    #
    def unstash_context( self ):       
        del self.__imm
        del self.__sym
        del self.__inireg
        del self.__reg
        del self.__mem
        del self.__ext
        del self.__relative
        del self.__imm_regs
        del self.FOO
        del self.__alloc_size
        del self.__state
        del self.__disable_hooks
        del self.unchecked_regsets

        self.__imm           = self.__stash_imm
        self.__sym           = self.__stash_sym 
        self.__inireg        = self.__stash_inireg
        self.__reg           = self.__stash_reg
        self.__mem           = self.__stash_mem
        self.__ext           = self.__stash_ext 
        self.__relative      = self.__stash_relative
        self.__imm_regs      = self.__stash_imm_regs
        self.FOO             = self.__stash_FOO
        self.__alloc_size    = self.__stash_alloc_size
        self.__state         = self.__stash_state 
        self.__disable_hooks = self.__stash_disable_hooks
        self.unchecked_regsets = self.__stash_unchecked_regsets



    # ---------------------------------------------------------------------------------------------
    # constraints(): Get constraints.
    #
    # :Ret: None.
    #
    def constraints( self ):
        return self.__state.se.constraints



    # ---------------------------------------------------------------------------------------------
    # __make_relative(): Make an address relative (if needed).
    #
    # :Arg addr: Current address
    # :Ret: A string with the realtive address.
    #
    def __make_relative( self, addr ):
        '''
        # TODO: breaks for eval/orzhttpd/orzhttpd -s payloads/memrd.spl        
        elif abs(addr - FRAMEPTR_BASE_ADDR) < MAX_BOUND or abs(addr - RSP_BASE_ADDR) < MAX_BOUND:

            if abs(addr - RSP_BASE_ADDR) < abs(addr - FRAMEPTR_BASE_ADDR):

                if addr > RSP_BASE_ADDR:
                    return "($stack + 0x%03x)" % (addr - RSP_BASE_ADDR)
                else:
                    return "($stack - 0x%03x)" % (RSP_BASE_ADDR - addr)

            else:
                if addr > FRAMEPTR_BASE_ADDR:
                    return "($frame + 0x%03x)" % (addr - FRAMEPTR_BASE_ADDR)
                else:
                    return "($frame - 0x%03x)" % (FRAMEPTR_BASE_ADDR - addr)
        '''


        if addr in self.__relative:                 # if in relative table
            return '(' + self.__relative[addr] + ')'

        # frame first
        elif abs(addr - RSP_BASE_ADDR) < MAX_BOUND:
            if addr > RSP_BASE_ADDR:
                return "($stack + 0x%03x)" % (addr - RSP_BASE_ADDR)
            else:
                return "($stack - 0x%03x)" % (RSP_BASE_ADDR - addr)

        elif abs(addr - FRAMEPTR_BASE_ADDR) < MAX_BOUND:
            if addr > FRAMEPTR_BASE_ADDR:
                return "($frame + 0x%03x)" % (addr - FRAMEPTR_BASE_ADDR)
            else:
                return "($frame - 0x%03x)" % (FRAMEPTR_BASE_ADDR - addr)
    
   
        elif abs(addr - POOLVAR_BASE_ADDR) < MAX_BOUND:
            if addr > POOLVAR_BASE_ADDR:
                return "($pool + 0x%03x)" % (addr - POOLVAR_BASE_ADDR)
            else:
                return "($pool - 0x%03x)" % (POOLVAR_BASE_ADDR - addr)
            
        elif POOLVAR_BASE_ADDR <= addr <= POOLVAR_BASE_ADDR + self.__plsz:
            return "($pool + 0x%03x)" % (addr - POOLVAR_BASE_ADDR)


        elif ALLOCATOR_BASE_ADDR <= addr and addr <= ALLOCATOR_CEIL_ADDR:
            return "($alloca + 0x%03x)" % (addr - ALLOCATOR_BASE_ADDR)                    
            
        else:
            return "0x%x" % addr



    # ---------------------------------------------------------------------------------------------
    # __is_relative(): Check if an is relative
    #
    # :Arg addr: Current Address
    # :Ret: True if it's relative. False otherwise.
    #
    def __is_relative( self, addr ):

        if addr in self.__relative:                 # if in relative table
            return True

        elif abs(addr - RSP_BASE_ADDR) < MAX_BOUND:
            return True
        
        elif abs(addr - FRAMEPTR_BASE_ADDR) < MAX_BOUND:
            return True

        elif abs(addr - POOLVAR_BASE_ADDR) < MAX_BOUND:
            return True 

        elif POOLVAR_BASE_ADDR <= addr <= POOLVAR_BASE_ADDR + self.__plsz:
            return True

        elif ALLOCATOR_BASE_ADDR <= addr and addr <= ALLOCATOR_CEIL_ADDR:
            return True
            
        else:
            return False



    # ---------------------------------------------------------------------------------------------
    # dump(): Dump the results of the simulation.
    #
    # :Arg output: The output object
    # :Ret: None.
    #
    def dump( self, output ):
        # for a, b in self.__relative.iteritems():
        #     print 'relative', hex(a), b

        output.newline()
        
        if self.__plsz > 0:
            output.comment('Allocation size is always bigger (it may not needed at all)')
            output.alloc(POOLVAR_NAME, self.__plsz)
            output.newline()



        if self.__alloc_size > 0:
            output.comment('Allocation size is always bigger')
            output.alloc(ALLOCATOR_NAME, self.__alloc_size)
            output.newline()


        # TODO: make sure that there is a single $rbp, $stack, $frame (not 1 per fork)
        output.comment('OPTIONAL!')        
        output.set('$rbp', '$rsp + 0xc00')              # TODO: KEEP ME CONSISTENT!

        output.comment('Stack and frame pointers aliases')
        output.set('$stack', '$rsp')
        output.set('$frame', '$rbp')
        output.newline()


        # ---------------------------------------------------------------------
        # TODO: Having a primitive to set registers may be useless.
        #       Give the option to the attacker to be able to discard solutions
        #       that use apriori registers
        #
        dbg_prnt(DBG_LVL_0, 'Apriori Register Assignments (if any):')

        for reg, val in self.__reg.iteritems():
            # tuples are not part of the constraints and therefore are dfor simu in self.__simstash:iscarded
            if not isinstance(val, tuple):

                dbg_prnt(DBG_LVL_0, '\t%s = 0x%x (DROP)' % (reg, val))
                                
                #output.register(reg, val, comment='(DROP)')
                output.comment('(DROP) %s = %s' % (reg, val))
                #output.register(reg, val)
                #output.newline()

        output.newline()

        for reg, symv in self.__inireg.iteritems():
            # check if any of the original register is still in the constraints
            if symv != None:
                symv = self.__make_relative(symv)

                # print 'OUTPUT:', symv
                output.register(reg, symv)

        
        output.newline()

        if self.condreg and isinstance(self.condreg, tuple):            
            reg, symv = self.condreg
            symv = self.__make_relative(symv)
 
            output.comment('(CONDITIONAL) %s = %s' % (reg, symv))
             

        # ---------------------------------------------------------------------
        dbg_prnt(DBG_LVL_0, 'Memory Addresses for variables (if any):')

        output.newline()

        # variables
        for addr, values in self.__inivar_rel.iteritems():

            displacement = 0

            # check which elements from values are relative addresses
            for val in values:                
                if isinstance(val, str):            # string values are directly packed                    
                    pval = '{' + ', '.join("0x{0:02x}".format(ord(c)) for c in val) + '}'
                    size = len(val)

                else:
                    if not self.__is_relative(val):
                        pval = '{' + ', '.join("0x{0:02x}".format(ord(c)) for c in struct.pack("<Q", val)) + '}'
                    else:
                        pval = self.__make_relative(val)

                    size = 8



                # calculate address (base + offset + displacement)
                paddr = "(%s + 0x%02x)" % (self.__make_relative(addr), displacement)


                displacement += size                # shift inside variable's values
                output.memory(paddr, pval, size)
            

                dbg_prnt(DBG_LVL_0, "\t*%s = %s" % (paddr, pval))


        # ---------------------------------------------------------------------
        dbg_prnt(DBG_LVL_0, 'Other Memory Addresses:')

        output.newline()


        for addr, val in self.__mem.iteritems():
            if isinstance(val, tuple):

                # if val[0] in self.__relative:
                if "0x%x" % val[0] != self.__make_relative(val[0]):
                    # pval = '(' + self.__relative[ val[0] ] + ')'
                    pval = self.__make_relative(val[0])

                else:
                    # cast integer to zero padded hex string
                    x = ("{0:0%dx}" % (val[1] << 1)).format(val[0])

                    # cast string to bytes and change endianess 
                    x = ''.join(reversed(x.decode('hex')))

                    # print string in C-style format
                    pval = '{' + ', '.join("0x{0:02x}".format(ord(c)) for c in x) + '}'
                    #lval = ["0x{0:02x}".format(ord(c)) for c in x]


                paddr = self.__make_relative(addr)                
                #   output.memory(addr, '', addr, lval, op='+')

                for a, b in self.__ext.iteritems():
                    #print '^^^^^^^^^^', a, b, addr
                    if b != EXTERNAL_UNINITIALIZED and addr == b[0]:
                        output.comment('value comes from external input (DROP)')
                        break


                output.memory(paddr, pval, val[1])

                dbg_prnt(DBG_LVL_0, "\t*%s = %s\t# %d bytes" % (paddr, pval, val[1]))


        # ---------------------------------------------------------------------
        dbg_prnt(DBG_LVL_0, 'External Input (if any): ')
        
        # TODO: better variable names
        ext_stdin = { }
        ext_file  = { }
        ext_retn  = { }
        stdin, file, retn = [], [], []


        for var, value in self.__ext.iteritems():
            if value == EXTERNAL_UNINITIALIZED:
                continue
            

            if 'stdin' in var.args[0]:
                ext_stdin[ var.args[0] ] = value

            elif SYMBOLIC_FILENAME in var.args[0]:
                ext_file[ var.args[0] ] = value

            elif 'unconstrained_ret' in var.args[0]:
                ext_retn[ var.args[0].replace("unconstrained_ret___", "") ] = value

        
        for var in sorted(ext_stdin):
            stdin.append('0x%x' % ext_stdin[var][1])

        for var in sorted(ext_file):
            file.append('0x%x' % ext_file[var][1])

        for var in sorted(ext_retn):
            retn.append('%s = 0x%x' % (str(var), ext_retn[var][1]))
        
        dbg_arb(DBG_LVL_0, 'External input (stdin) :', stdin)
        dbg_arb(DBG_LVL_0, 'External input (file)  :', file)
        dbg_arb(DBG_LVL_0, 'External input (return):', retn)


        output.newline()
        output.comment('External input (stdin): %s'  % str(stdin))
        output.comment('External input (%s): %s'     % (SYMBOLIC_FILENAME, str(file)))
        output.comment('External input (return): %s' % str(retn))
        

        # for a,b in self.__relative.iteritems():
        #     print 'ADDR2SYM', hex(a), b


        dbg_prnt(DBG_LVL_0, "pool_base  = 0x%x" % POOLVAR_BASE_ADDR)
        dbg_prnt(DBG_LVL_0, "stack_base = 0x%x" % RSP_BASE_ADDR)
        


# -------------------------------------------------------------------------------------------------

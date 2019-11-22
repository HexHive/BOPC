#!/#!/usr/bin/env python2
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
# absblk.py:
#
# This module implements the basic block "abstractions". Abstraction is a process that summarizes
# a basic block into the "impact" on program's state.
#
# -------------------------------------------------------------------------------------------------
from coreutils import *
import signal
import simuvex
import claripy
import archinfo
import angr



# ------------------------------------------------------------------------------------------------
# Constant Definitions
# ------------------------------------------------------------------------------------------------
_STACK_SZ = 0x1000                                  # size of symbolic stack



# -------------------------------------------------------------------------------------------------
# abstract_ng: This class implements the next generation of the basic block "abstraction". So
#   far, the following abstractions are supported:
#  
#   * * Register Writes * *
#   A dictionary that contains all registers that are being written. The "write" information is
#   another dictionary with the following fields:
#
#       * type     : Can be 'concrete', 'deref', 'mod' or 'clob'. A register is of type 'clob'
#                    when, it does not fall to any of the other types
#       * const    : ('concrete' and 'mod' types). The constant value that is written to the
#                    register
#       * writable : ('concrete' types). If the constant value is a valid and writable memory
#                    address, then this field is set to True
#       * op       : ('mod' types). The modification operator
#       * addr     : ('deref' types). The address that register value is loaded from
#       * deps     : ('deref' types). Any registers that participate in addr field
#       * sym      : ('deref' types). A mapping between registers and their symbolic variables
#       * memrd    : ('deref' types). When the register write can be used as a memory read, this
#                    field contains the size of the memory read in bytes (1,2,4,8). Otherwise it
#                    is set to None
#
#   Example:
#       regwr = {
#           rsp : {'type': 'concrete', 'const': 576460752303357888L, 'writable': True },
#           rcx : {'type': 'deref', 'addr': <BV64 rsi_43_64 + 0x10>, 'deps': ['rsi']},
#           r9  : {'type': 'mod', 'op': '+', 'const': 1337L}
#       }
#
#
#   * * Memory Reads * *
#   A list of tuples (address, size) for every memory read.
#
#   Example:
#       memrd = set([(<SAO <BV64 0x7ffffffffff0810>>, 64), (<SAO <BV64 0x7ffffffffff0818>>, 64)])
#
#
#   * * Memory Writes * *
#   A list of tuples (address, data) for every memory write (len(data) indicates the size)
#
#   Example:
#       memwr = set([(<SAO <BV64 0x7ffffffffff07f8>>, <SAO <BV64 rbx_1_64>>), 
#                    (<SAO <BV64 0x7ffffffffff07e0>>, <SAO <BV64 0x416631>>)])
#
#
#   * * Concrete Writes * *
#   A list of tuples (address, size) for every concrete memory write.
#
#   Example:
#       conwr = set([(576460752303359992L, 64), (576460752303359968L, 64)])
#
#
#   * * SPL Memory Writes * *
#   A list of dictionaries for every SPL memory write (memory writes that are in the form:
#   "mov [rax], rbx"). Each dictionary contains the following fields:
#
#       * mem  : The register that holds the address to write (string)
#       * val  : The register that holds the value to be written (string)
#       * size : The number of bytes to write (e.g., mov [rax], cl, mov [rbx], dx)
#       * sym  : A mapping between registers and their symbolic variables
#
#   Example:
#       splmemwr = [{
#            'mem'  : 'rbx', 
#            'val'  : 'rax', 
#            'size' : 4,
#            'sym'  : {'rax': <BV64 rax_0_64>, 'rbx': <BV64 rbx_1_64>}
#       }]
#
#
#   * * Calls * *
#   A dictionary with the following fields:
#
#       * type : Can be 'syscall', or 'libcall'
#       * name : The name of the call
#
#   Example:
#       call = {'type': 'libcall', 'name': u'puts'}
#
#
#   * * Conditional Jumps * *
#   A dictionary with the following fields:
#
#       * form      : The form of the conditional jump ('simple' / 'extended')
#       * reg       : The register that participates in the conditional jump
#       * const     : The constant value that register is compared against
#       * op        : The comparison operator
#       * mod_op    : ('extended' types). The operator of the register modification
#       * mod_const : ('extended' types). The constant of the register modification
#
#   Example:
#       cond = {'reg': 'r11', 'op': '==', 'const': 11L}
#       cond = {'mod_op': '^', 'const': 0L, 'form': 'extended', 'op': '=='}
#
#
#   * * Symbolic Variables * *
#   A dictionary that maps the symbolic variables to their actual addresses that they correspond
#
#   Example:
#       symvar = {<BV64 mem_7fffffffffef1e8_82_64>' : 0x7fffffffffef1e8}
#
#
# * * * ---===== TODO list =====--- *
#
#   [1]. Make absblk more precise i.e., check the order of memory writes
#   [2]. Move this list at the beginning of the file.
#
class abstract_ng( object ):
    ''' ======================================================================================= '''
    '''                                   AUXILIARY FUNCTIONS                                   '''
    ''' ======================================================================================= '''
 
    # ---------------------------------------------------------------------------------------------
    # __reg_w(): Analyze the register writes of the symbolic execution.
    #
    # :Arg state: Program's state after symbolic execution
    # :Ret: None.
    #
    def __reg_w( self, state ): 
        visited = set()                             # visited registers

        for action in reversed(state.actions):      # for every action (start backwards)    
            if not (action.type == 'reg' and action.action == 'write'):
                continue                            # we care about register writes only                        

            try:
                # we only care about the most recent register write only            
                reg = self.__proj.arch.register_names[action.offset]
            except KeyError:
                continue

            # get the last write only
            if reg not in HARDWARE_REGISTERS or reg in visited:
                continue

            data = { }                              # various data related to the write
            visited.add(reg)                        # make sure that you won't visit this again


            # ---------------------------------------------------------------------------
            # If some address (initialized or not) is used as a dereference, the regwr
            # entry for that register must be preserved (we should not overwrite register
            # with the actual value in that address)
            # ---------------------------------------------------------------------------
            if reg in self.regwr and self.regwr[ reg ]['type'] == 'deref':
                continue

            # The register is being modified, so we start by marking it as clobbering
            if reg not in self.regwr:
                self.regwr[ reg ] = {'type' : 'clob'}

            
            # -----------------------------------------------------------------
            if action.data.concrete:                # if register gets a concrete value,
                value = state.se.eval(action.data)  # concretize it

                data['type']     = 'concrete'       # set data
                data['const']    = value
                data['writable'] = True             # initialize this first
                in_section = False

                # now, check whether this value is a writable address                
                try:                    
                    # The problem: There are some weird sections (.e.g., ".comment") whose VA
                    # starts from 0. Therefore, we may have register writes with constants like
                    # 1, 2 and so on, which are marked as +W. This means that at the end we can 
                    # have memory reservations (writes) at those addresses. Our old approach with 
                    # "state.memory.permissions(value)" doesn't work here.
                    #
                    # So iterate over ELF sections looking for it
                    for _, sec in  self.__proj.loader.main_object.sections_map.iteritems():                        
                        # it's possible for the value to be part of >1 sections (usually when
                        # section's VA is 0; sec.vaddr != 0). We mark value as +W only when *all*
                        # sections are writable
                        if sec.contains_addr(value):
                            data['writable'] &= sec.is_writable
                            in_section = True


                    # if can't find section (b/c it's generated at runtime, like .stack)
                    if not in_section:
                        # TODO: check if value+1, value+2, etc. are writable as well
                        rwx = state.memory.permissions(value)

                        if state.se.eval(rwx) & 2 == 2: # is +W (2nd bit) set?
                            data['writable'] = True
                        else:
                            data['writable'] = False
                        
                except Exception, e:                # page does not exist at given address
                    data['writable'] = False        # not writable at all

                    try:
                        # special case when a stack address is in the next page (-W)
                        if value & 0x07ffffffffff0000 == 0x07ffffffffff0000:
                            rwx = state.memory.permissions(value-0x4000)

                            # give it a second change
                            if state.se.eval(rwx) & 2 == 2:
                                data['writable'] = True

                    except Exception, e:            # or angr.errors.SimMemoryError
                        pass

            # -----------------------------------------------------------------
            else:                                   # register doesn't get a concrete value

                # register gets an expression. Check for simple register modifications: 
                # "<reg> <op>= <const>" (we can easily scale this to <reg> <op>= <reg>)
                # Note that modified register should be the same with action.offset
                node = [leaf for leaf in action.data.recursive_leaf_asts]
                    
                # we need an AST with depth 2, 2 leaves and 1 variable (i.e., register)
                if action.data.depth == 2 and len(action.data.variables) == 1 and len(node) == 2:
                    try:
                        data['op'] = {              # cast operator
                            '__add__'    : '+',
                            '__sub__'    : '-',
                            '__mul__'    : '*',
                            '__div__'    : '/',
                            '__and__'    : '&',
                            '__or__'     : '|',
                            '__xor__'    : '^',
                            '__invert__' : '~',
                            '__lshift__' : '<<',
                            '__rshift__' : '>>'
                        }[ action.data.op ]
                    
                        # if constant is on the left, swap sides
                        if node[0].op == 'BVV' and node[0].concrete:
                            node[0], node[1] = node[1], node[0]


                        # check if we're in the form: <reg> <op> <const> 
                        if node[0].op == 'BVS' and self.__symreg[node[0]] == reg and \
                           node[1].op == 'BVV' and node[1].concrete:
                                data['type']  = 'mod'
                                data['const'] = state.se.eval(node[1])
                        else:                       # not in the right form
                                continue

                    except KeyError:                # __symreg() threw an exception
                        continue

        
                # -----------------------------------------------------------------------
                # Consider the following case:
                #       .text:000000000040BA49         mov     eax, [rbp+tfd]
                #       .text:000000000040BA52         mov     edi, eax         ; fd
                #
                # Here, edi gets exactly the same value with eax, but edi is marked as
                # 'clob', while eax as 'deref'. The root cause is that edi does not
                # participate in any memory reads and the assigned value is not constant
                # (i.e., it doesn't come directly from a register).
                #
                # To fix that we check whether a 'clob' register has *exactly* the same 
                # symbolic value with another one (eax in our example), and if so we 
                # assign the same regwr entry to it.
                # -----------------------------------------------------------------------
                else:
                    # iterate over previous writes
                    for reg2, val in self.__reg_rawval.iteritems():
                        try:

                            # check if raw values match
                            if reg != reg2 and val.shallow_repr() == action.data.shallow_repr():

                                self.regwr[ reg ] = self.regwr[ reg2 ]
                                pass

                        except KeyError:
                            pass


            # -----------------------------------------------------------------
            if data:
                self.regwr[ reg ] = data            # set data to this register
        


    # ---------------------------------------------------------------------------------------------
    # __mem_r(): Analyze the memory reads of the symbolic execution.
    #
    # :Arg state: Program's state after symbolic execution
    # :Ret: None.
    #
    def __mem_r( self, state ):
        for action in state.actions:                # for every action        
            if not (action.type == 'mem' and action.action == 'read'):
                continue                            # we care about memory reads only

            # simply add address (can be an expression) and size to the list
            self.memrd.add( (action.addr, len(action.data)) )



    # ---------------------------------------------------------------------------------------------
    # __mem_w(): Analyze the memory writes of the symbolic execution.
    #
    # :Arg state: Program's state after symbolic execution
    # :Ret: None.
    #
    def __mem_w( self, state ):
        for action in state.actions:                # for every action        
            if not (action.type == 'mem' and action.action == 'write'):
                continue                            # we care about memory writes only

            # simply add address (can be an expression) and data to the list
            self.memwr.add( (action.addr, action.data) ) 
            
            if action.addr.concrete:                # if address is concrete
                # concretize it as well
                self.conwr.add( (state.se.eval(action.addr), len(action.data)) )


            deps   = [ ]
            symtab = { }

            # -----------------------------------------------------------------
            # Check for memory register writes (mov [rax], rbx)
            #
            # In this case, both action.addr and action.data will consist of a
            # single leaf in their ast which is a register
            # -----------------------------------------------------------------
            mem_reg = [leaf for leaf in action.addr.recursive_leaf_asts]
            val_reg = [leaf for leaf in action.data.recursive_leaf_asts]


            # print 'ADDR', mem_reg, action.addr
            # print 'ADDR', val_reg, action.addr
                 
            # check AST have a single leaf
            if len(mem_reg) == 1 and len(val_reg) == 1:
                mem, val = None, None

                # check whether the leaf is a register
                for sym, nam in self.__symreg.iteritems():
                    # skip registers that are not symbolic (e.g., rbp)
                    if isinstance(sym.args[0], str) and sym.args[0] in mem_reg[0].shallow_repr():                        
                        symtab[nam] = sym
                        mem         = nam

                    elif isinstance(sym.args[0], str) and sym.args[0] in val_reg[0].shallow_repr():                        
                        symtab[nam] = sym
                        val         = nam

                # if both leaves are registers we have a memory register write!
                if mem and val:                
                    self.splmemwr.append({
                        'mem'  : mem,
                        'val'  : val,
                        'size' : int(action.size) >> 3,
                        'sym'  : symtab,                      
                    })



    # ---------------------------------------------------------------------------------------------
    # __call(): Analyze the (sys|lib)calls of the symbolic execution. Because we're analyzing a
    #       single basic block, we can have up to one such (sys|lib)call (the last instruction).
    #
    # :Arg state: Program's state after symbolic execution
    # :Ret: None.
    #
    def __call( self, state ):
        blk = self.__proj.factory.block(self.__entry)

        # check if symbolic execution stopped on a syscall
        # (don't use "if self.__proj._simos.is_syscall_addr(state.addr)"; it throws exceptions)
        if blk.vex.jumpkind == "Ijk_Sys_syscall":
            # a system call was invoked
            # we assume that simproc.cc == SimCCAMD64LinuxSyscall                
            simproc = self.__proj._simos.syscall(state)

            self.call['type'] = 'syscall'
            self.call['name'] = simproc.display_name
            # self.call['nargs'] = simproc.num_args

        else:  
            if blk.vex.jumpkind != "Ijk_Call":      # skip block when it doesn't end with a call
                return


            # check if symbolic execution stopped on a library call
            for action in reversed(state.actions):  # for every action        
                if action.type != 'exit':
                    continue                        # we care about branches only


                # concretize function's entry point
                target = state.se.eval(action.target)

                # Note: Before you use kb.functions, calculate CFG (e.g., analyses.CFGFast())
                try:
                    self.call['type'] = 'libcall'
                    self.call['name'] = self.__proj.kb.functions[target].name
                except Exception:                   # no function name at that address
                    self.call = { }



    # ---------------------------------------------------------------------------------------------
    # __cond(): Analyze the conditional jump of the symbolic execution. Because we're analyzing a
    #       single basic block, we can have up to one conditional jump.
    #
    # :Arg state: Program's state after symbolic execution
    # :Ret: None.
    #
    def __cond( self, state ):        
        for action in reversed(state.actions):      # for every action        
            if not (action.type == 'exit' and action.exit_type == 'conditional'):
                continue                            # we care about conditional jumps only
          

            # as in __reg_w(), we only care about simple conditional jumps: "<reg> <op> <const>"
            if len(action.condition.variables) == 1:  
                try:
                    self.cond['op'] = {             # cast operator
                        '__eq__' : '==',
                        '__ne__' : '!=',
                        '__le__' : '<=',
                        '__lt__' : '<',
                        '__ge__' : '>=',
                        '__gt__' : '>',

                        'SGT'    : '>',                        
                        'SGE'    : '>=',
                        'SLT'    : '<',
                        'SLE'    : '<=',                        
                        'UGT'    : '>',             # do not distinguish signed/unsigned operators
                        'UGE'    : '>=',
                        'ULT'    : '<',
                        'ULE'    : '<=',
                    }[ action.condition.op ]
                except KeyError: 
                    warn('Unknown conditional jump operator "%s"' % action.condition.op)
                    self.cond = { }
                    return

                
                node = [leaf for leaf in action.condition.recursive_leaf_asts]


                # -----------------------------------------------------------------------
                # Check if we're in the simple form: <reg> <op> <const>
                # -----------------------------------------------------------------------
                if len(node) == 2:                  # we need 2 leaves + 1 operator
                    self.cond['form'] = 'simple'    # we're in the simple form

                    try:
                        # swap register and constant if needed
                        if node[1].op == 'BVS' and node[0].op == 'BVV' and node[0].concrete:
                            node[0], node[1] = node[1], node[0]


                        # if we're in the right form (reg and const), we have our condition
                        if node[0].op == 'BVS' and node[1].op == 'BVV' and node[1].concrete:
                            self.cond['reg']   = self.__symreg[node[0]]
                            self.cond['const'] = state.se.eval(node[1])
                        else:
                            self.cond = { }         # not in the right form
                            return

                    except KeyError:                    
                        # if not in the right form, __symreg() will throw a KeyError exception
                        self.cond = { }
                        return


                # -----------------------------------------------------------------------
                # Check if we're in the extended form: (<reg> <op> <const>) <op> <const>
                # (example: "<SAO <Bool (rbx_1_64 + 0x1) == 0x8>>")
                # 
                # This is when the iterator (register) gets modified and compared at the
                # same basic block.
                # -----------------------------------------------------------------------
                elif len(node) == 3:                # we need 3 leaves and 2 operators
                    self.cond['form'] = 'extended'  # we're in the extended form

                    try:
                        # get left and right side of the comparison
                        left, right = action.condition.split( action.condition.op )

                        # if the constant is on the left side, swap sides
                        if left.op == 'BVV' and left.concrete:
                            left, right = right, left


                        mod_ops = {                 # register modification operations
                            '__add__'    : '+',
                            '__sub__'    : '-',
                            '__mul__'    : '*',
                            '__div__'    : '/',
                            '__and__'    : '&',
                            '__or__'     : '|',
                            '__xor__'    : '^',
                            '__invert__' : '~',
                            '__lshift__' : '<<',
                            '__rshift__' : '>>'
                        }

                        
                        # if the left side is a modification and the right side a constant
                        if left.op in mod_ops and right.op == 'BVV' and right.concrete:
                            self.cond['const']  = state.se.eval(right)
                            self.cond['mod_op'] = mod_ops[ left.op ]

                            reg, const = left.split( left.op )

                            # if the constant is on the left side, swap sides
                            if reg.op == 'BVV' and reg.concrete:
                                reg, const = const, reg

                            # if the modification uses a constant and a register
                            if reg.op   == 'BVS' and reg in self.__symreg and \
                               const.op == 'BVV' and const.concrete:
                                    self.cond['reg']       = self.__symreg[reg]
                                    self.cond['mod_const'] = state.se.eval(const)
                            else:
                                self.cond = { }     # something is not in the right form
                                return    
                        else:
                            self.cond = { }
                            return    
                                    
                    except ValueError:              # != 2 values to split()
                        self.cond = { }
                        return


                # -----------------------------------------------------------------------
                # Otherwise we're not in the right form
                # -----------------------------------------------------------------------
                else:
                    self.cond = { }
                    continue


                # The problem here, is that simgr sometimes "inverts" the condition, so the 
                # "target" basic block is the block immediately after the current block. To 
                # be consistent, we have to "invert" the operator, so the target basic block
                # is executed when the jump is taken.
                blk = self.__proj.factory.block(self.__entry) 

                # check if the target is the next block (assume action.target is concrete)
                if state.se.eval(action.target) == blk.addr + blk.size:
                    self.cond['op'] = {                 # invert the condition
                        '==' : '!=',
                        '!=' : '==',
                        '>'  : '<=',
                        '>=' : '<',
                        '<'  : '>=',
                        '<=' : '>'
                    }[ self.cond['op'] ]  

            break                                   # there's up to 1 conditional jump



    # ---------------------------------------------------------------------------------------------
    # __add_sym_vars(): This function extracts all (memory) symbolic variables from an expression.
    #       For instance, given the expression: <BV64 mem_7fffffffffef1e8_82_64 + 0x68>, we want to
    #       map the variable 'mem_7fffffffffef1e8_82_64' to its actual address: 0x7fffffffffef1e8.
    #
    # :Arg addr_expr: The address expression to get variables from
    # :Ret: None.
    #
    def __add_sym_vars( self, addr_expr ):
        # A memory symbolic variable is in the form: mem_ADDRESS_RANDOM_SIZE. The AST leaf
        # will be like this: "<BV64 mem_7ffffffffff13e8_4928_64{UNINITIALIZED}>"
        #
        # We want to extract the ADDRESS and SIZE fields
        for leaf in addr_expr.recursive_leaf_asts:  # for each leaf in the AST
            leafstr = leaf.shallow_repr()           # cast it to sting

            # if leaf is a memory variable, extract its address and its size
            if re.search(r'mem_[0-9a-f]+_[0-9]+_[0-9]+', leafstr):
                _, addr, rand, size = leafstr.split('_')

                # size might be followed by the "{UNINITIALIZED}" keyword, so it must be dropped
                # if not the ">" must also be dropped
                size = size.replace("{UNINITIALIZED}>", "").replace(">", "")

                # add the symbolic variable to the map
                self.symvars[ leaf ] = (int(addr, 16), int(size, 10) >> 3)



    # ---------------------------------------------------------------------------------------------
    # __memread_callback(): This function is invoked every time that a memory read operation is 
    #       performed.
    #
    # :Arg state: Current state to read memory from
    # :Ret: None.
    #
    def __memread_callback( self, state ):
        if self.__callback_mutex == 1:              # if mutex is taken, return
            return
        
        self.__callback_mutex = 1                   # get lock

        # ---------------------------------------------------------------------
        # If address is part of the .bss/.data, it will be initialized with a
        # default value of 0. However, it can get any value (due to AWP) so it
        # should get a symbolic value.
        # ---------------------------------------------------------------------
        # get ELF sections that give default values to their uninitialized variables
        bss  = self.__proj.loader.main_object.sections_map[".bss"]
        data = self.__proj.loader.main_object.sections_map[".data"]

        addr = state.se.eval(state.inspect.mem_read_address)
        # print '=== READ', hex(state.inspect.instruction), hex(addr)

        # check if address is inside .bss or .data sections
        if bss.min_addr  <= addr and addr <= bss.max_addr or \
           data.min_addr <= addr and addr <= data.max_addr:
                # This is also works, but is for Big Endian:
                #       state.memory.make_symbolic('mem', state.inspect.mem_read_address, length)

                # make address symbolic
                symv = state.se.BVS("mem_%x" % addr, state.inspect.mem_read_length << 3)
                
                state.memory.store(state.inspect.mem_read_address, symv, 
                                        state.inspect.mem_read_length, endness=archinfo.Endness.LE)

                # we should read it to update state.inspect.mem_read_expr
                state.memory.load(state.inspect.mem_read_address,
                                        state.inspect.mem_read_length, endness=archinfo.Endness.LE)


        # -------------------------------------------------------------------------------
        # Identifying dereferences is a two stage process. Here (1st step) we capture all
        # memory load information (which happens before the register write) that happen 
        # at this instruction (x64 has 1 distinct memory read per insruction; however 
        # instructions like popad do multiple register writes, but this is not an issue 
        # here).
        # -------------------------------------------------------------------------------
        self.__load[ state.inspect.instruction ] = (
                state.inspect.mem_read_address, 
                state.inspect.mem_read_length, 
                state.inspect.mem_read_expr         # this will be updated
        )

        # associate memory expression with memory address (needed for later on)
        self.__mem2addr[ state.inspect.mem_read_expr.shallow_repr() ] = \
                                (state.inspect.mem_read_address, state.inspect.mem_read_length)
      
        # extract memory symbolic variables
        self.__add_sym_vars( state.inspect.mem_read_address )    

        self.__callback_mutex = 0                   # release lock

   

    # ---------------------------------------------------------------------------------------------
    # __regwrite_callback(): This function is invoked every time that a register write operation
    #       is performed.
    #
    # :Arg state: Current state to write register to
    # :Ret: None.
    #
    def __regwrite_callback( self, state ):
        if self.__callback_mutex == 1:              # if mutex is taken, return
            return

        self.__callback_mutex = 1                   # get lock
        
        try:
            # get register that is being written
            reg = self.__proj.arch.register_names[state.inspect.reg_write_offset]
        except KeyError:                            # just in case
            return


        # TODO: Regwrite only checks writes, but it doesn't check if the previous value perists after
        #       .text:000000000040BCEA         mov     eax, [rbp+ac]
        #       .text:000000000040BCF0         cdqe
        #       .text:000000000040BCF2         shl     rax, 3
        #       .text:000000000040BCF6         mov     rcx, rax
        #       .text:000000000040BCF9         add     rcx, [rbp+nargv]
        # 
        # ('sudo' example)
        #
        # We should add some checks to test whether the regwrite is "mov" or something else


        # print '--------------- ', hex(state.addr), hex(state.inspect.instruction), reg, 
        #                           state.inspect.reg_write_expr


        # remember the "raw" value that is being written to the register
        self.__reg_rawval[ reg ] = state.inspect.reg_write_expr

        if reg not in HARDWARE_REGISTERS:           # we only care about specific registers
            self.__callback_mutex = 0               # release lock
            return        


        # -------------------------------------------------------------------------------
        # This is the 2nd step of the dereference identification process. At this point 
        # we match the instruction that writes a register with the instruction that read
        # from memory. This is because we want to match the memory read expression with
        # the register write.
        # -------------------------------------------------------------------------------
        elif state.inspect.instruction in self.__load:
            addr, length, _ = self.__load[ state.inspect.instruction ]


            # ok we have a dereference!
            deps   = [ ]                            # dependent registers
            symtab = { }

            # find register dependencies on the address (e.g., rsi on <BV64 rsi_44_64 + 0x18>)
            for sym, nam in self.__symreg.iteritems():
                # skip registers that are not symbolic (e.g., rbp)
                if isinstance(sym.args[0], str) and sym.args[0] in addr.shallow_repr():
                    deps.append(nam)
                    symtab[nam] = sym


            # there might be dependencies with constant memory addresses as well (i.e., reading
            # from global variables). Such dependencies are handled during trace searching, so 
            # we ignore them for now. However the register dependencies are needed to check
            # whether a register mapping is valid or not.


            # if "deps" has a single element, we know that a register is containted in "addr"
            # expression. If also that expression has a single node, we know that this will be
            # that register.
            if len(deps) == 1 and len([leaf for leaf in addr.recursive_leaf_asts]) == 1:
                memrd = length
            else:
                memrd = None

            
            # (if basic block has >1 dereferences on the same register, use the most recent one)
            self.regwr[ reg ] = {                   # set data
                'type'  : 'deref',
                'addr'  : addr,
                'deps'  : deps,
                'sym'   : symtab,
                'memrd' : memrd
            }


        # -------------------------------------------------------------------------------
        # The current approach for detecting dereferences is not transitive. Consider the
        # following example:
        #       mov rcx, [rsi + 0x10]
        #       mov rdi, rcx
        #
        # In the 2nd register write, rdi gets an unconstrained symbolic variable (e.g., 
        # <SAO <BV64 Reverse(symbolic_read_unconstrained_17_64)>>) and therefore it's of
        # type 'clob'. However, we want rdi to be treated in the same way with rcx, as
        # they both have the exact same value. Because SE engine gives a unique symbolic
        # variable on every memory cell, we can associate them with their addresses. 
        # Thus, when a register gets a random symbolic value, we can figure out whether
        # it is actually a dereference.
        # -------------------------------------------------------------------------------
        elif state.inspect.reg_write_expr.shallow_repr() in self.__mem2addr:
            addr, length = self.__mem2addr[ state.inspect.reg_write_expr.shallow_repr() ]

            # this code is copy-pasta from above
            deps    = [ ]
            symtab  = { }

            for sym, nam in self.__symreg.iteritems():
                if isinstance(sym.args[0], str) and sym.args[0] in addr.shallow_repr():
                    deps.append(nam)
                    symtab[nam] = sym


            if len(deps) == 1 and len([leaf for leaf in addr.recursive_leaf_asts]) == 1:
                memrd = length
            else:
                memrd = None


            self.regwr[ reg ] = {
                'type'  : 'deref',
                'addr'  : addr,
                'deps'  : deps,
                'sym'   : symtab,
                'memrd' : memrd
            }
            

        # -------------------------------------------------------------------------------

        self.__callback_mutex = 0                   # release lock



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
            raise Exception("Alarm triggered after %d seconds" % ABSBLK_TIMEOUT)
            raise Exception("Alarm triggered after %d seconds" % ABSBLK_TIMEOUT)
            raise Exception("Alarm triggered after %d seconds" % ABSBLK_TIMEOUT)
            raise Exception("Alarm triggered after %d seconds" % ABSBLK_TIMEOUT)



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor. This function initializes the environment for the symbolic
    #       execution, it executes the basic block, and performs the abstraction.
    #
    # :Arg project: Instance of angr project
    # :Arg addr: Entry point of the basic block
    # :Ret: None.
    #
    def __init__( self, project, addr ):
        self.__proj  = project                      # we'll need these
        self.__entry = addr

        
        # ---------------------------------------------------------------------
        # initialize abstraction variables
        # ---------------------------------------------------------------------
        self.regwr      = { }                       # all register writes for that block
        self.memrd      = set()                     # all memory reads for that block
        self.memwr      = set()                     # all memory writes for that block
        self.conwr      = set()                     # all concrete memory writes for that block
        self.splmemwr   = [ ]                       # all memory register writes for that block
        self.call       = { }                       # function/system call (if any) for that block
        self.cond       = { }                       # conditional jumps (if any) for that block
        self.symvars    = { }                       # symbolic variables for memory
        self.__load     = { }                       # memory loads (for internal use)
        self.__mem2addr = { }                       # map between memory expressions and addresses

        self.__mem = { }
        self.__reg_rawval = { }

        # ---------------------------------------------------------------------
        # Create a blank state and prepare it for symbolic execution.
        #
        # TODO: Check options again
        # ---------------------------------------------------------------------
        inist = self.__proj.factory.blank_state(    # create a blank state
            addr=addr,                              # set address
            #mode='symbolic', 
            add_options={                           # configure options
                simuvex.o.AVOID_MULTIVALUED_READS,
                simuvex.o.AVOID_MULTIVALUED_WRITES,
                simuvex.o.NO_SYMBOLIC_JUMP_RESOLUTION,
                simuvex.o.CGC_NO_SYMBOLIC_RECEIVE_LENGTH,
                simuvex.o.NO_SYMBOLIC_SYSCALL_RESOLUTION,
                simuvex.o.TRACK_ACTION_HISTORY,
                
                # newly added option
                simuvex.o.SYMBOLIC_INITIAL_VALUES
            },
            remove_options=simuvex.o.resilience_options | simuvex.o.simplification           
        )

        # configure more options (add/remove)
        inist.options.discard(simuvex.o.CGC_ZERO_FILL_UNCONSTRAINED_MEMORY)
        inist.options.update( {
            simuvex.o.TRACK_REGISTER_ACTIONS,
            simuvex.o.TRACK_MEMORY_ACTIONS,
            simuvex.o.TRACK_JMP_ACTIONS,
            simuvex.o.TRACK_CONSTRAINT_ACTIONS }
        )

      
        # ---------------------------------------------------------------------
        # initialize all registers with a symbolic variable
        # ---------------------------------------------------------------------
        inist.regs.rax = inist.se.BVS("rax", 64)    # give convenient names
        inist.regs.rbx = inist.se.BVS("rbx", 64)
        inist.regs.rcx = inist.se.BVS("rcx", 64)
        inist.regs.rdx = inist.se.BVS("rdx", 64)
        inist.regs.rsi = inist.se.BVS("rsi", 64)
        inist.regs.rdi = inist.se.BVS("rdi", 64)


        # rbp may also needed as it's mostly used to access local variables (e.g., 
        # rax = [rbp-0x40]) but some binaries don't use rbp and all references are
        # rsp related. In these cases it may worth to use rbp as well.
        if MAKE_RBP_SYMBOLIC:
            inist.regs.rbp = inist.se.BVS("rbp",64) # keep rbp symbolic
        else:
            inist.registers.store('rbp', FRAMEPTR_BASE_ADDR, size=8, endness=archinfo.Endness.LE)
        
        # rsp must be concrete and properly initialized
        inist.registers.store('rsp', RSP_BASE_ADDR, size=8, endness=archinfo.Endness.LE)

        inist.regs.r8  = inist.se.BVS("r08", 64)
        inist.regs.r9  = inist.se.BVS("r09", 64)
        inist.regs.r10 = inist.se.BVS("r10", 64)
        inist.regs.r11 = inist.se.BVS("r11", 64)
        inist.regs.r12 = inist.se.BVS("r12", 64)
        inist.regs.r13 = inist.se.BVS("r13", 64)
        inist.regs.r14 = inist.se.BVS("r14", 64)
        inist.regs.r15 = inist.se.BVS("r15", 64)


        # ---------------------------------------------------------------------
        # Other initializations
        # ---------------------------------------------------------------------        
        # map symbolic names to registers

        # self.__symreg = { self.__getreg(inist, r):r for r in HARDWARE_REGISTERS }
        self.__symreg = { 
            inist.regs.rax : 'rax',
            inist.regs.rbx : 'rbx',
            inist.regs.rcx : 'rcx',
            inist.regs.rdx : 'rdx',
            inist.regs.rsi : 'rsi',
            inist.regs.rdi : 'rdi',
            inist.regs.rbp : 'rbp',
            inist.regs.rsp : 'rsp',
            inist.regs.r8  : 'r8',
            inist.regs.r9  : 'r9',
            inist.regs.r10 : 'r10',
            inist.regs.r11 : 'r11',
            inist.regs.r12 : 'r12',
            inist.regs.r13 : 'r13',
            inist.regs.r14 : 'r14',
            inist.regs.r15 : 'r15'
        }


        # UPDATE: Don't create a symbolic stack, as this consumes all the Virtual Memory and
        # may crash the machine. By carefully configuring rsp and rbp within the limit of virtual
        # page limit, we can achieve the same effect, so we don't need a symbolic stack.
        #
        # The main issue here are the permissions (stack may not appear as R+W), but as long as
        # both rsp and rbp point in the same page, there is no problem.
        #
        #
        #       # create a symbolic stack (required to have writable pages)
        #       stack = inist.se.BVS("stack", self.__proj.arch.bits * _STACK_SZ)     
        #
        #       # write symbolic stack to memory  
        #       # inist.memory.store(inist.regs.sp, stack, endness=archinfo.Endness.LE)                    
        #       inist.memory.store(STACK_BASE_ADDR, stack, endness=archinfo.Endness.LE)

        # when solver gives up (in milliseconds)
        inist.se._solver.timeout = ABSBLK_TIMEOUT*1000


        # ---------------------------------------------------------------------
        # Hooks for identifying dereferences
        # ---------------------------------------------------------------------
        self.__callback_mutex = 0                   # hooks are enabled

        inist.inspect.b('reg_write', when=angr.BP_BEFORE, action=self.__regwrite_callback)
        inist.inspect.b('mem_read',  when=angr.BP_AFTER,  action=self.__memread_callback)
        
        
        # -------------------------------------------------------------------------
        # Do the symbolic execution (using simulation managers)
        # ------------------------------------------------------------------------- 
        simgr = self.__proj.factory.simulation_manager(thing=inist)
        simgr.save_unconstrained = True             # do not discard unconstrained stashes


        signal.signal(signal.SIGALRM, self.__sig_handler)
        signal.alarm(ABSBLK_TIMEOUT)                  


        # make sure that you execute the normalized block
        # TODO: cleanup
        node = ADDR2NODE[self.__entry]
        num_inst = len(node.instruction_addrs) if node is not None else None
        if num_inst:
           simgr.step(num_inst=num_inst)
        
        else:
            simgr.step()                            # execute 1 basic block
    
        signal.alarm(0)                             # disable alarm


        if simgr.active:                            # check if execution was successful
            newst = simgr.active[0]                 # get the new state (after execution)

        elif simgr.unconstrained:
            # because we execute a single basic block, it's possible to end up in an state that
            # instruction pointer depends on symbolic data and hence to not know how to proceed
            # (i.e., unconstrained stash)
            newst = simgr.unconstrained[0]

        elif simgr.deadended:                       # check if execution can't continue (retq)
            newst = simgr.deadended[0]              # work with what you have
           
        else:                                       # everything else should generate an error
            print simgr.stashes
            raise Exception('There are no usable stashes!')


        # -------------------------------------------------------------------------
        # Analyze results and generate the abstractions
        # ------------------------------------------------------------------------- 
        self.__reg_w(newst)                         # analyze register writes
        self.__mem_r(newst)                         # analyze memory reads
        self.__mem_w(newst)                         # analyze memory writes
        self.__call(newst)                          # analyze function/system calls
        self.__cond(newst)                          # analyze conditional jumps


        # -------------------------------------------------------------------------
        # Apply (any) patches
        #
        # Instructions like 'rep movsq' incorrectly classify rsi and rdi in 'deref'
        # types. This is because angr assigns a basic block with a single rep* 
        # instruction (as VEX IR contains loops). To fix that, we simply mark the
        # used registers as clobbering.
        # ------------------------------------------------------------------------- 
        blk_insns = node.block.capstone.insns       # get block instructions

        if len(blk_insns) == 1 and 'rep' in blk_insns[0].insn.mnemonic:
            # name = blk_insns[0].insn.insn_name()    # get instruction name (w/o the rep*)
              
            # make 'rsi', 'rdi' and 'rcx' clobbering (all of them are modified)
            self.regwr['rdi'] = {'type' : 'clob'}    
            self.regwr['rsi'] = {'type' : 'clob'}
            self.regwr['rcx'] = {'type' : 'clob'}            


        '''
        print
        print '-------------------- Register Writes --------------------'                   
        for a, b in self.regwr.iteritems():
            print a, b

        print '-------------------- Memory Reads --------------------'            
        for a, b in self.memrd:
            print a, b

        print '-------------------- Memory Writes --------------------'            
        for a, b in self.memwr:
            print a, b

        print '-------------------- Concrete Writes --------------------'            
        for a, b in self.conwr:
            print a, b

        print '-------------------- SPL Memory Writes --------------------'            
        for a in self.splmemwr:
            print a

        print '-------------------- Calls --------------------'            
        print self.call

        print '-------------------- Conditional Jumps --------------------'            
        print self.cond
        '''



    # ---------------------------------------------------------------------------------------------
    # __getitem__(): An alternative way to get block "abstractions".  
    #
    # :Arg what: The name of the abstraction that you want to get
    # :Ret: The requested abstraction.
    # 
    def __getitem__( self, what ):
        try:
            return {
                'regwr'    : self.regwr,
                'memrd'    : self.memrd,
                'memwr'    : self.memwr,
                'conwr'    : self.conwr,
                'splmemwr' : self.splmemwr,
                'call'     : self.call,
                'cond'     : self.cond,
                'symvars'  : self.symvars
            }[ what ]
        except KeyError:
            return None                             # abstraction not found



    # ---------------------------------------------------------------------------------------------
    # __iter__(): Iterate over all abstractions. This function is a generator over all possible
    #       abstractions.
    #
    # :Ret: Each time function returns a different tuple (name, abstraction).
    # 
    def __iter__( self ):   
        yield 'regwr',    self.regwr
        yield 'memrd',    self.memrd
        yield 'memwr',    self.memwr
        yield 'conwr',    self.conwr
        yield 'splmemwr', self.splmemwr
        yield 'call',     self.call
        yield 'cond',     self.cond
        yield 'symvars',  self.symvars 



# -------------------------------------------------------------------------------------------------
'''
if __name__ == '__main__':                          # DEBUG ONLY
    import angr

    project = angr.Project('eval/opensshd/sshd', load_options={'auto_load_libs': False})    
    # project.analyses.CFGFast()                    # to prepare project.kb.functions

    # Problem: Inidirect pointers in .bss:
    #   .text:00000000004050B1         mov     rax, cs:public_key
    #   .text:00000000004050B8         mov     rdi, [rax+20h]          ; value
    #
    # abstr = abstract_ng(project, 0x4050B1)

    # abstr = abstract_ng(project, 0x416610)
    abstr = abstract_ng(project, 0x416631)

    # TODO: check me again!
    abstr = abstract_ng(project, 0x0x40c01f)

    for a, b in abstr:
        print '\t', a, b

    print 'done!'
'''
# -------------------------------------------------------------------------------------------------

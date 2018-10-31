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
# compile.py:
#
# This module compiles an program written in SPL into an equivalent Intermediate Representation
# (IR) suitable for processing by subsequent modules. Please do not confuse it with the VEX IR.
#
# SPL is actually a subset of C, so it has the same syntax. Comments are denoted with '//'. Multi
# line comments are not supported.The specs of the language (expressed in EBNF) are shown below:
#
#       <SPL>    := 'void' 'payload' '(' ')' '{' <stmts> '}'
#       <stmts>  := ( <stmt> | <label> )* <return>?
#       <stmt>   := <varset> | <regset> | <regmod> | <memrd> | <memwr> | <call> | <cond> | <jump>
#
#       <varset> := 'int' <var> '=' <rvalue> ';'
#                 | 'int' <var> '=' '{'  <rvalue> (',' <rvalue>)* ';'
#                 | 'string' <var> '=' <str> ';'
#       <regset> := <reg> '=' <rvalue> ';'
#       <regmod> := <reg> <asgop> <number> ';'
#       <memrd>  := <reg> '=' '*' <reg> ';'
#       <memwr>  := '*' <reg> '=' <reg> ';'
#       <call>   := <var> '(' (e | <reg> (',' <reg>)*) ')'
#       <label>  := <var> ':'
#       <cond>   := 'if' '(' <reg> <cmpop> <number> ')' 'goto' <var> ';'
#       <jump>   := 'goto' <var> ';'
#       <return> := 'return' <number> ';'
#
#       <reg>    := '__r' <regid>
#       <regid>  := [0-7]
#       <var>    := [a-zA-Z_][a-zA-Z_0-9]*
#       <number> := ('+' | '-') [0-9]+ | '0x' [0-9a-fA-F]+
#       <rvalue> := <number> | '&' <var>
#       <str>    := '"' [.]* '"'
#       <asgop>  := '+=' | '-=' | '*=' | '/=' | '&=' | '|=' | '~=' | '^=' | '>>=' | '<<='
#       <cmpop>  := '==' | '!=' | '>' | '>=' | '<' | '<='
#
#
# Here's how the IR looks like:
#
#   {'uid': 2, 'type': 'regset', 'reg': 0, 'valty': 'num', 'val': -10}
#   {'uid': 6, 'type': 'varset', 'name': 'test', 'val': ['a1']}
#   {'uid': 10,'type': 'varset', 'name': 'bar',
#                           'val': ['\xd2\x04\x00\x00\x00\x00\x00\x00', ('foo',), ('test',)]}
#   {'uid': 12, 'type': 'regset', 'reg': 6, 'valty': 'var', 'val': ('bar',)}
#   {'uid': 18, 'type': 'regmod', 'reg': 6, 'op': '+', 'val': 17712}
#   {'uid': 6,  'type': 'memrd', 'reg': 0, 'mem': 1}
#   {'uid': 8,  'type': 'memwr', 'mem': 0, 'val': 1}
#   {'uid': 20, 'type': 'label'}
#   {'uid': 24, 'type': 'call', 'name': 'execve', 'args': [0, 1, 6], 'dirty': ['rax', 'rcx', 'rdx']}
#   {'uid': 30, 'type': 'cond', 'reg': 0, 'op': '==' 'num': 11, 'target': '@__26'}
#   {'uid': 32, 'type': 'jump', 'target': '@__20'}
#   {'uid': 34, 'type': 'return', 'target': 0xdead}
#
# NOTE: The compiler is implemented using regular expressions, and not using flex/bison, as it's
#   too simple. So, be careful about the language syntax, as very small differences (that may not
#   affect other languages) can result in syntax errors.
#
#
# * * * ---===== TODO list =====--- * * *
#
#   [1]. Consider the control flow of the SPL program upon "Semantic check #4".
#
# -------------------------------------------------------------------------------------------------
from coreutils import *
from calls     import *

import struct
import shlex
import re



# ------------------------------------------------------------------------------------------------
# Constant Definitions
# ------------------------------------------------------------------------------------------------
N_VIRTUAL_REGISTERS = 8                             # number of virtual registers

STATE_IDLE          = 0                             # program is in idle state
STATE_START         = 1                             # state after we encounter !PROGRAM START
STATE_END           = 2                             # state after we encounter !PROGRAM END

# tokens come in tuples (symbol, lineno). To make code easier to read, don't use 0 and 1 to
# access them, but instead use T and L
T = 0
L = 1

# Instead of incrementing pc and uid by one, we can increment them by two (or by larger intervals).
# This has to do with optimization. If we want to "inject" a new statement, we can do that without
# modifying the pc/uid of the other statements.
_STEP_UP = 2                                        # 2 is ok for current optimizer


# WARNING: Don't try to use modulo operator ;)
asg_ops = ['+=', '-=', '*=', '/=', '&=', '|=', '^=', '~=', '>>=', '<<=']
cmp_ops = ['==', '!=', '>',  '>=', '<',  '<=']


# The regular expressions to match various tokens
_reg_    = r'^__r[0-7]$'
_var_    = r'^[a-zA-Z_][a-zA-Z_0-9]*$'
_number_ = r'^(((\+|\-)?[0-9]+)|(0x[0-9a-fA-F]+))$'
_rvalue_ = r'^(((\+|\-)?[0-9]+)|(0x[0-9a-fA-F]+)|(\&[a-zA-Z_][a-zA-Z_0-9]*))$'
_asgop_  = r'^\+=|\-=|\*=|\/=|\&=|\|=|\^=|\~=|\>\>=|\<\<=$'
_cmpop_  = r'^\=\=|\!\=|\>|\>\=|\<|\<\=$'




# -------------------------------------------------------------------------------------------------
# compile: This is the main class that compiles an SPL program into its equivalent IR form.
#
class compile( object ):
    ''' ======================================================================================= '''
    '''                                   INTERNAL VARIABLES                                    '''
    ''' ======================================================================================= '''
    __prog          = ''                            # program's file name
    __state         = STATE_IDLE                    # program's state
    __lineno        = 1                             # current line number for parsing
    __pc            = START_PC                      # program counter (initialized)
    __uid           = 0                             # IR unique identifier
    __label_dict    = { }                           # label lookup
    __vartab        = { }                           # variable table
    __ir            = [ ]                           # intermediate list


    ''' ======================================================================================= '''
    '''                                   AUXILIARY FUNCTIONS                                   '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __syn_err(): A syntax error is fatal. Print a verbose explanation and halt execution.
    #
    # :Arg err: Error to display
    # :Ret: None.
    #
    def __syn_err( self, err, lineno ):
        fatal("%s:%d : Syntax Error: %s" % (self.__prog, lineno, err))



    # ---------------------------------------------------------------------------------------------
    # __sem_err(): A semantic error is fatal as well. Print a verbose explanation and halt
    #       execution.
    #
    # :Arg err: Error to display
    # :Ret: None.
    #
    def __sem_err( self, err ):
        fatal("%s : Semantic Error: %s" % (self.__prog, err))



    # ---------------------------------------------------------------------------------------------
    # __sem_warn(): A semantic warning isn't fatal, but it's still important. Print a verbose
    #       explanation and continue execution.
    #
    # :Arg err: Error to display
    # :Ret: None.
    #
    def __sem_warn( self, msg ):
        warn("%s : Semantic Warning: %s" % (self.__prog, msg))



    # ---------------------------------------------------------------------------------------------
    # __multi_re(): Extend regular expression matching to lists. Instead of applying 1 regex in a
    #       single string, __multi_re() applies a list of regexes in a list of strings. A list of
    #       errors is also supplied in case that a regex fails.
    #
    # :Arg stmt: List of statements to match
    # :Arg regex: List of regular expressions for statements
    # :Arg err: List of errors in case of a mismatch
    # :Ret: None.
    #
    def __multi_re( self, stmt, regex, err ):
        stmt, lno = zip(*stmt)

        if len(stmt) != len(regex):                 # check if parameters match
            self.__syn_err( "Invalid number of parameters", lno[0] )

        for i in range(len(stmt)):                  # for each string in list
            try:
                if not re.match(regex[i], stmt[i]): # apply regex
                    self.__syn_err("%s '%s'" % (err[i], stmt[i]), lno[i])
            except IndexError: pass



    # ---------------------------------------------------------------------------------------------
    # __ir_add(): Add a "compiled" statement to IR.
    #
    # :Arg tup: A tuple containing the statement
    # :Ret: None.
    #
    def __ir_add( self, tup ):
        # extend statement and add it to IR (along with its pc)
        self.__ir.append( ['@__' + str(self.__pc), dict([('uid',self.__uid)] + tup.items())] )

        # __pc and __uid are equal for now, but they're going be different after optimization.
        self.__pc  = self.__pc  + _STEP_UP          # increase program counter
        self.__uid = self.__uid + _STEP_UP          # assign a unique id to each statement



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     SYNTAX ANALYSIS                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __check_prog_state(): A decorator function (== hook) that is called before every statement
    #       parsing and verifies that all statements are inside payload() declaration.
    #
    # :Arg func: Function to invoke from decorator
    # :Ret: Decorator function.
    #
    def __check_prog_state( func ):
        def stmt_intrl( self, stmt ):
            dbg_prnt(DBG_LVL_3, "Parsing statement: " + ' '.join(zip(*stmt)[0]))

            if self.__state != STATE_START:
                self.__syn_err("Statement outside of !PROGRAM directives")

            func(self, stmt)                        # invoke the appropriate statement function

        return stmt_intrl                           # return decorator



    # ---------------------------------------------------------------------------------------------
    # __stmt_program(): A payload declaration has been encountered.
    #
    # :Arg stmt: Statement to process
    # :Ret: None.
    #
    def __stmt_program( self, stmt ):
        if self.__state == STATE_IDLE:
            # we haven't declare payload() yet. Make sure that declaration is "void payload() {"
            if len(stmt) != 5:
                self.__syn_err("Invalid number of aaa operands", stmt[0][L])

            self.__multi_re(stmt,
                [r'^void$', r'^payload$', r'^\($', r'^\)$', r'^\{$'],
                ["Invalid function declaration"]*5
            )

            self.__state = STATE_START              # change state

            # A pseudo-statement to avoid corner cases (needed for building the delta graph)
            self.__ir_add( {'type':'entry'} )


        elif self.__state == STATE_START:
            # we're looking to close payload() declaration ("}")
            if len(stmt) != 1:
                self.__syn_err("Code outside of function!", stmt[1][L])

            self.__multi_re(stmt, [r'^}$'],["Unknown"] )

            self.__state = STATE_END                # change state


        else:
            self.__syn_err("Invalid program state")



    # ---------------------------------------------------------------------------------------------
    # __stmt_var(): A variable assignment has been encountered.
    #
    # :Arg stmt: Statement to process
    # :Ret: None.
    #
    @__check_prog_state
    def __stmt_var( self, stmt ):
        # stmt[0] has already been checked. Some checks are redundant here, but we do them to keep
        # functions autonomous.

        # ---------------------------------------------------------------------
        if re.search(r'^string$', stmt[0][T]):
            # start with the easy one
            self.__multi_re( stmt[1:],
                [_var_, r'^=$', r'^".*"$',],
                ["Invalid variable name", "Expected '=', but found", "Invalid assigned value"]
            )

            val = [stmt[3][T][1:-1].decode('string_escape')]

        # ---------------------------------------------------------------------
        elif re.search(r'^int$', stmt[0][T]):
            self.__multi_re( stmt[1:3],
                [_var_, r'^=$'],
                ["Invalid variable name", "Expected '=', but found"]
            )

            try:
                if re.search(_rvalue_, stmt[3][T]): # single R-value

                    if stmt[3][T][0] == '&':
                        val = [(stmt[3][T][1:],)]
                    else:
                        val = [struct.pack('<Q', int(stmt[3][T], 0))]

                else:                               # array of R-values
                    val = []

                    self.__multi_re( [stmt[3]] + [stmt[4]] + [stmt[-1]],
                        [r'^\{$', _rvalue_, r'^\}$'],
                        ["Expected '{', but found", "Invalid R-value", "Expected '}', but found"]
                    )

                    if stmt[4][T][0] == '&':
                        val.append( (stmt[4][T][1:],) )
                    else:
                        val.append(struct.pack('<Q', int(stmt[4][T], 0)))

                    # parse all R-values
                    for i in range(5, len(stmt)-1, 2):
                        self.__multi_re( [stmt[i]] + [stmt[i+1]],
                            [r'^,$', _rvalue_],
                            ["Expected ',', but found", "Invalid R-value" ]
                        )

                        if stmt[i+1][T][0] == '&':
                            val.append( (stmt[i+1][T][1:],) )
                        else:
                            val.append(struct.pack('<Q', int(stmt[i+1][T], 0)))

            except IndexError:
                self.__syn_err("Invalid number of arguments", stmt[0][L])

        # ---------------------------------------------------------------------
        else:
            self.__syn_err("Invalid type", stmt[0][L])


        # ---------------------------------------------------------------------
        # This is a semantic check, but it's better to do it here
        # ---------------------------------------------------------------------
        if stmt[1][T] in self.__vartab:             # check if variable has already been declared
            self.__sem_err("Redeclaration of '%s'" % stmt[1][T])

        self.__vartab[ stmt[1][T] ] = val           # if not, add variable to vartab

        # add statement to IR
        self.__ir_add( {'type':'varset', 'name':stmt[1][T], 'val':val} )



    # ---------------------------------------------------------------------------------------------
    # __stmt_reg(): A register assignment/modification or a memory read has been encountered.
    #
    # :Arg stmt: Statement to process
    # :Ret: None.
    #
    @__check_prog_state
    def __stmt_reg( self, stmt ):
        self.__multi_re( [stmt[0]], [_reg_], ["Invalid register name"])


        # ---------------------------------------------------------------------
        # Memory read
        # ---------------------------------------------------------------------
        if re.search(r'^=$', stmt[1][T]) and re.search(r'^\*$', stmt[2][T]) and len(stmt) == 4:
            self.__multi_re( [stmt[3]], [_reg_], ["Invalid R-value"])

            self.__ir_add({'type':'memrd', 'reg':int(stmt[0][T][3],0), 'mem':int(stmt[3][T][3],0)})


        # ---------------------------------------------------------------------
        # Register assignment
        # ---------------------------------------------------------------------
        elif re.search(r'^=$', stmt[1][T]) and len(stmt) == 3:
            self.__multi_re( [stmt[2]], [_rvalue_], ["Invalid R-value"])

            if stmt[2][T][0] == '&':
                self.__ir_add( {'type'  : 'regset',
                                'reg'   : int(stmt[0][T][3]),
                                'valty' : 'var',
                                'val'   : (stmt[2][T][1:],)} )

            else:
                self.__ir_add( {'type'  : 'regset',
                                'reg'   : int(stmt[0][T][3]),
                                'valty' : 'num',
                                'val'   : int(stmt[2][T], 0)} )


        # ---------------------------------------------------------------------
        # Register modification
        # ---------------------------------------------------------------------
        elif re.search(_asgop_, stmt[1][T]) and len(stmt) == 3:
            self.__multi_re( [stmt[2]], [_number_], ["Invalid number"])


            self.__ir_add( {'type': 'regmod',
                            'reg' : int(stmt[0][T][3]),
                            'op'  : stmt[1][T][:-1],
                            'val' : int(stmt[2][T], 0)} )

        # ---------------------------------------------------------------------
        # Unknown register operation
        # ---------------------------------------------------------------------
        else:
            self.__syn_err("Unknown operator '%s'" % stmt[1][T], stmt[1][L])



    # ---------------------------------------------------------------------------------------------
    # __stmt_memwr(): An memory write statement has been encountered.
    #
    # :Arg stmt: Statement to process
    # :Ret: None.
    #
    @__check_prog_state
    def __stmt_memwr( self, stmt ):
        self.__multi_re( stmt,
            [r'^\*$', _reg_, r'^=$', _reg_],
            ["Expected '*', but found", "Invalid register name", "Expected '=', but found",
             "Invalid register name"]
        )

        self.__ir_add( {'type':'memwr', 'mem':int(stmt[1][T][3],0), 'val':int(stmt[3][T][3],0)} )



    # ---------------------------------------------------------------------------------------------
    # __stmt_call(). A library/system call has been encountered.
    #
    # :Arg stmt: Statement to process
    # :Ret: None.
    #
    @__check_prog_state
    def __stmt_call( self, stmt ):
        call = find_call(stmt[0][T])

        if not call:
            self.__syn_err( "Function '%s' is not supported" % stmt[0][T], stmt[0][L] )

        # this check is redundant
        self.__multi_re( [stmt[1]] + [stmt[-1]],
            [r'^\($', r'^\)$'],
            ["Expected '(', but found", "Expected ')', but found"]
        )

        args = []
        if len(stmt) - 3 > 0:
            for i in range(2, len(stmt)-1, 2):
                self.__multi_re( [stmt[i]] + [stmt[i+1]],
                    [_reg_, r'^,$' if len(stmt)-2 > i+1 else r'^\)$'],
                    ["Invalid register name", "Unexpected symbol"]
                )

                args.append( int(stmt[i][T][3]) )


        # both syscalls and libcalls have the same calling convention (in x64) so we're good ;)
        # we don't need to distinguish them

        # check if call has the right number of arguments (for non-variadic ones)
        if len(args) != call[1] and call[1] != INFINITY:
            self.__syn_err( "Function '%s' has an invalid number of arguments" %
                    stmt[0][T], stmt[0][L] )

        # check max number of registers (arguments) in calling convention
        maxlen = len(SYSCALL_CC) if find_syscall(stmt[0][T]) else len(LIBCALL_CC)

        if len(args) > maxlen:
           self.__syn_err("SPL supports functions with up to %d arguments" % maxlen, stmt[0][L])


        self.__ir_add( {'type':'call', 'name':stmt[0][T], 'args':args, 'dirty':call[2], 'alt':[]} )



    # ---------------------------------------------------------------------------------------------
    # __stmt_label(): A label has been encountered.
    #
    # :Arg stmt: Statement to process
    # :Ret: None.
    #
    @__check_prog_state
    def __stmt_label( self, stmt ):
        # check if label is in correct form
        self.__multi_re( stmt, [_var_], ["Invalid label name"] )

        # give a UID to that label
        # Our semantic analysis states that "every label must be followed by a statement". So we
        # set the UID to be equal with the UID of the next statement. This is because labels
        # are pseudo-statements (they're not part of the IR) and we want the jump target to be
        # at the statement after it.
        #
        # (self.__pc points to the current statement, so +_STEP_UP will point to the next)
        self.__label_dict[ stmt[0][T] ] = '@__' + str(self.__pc + _STEP_UP)

        # add a dummy label (needed for slicing during optimization)
        self.__ir_add( {'type':'label'} )



    # ---------------------------------------------------------------------------------------------
    # __stmt_cond(): An conditional jump statement has been encountered.
    #
    # :Arg stmt: Statement to process
    # :Ret: None.
    #
    @__check_prog_state
    def __stmt_cond( self, stmt ):
        self.__multi_re( stmt,
            [r'^if$', r'^\($', _reg_, _cmpop_, _number_, r'^\)$', r'^goto$', _var_],
            ["Expected 'if', but found",
             "Expected '(', but found",
             "Expected register, but found",
             "Invalid comparison operator",
             "Invalid number",
             "Expected ')', but found",
             "Expected 'goto', but found",
             "Invalid goto target"]
        )

        # When an conditional jump branches to a label that hasn't been declared yet, we add a
        # temporary jump target. After parsing is done, __label_dict will contain all labels,
        # so we can go back and fix missing target.
        self.__ir_add( {'type'   : 'cond',
                        'reg'    : int(stmt[2][T][3]),
                        'op'     : stmt[3][T],
                        'num'    : int(stmt[4][T], 0),
                        'target' : stmt[7][T]} )



    # ---------------------------------------------------------------------------------------------
    # __stmt_jump(): An jump statement (goto) has been encountered.
    #
    # :Arg stmt: Statement to process
    # :Ret: None.
    #
    @__check_prog_state
    def __stmt_jump( self, stmt ):
        self.__multi_re( stmt,
            [r'^goto$', _var_],
            ["Expected 'goto', but found", "Invalid goto target"]
        )

        self.__ir_add( {'type':'jump', 'target':stmt[1][T]} )



    # ---------------------------------------------------------------------------------------------
    # __stmt_return(): An return statement has been encountered.
    #
    # :Arg stmt: Statement to process
    # :Ret: None.
    #
    @__check_prog_state
    def __stmt_return( self, stmt ):
        self.__multi_re( stmt,
            [r'^return$', _number_],
            ["Expected 'return', but found", "Invalid return address"]
        )

        self.__ir_add( {'type':'return', 'target':int(stmt[1][T],0)} )



    # ---------------------------------------------------------------------------------------------
    # __do_syntax_parsing(): This is where syntax analysis starts. Function takes as input the SPL
    #       program (expressed as a list of tokens) and checks whether it follows the EBNF.
    #
    # :Arg tokens: A list of all tokens from the SPL program
    # :Ret: None. If a syntax error occurs, an exception will be raised.
    #
    def __do_syntax_parsing( self, tokens ):

        # -------------------------------------------------------------------------------
        # Merge tokens into statements
        # -------------------------------------------------------------------------------
        stmts, stmt = [], []

        for symbol, lineno in tokens:               # for each token
            if symbol != ';' and symbol != ':':     # not a statement delimiter?

                # if a memory read/write is used, make sure that '*' operator is separated
                if re.search(r'^\*__r.*$', symbol):                     
                    stmt.append( ('*', lineno) )
                    stmt.append( (symbol[1:], lineno) )
                else:
                    stmt.append( (symbol, lineno) ) # append it to the current statement

            else:                                   # statement delimiter
                stmts.append(stmt)                  # append statement to the statements list
                stmt = []                           # clear current statement

        if stmt: stmts.append(stmt)                 # push any leftovers to the list


        # The 1st statement should be the function declaration: "void payload() {". However it
        # also contains the 2nd statement (up to the first delimiter). Split this statement.
        stmt = stmts.pop(0)                         # get 1st statement

        if len(stmt) < 5:                           # not the expected size?
            self.__syn_err("Invalid function declaration", stmt[0][L])

        stmts = [stmt[:5], stmt[5:]] + stmts        # split it and push it back


        # -------------------------------------------------------------------------------
        # To keep the code simple, each statement is parsed in its own function. Here,
        # we quickly identify the type of statement and we invoke the right function to
        # further process it.
        # -------------------------------------------------------------------------------
        for stmt in stmts:                          # for each statement
            # function declaration starts with 'void' and ends with '}':
            #   [('void', 1), ('payload', 1), ('(', 1), (')', 1), ('{', 1)]
            #   [('}',10)]
            if re.search(r'^void$', stmt[0][T]) or re.search(r'^}$', stmt[0][T]):
                self.__stmt_program(stmt)

            # Variable assignments start with 'int' or 'string':
            #   [('int', 2), ('a', 2), ('=', 2), ('0x10', 2)]
            elif re.search(r'^int|string$', stmt[0][T]):
                self.__stmt_var(stmt)

            # Register assignments/modifications and memory reads start with '__r':
            #   [('__r0', 4), ('=', 4), ('1', 4)]
            elif re.search(r'^__r.*', stmt[0][T]):
                self.__stmt_reg(stmt)


            # Memory writes start with '*':            
            #  [('*', 14), ('__r1', 14), ('=', 14), ('__r0', 14)]
            elif re.search(r'^\*', stmt[0][T]):
                self.__stmt_memwr(stmt)

            # Labels consist of a single token:
            #   [('LABEL', 5)]
            elif len(stmt) == 1:
                self.__stmt_label(stmt)

            # Calls have a '(' as 2nd token and a ')' as last token:
            #   [('func', 6), ('(', 6), ('__r0', 6), (',', 6), ('__r1', 6), (',', 6), (')', 6)]
            #
            # (we already know that len(stmt) > 1, so we can access stmt[1])
            elif re.search(r'^\($', stmt[1][T]) and re.search(r'^\)$', stmt[-1][T]):
                self.__stmt_call(stmt)

            # Conditional statements start with 'if':
            #   [('if', 7), ('(', 7), ('__r0', 7), ('>', 7), ('=', 7), ('0x0', 7), (')', 7),
            #    ('goto', 7), ('LABEL', 7)]
            elif re.search(r'^if$', stmt[0][T]):
                self.__stmt_cond(stmt)

            # Jump statements start with 'goto':
            #   [('goto', 8), ('LABEL', 8)]
            elif re.search(r'^goto$', stmt[0][T]):
                self.__stmt_jump(stmt)

            # Returns statements start with 'return':
            #   [('return', 9), ('0x4006fe', 9)]
            elif re.search(r'^return$', stmt[0][T]):
                self.__stmt_return(stmt)

            # Othewise we have a syntax error...
            else:
                self.__syn_err("Unknown keyword '%s'" % stmt[0][T], stmt[0][L])



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                    SEMANTIC ANALYSIS                                    '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __fix_jump_targets(): Fix target labels (replace names with pc) for conditional jumps.
    #
    # :Ret: None.
    #
    def __fix_jump_targets( self ):
        dbg_prnt(DBG_LVL_2, "Fixing jump/goto targets...")

        for _, stmt in self.__ir:                   # for each jump statement
            if stmt['type'] == 'cond' or stmt['type'] == 'jump':
                try:
                    # find pc that label belongs to
                    stmt['target'] = self.__label_dict[ stmt['target'] ]
                except KeyError:
                     self.__sem_err("Label '%s' is not declared" % stmt['target'])

        dbg_prnt(DBG_LVL_2, "Done.")



    # ---------------------------------------------------------------------------------------------
    # __do_semantic_checks(): Perform a basic semantic analysis. This function performs a series
    #       of some semantic checks that IR has to pass.
    #
    # :Ret: None. If a semantic error occurs, an exception will be raised.
    #
    def __do_semantic_checks( self ):
        dbg_prnt(DBG_LVL_2, "Semantic analysis started.")


        # --------------------------------=[ CHECK #1 ]=---------------------------------
        # -----------------=[ "A variable can be declared only once" ]=------------------
        #
        # This check is already done in __stmt_var() as it's way easier to do it there.


        # --------------------------------=[ CHECK #2 ]=---------------------------------
        # ----------=[ "An return must be the last statement of the program" ]=----------
        nret = len([s for _, s in self.__ir if s['type'] == 'return'])

        if nret > 1 or nret == 1 and self.__ir[-1][1]['type'] != 'return':
            self.__sem_err("Only one return is allowed and only at the end of the program")


        # --------------------------------=[ CHECK #3 ]=---------------------------------
        # --------------------=[ "A statement must follow a label" ]=--------------------
        #
        # A tricky check. First we check whether the last statement is _not_ a label. Then, we get
        # all statements (we only care about statement type -VARSET, etc) that follow a label
        # (there's always a next statement after a label, because the last statement is not label)
        # and check whether there are labels there.
        #
        if self.__ir[-1][1]['type'] == 'label' or \
           'label' in [self.__ir[i+1][1]['type'] for i, (_, s) in enumerate(self.__ir) \
           if s['type'] == 'label']:
                self.__sem_err("A label must be followed by a statement (labels are not statements)")


        # --------------------------------=[ CHECK #4 ]=---------------------------------
        # -------=[ "A variable/register must be assigned before it gets used" ]=--------
        #
        # Here we "simulate" the IR. When we encounter an assignment, we mark this variable/
        # register. When we use a variable/register, we check if it's marked. Note that this
        # check does not consider the control flow of the program (e.g. conditional jumps and
        # goto).
        #
        tvar, treg = { }, { }                       # temp variable and register tables

        for _, stmt in self.__ir:                   # for each statement (linear sweep)
            
            # -----------------------------------------------------------------
            if stmt['type'] == 'varset':
                for val in stmt['val']:
                    if isinstance(val, tuple):
                        if val[0] in tvar:
                            tvar[ val[0] ] = 1      # mark variable
                        else:
                            self.__sem_err("Variable '%s' referenced before assignment" % val[0])

                # add this after isinstance() check to catch cases like $c := [$c]
                # mark variable (if it's set for 2nd time don't make it 0)
                tvar[ stmt['name'] ] = tvar.get(stmt['name'], 0) * 1

            
            # -----------------------------------------------------------------
            elif stmt['type'] == 'regset':
                if isinstance(stmt['val'], tuple):  # reference of another variable?
                    if stmt['val'][0] in tvar:
                        tvar[ stmt['val'][0] ] = 1  # mark variable
                    else:
                        self.__sem_err("Variable '%s' referenced before assignment" % stmt['val'][0])


                treg[ stmt['reg'] ] = treg.get(stmt['reg'], 0) * 1

            
            # -----------------------------------------------------------------
            elif stmt['type'] == 'regmod':
                if stmt['reg'] in treg:
                    treg[ stmt['reg'] ] = 1
                else:
                    self.__sem_err("Register '__r%d' referenced before assignment" % stmt['reg'])
                   
           
            # -----------------------------------------------------------------
            elif stmt['type'] == 'memrd':
                if stmt['mem'] in treg:
                    treg[ stmt['mem'] ] = 1
                else:
                    self.__sem_err("Register '__r%d' referenced before assignment" % stmt['mem'])

                # mark register being set
                treg[ stmt['reg'] ] = treg.get(stmt['reg'], 0) * 1

                
            # -----------------------------------------------------------------
            elif stmt['type'] == 'memwr':
                if stmt['mem'] in treg:
                    treg[ stmt['mem'] ] = 1
                else:
                    self.__sem_err("Register '__r%d' referenced before assignment" % stmt['mem'])

                if stmt['val'] in treg:
                     treg[ stmt['val'] ] = 1
                else:
                    self.__sem_err("Register '__r%d' referenced before assignment" % stmt['val'])


            # -----------------------------------------------------------------
            elif stmt['type'] == 'cond':
                if stmt['reg'] in treg:
                    treg[ stmt['reg'] ] = 1
                else:
                    self.__sem_err("Register '__r%d' referenced before assignment" % stmt['reg'])


            # -----------------------------------------------------------------
            elif stmt['type'] == 'call':
                for arg in stmt['args']:
                    if arg in treg:
                        treg[ arg ] = 1

                    else:
                        self.__sem_err("Register '__r%d' referenced before assignment" % arg)


        # --------------------------------=[ CHECK #5 ]=---------------------------------
        # -------------------=[ "A variable/register must be used" ]=--------------------
        #
        # Here we check if there are any registers/variables that are unused. This is actually
        # gets calculated on the previous check. If a variable/register is used, the treg/tvar
        # it will be 1. Otherwise it's 0. Note that this is a soft error. Execution doesn't
        # halt when checks fails.
        #        
        for reg, used in treg.iteritems():
            if not used:
               self.__sem_warn("Register '__r%d' is unused" % reg)

        for var, used in tvar.iteritems():
            if not used:
                self.__sem_warn("Variable '%s' is unused" % var)

        del treg
        del tvar


        # -----------------------------=[ OPTIONAL CHECKs ]=-----------------------------
        # There are other checks that we could do as well:
        #   [1]. A label must be referenced
        #   [2]. A variable must be declared only once
        #   ...
        #

        dbg_prnt(DBG_LVL_2, "Semantic analysis completed.")



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                 MISCELLANEOUS FUNCTIONS                                 '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # _calc_stats(): Collect some statistics regarding generated IR.
    #
    # :Ret: None.
    #
    def _calc_stats( self ):
        # nreal: the number of real statement (those that need a candidate block)
        self.nreal = 0

        for stmt in self:                           # for each statement
            if stmt['type'] not in ['entry', 'varset', 'label', 'jump', 'return']:
                self.nreal += 1

        # nregs contains the number of distinct virtual registers. This is calculated as follows:
        # It iterates over all statements and gets all registers in 'regset' statements (thanks
        # to our semantic analysis, it's not allowed for a 'regmod' to use a register that hasn't
        # been used in a previous 'regset'; thus we only care about 'regset'). Then in counts the
        # distinct registers by transforming the list into a set.
        self.nregs = len( set([s['reg'] for s in self if s['type'] in ['regset', 'memrd']]) )

        # the number of distinct variables. The processing is identical to nregs
        self.nvars = len( set([s['name'] for s in self if s['type'] == 'varset']) )

        # the number of distinct variables that their references are assigned to registers
        self.nregvars = len( set([s['val'][0] for s in self
                                    if s['type'] == 'regset' and isinstance(s['val'], tuple)]) )

        # the number of "free" variables. Free variables are not assigned to any register, so
        # they can be placed at any memory address (due to the AWP)
        self.nfreevars = self.nvars - self.nregvars



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor.
    #
    # :Arg filename: The SPL source file name
    #
    def __init__( self, filename ):
        self.__prog = filename                      # program's file name is all we need



    # ---------------------------------------------------------------------------------------------
    # __getitem__(): Get i-th statement from IR. Out-of-order statements are groups in the same
    #       list entry, so we cannot find them in O(1) without some auxiliary data struct. For
    #       now we simply do a linear search.
    #
    # :Arg idx: Index of the IR statement
    # :Ret: The requested IR statement
    # 
    def __getitem__( self, idx ):
        assert( idx >= 0 )                          # bound checks

        for _, stmt in self.__ir:                   # for each IR statement list
            # each list has a single element here
            if stmt[0]['uid'] == idx: return stmt   # if index found return statement

        raise IndexError("No statement with uid = %d found" % idx )



    # ---------------------------------------------------------------------------------------------
    # __len__(): Get the number of IR statements.
    #
    # :Ret: Each time function returns a different statement.
    #
    def __len__( self ):
        return len(self.__ir)



    # ---------------------------------------------------------------------------------------------
    # __iter__(): Iterate over all statements. This function is a generator over all statements
    #       (no matter if they are out-of-order or not).
    #
    # :Ret: Each time function returns a different statement.
    #
    def __iter__( self ):
        for _, stmt_r in self.__ir:                 # for each IR statement list
            for stmt in stmt_r:                     # for each "parallel" statement
                yield stmt                          # return next statement



    # ---------------------------------------------------------------------------------------------
    # compile(): Compile the source file into its Intermediate Representation (IR). Make sure that
    #       the file follows the syntax of and the semantics of the SPL.
    #
    # :Ret: None. If an error occurs, program will terminate.
    #
    def compile( self ):
        dbg_prnt(DBG_LVL_1, "Compiling '%s'..." % self.__prog)
        dbg_prnt(DBG_LVL_2, "Parsing started.")

        tokens = []                                 # place all tokens here

        try: 
            with open(self.__prog, "r") as file:    # open source file
                # -----------------------------------------------------------------------
                # Do the lexical analysis here
                # -----------------------------------------------------------------------
                for line in file:                   # process it line by line
                    # drop all comments "//" from current line (be careful though to not
                    # drop "comments" that are inside quotes)
                    line = re.sub("(?!\B\"[^\"]*)\/\/(?![^\"]*\"\B).*\n", '', line)


                    # tokenize line and append it to the token list
                    lexical = shlex.shlex(line)     # create a lexical analysis object

                    # TODO: this is not recognized as comment: //string s2 = "/this";

                    #  lexical.commenters = '//'    # alternative way to drop comments
                    lexical.wordchars += ''.join(set(''.join(asg_ops + cmp_ops) + '+-&'))

                    symbols = [token for token in lexical]
                    if symbols:                     # if there are any tokens

                        # tokens are tuples (symbol, line number)
                        tokens += zip(symbols, [self.__lineno]*len(symbols))

                    self.__lineno = self.__lineno+1 # update line counter

        except IOError:
            fatal("File '%s' not found" % self.__prog)



        self.__do_syntax_parsing(tokens)            # do the syntax analysis

        dbg_prnt(DBG_LVL_2, "Parsing complete.")

        # ===-----
        # At this point, program has a valid syntax. We move on the semantic analysis
        # ===-----

        self.__fix_jump_targets()                   # fix goto branches (label => pc)
        self.__do_semantic_checks()                 # do the semantic checks


        # at this point each statement is the form: [pc, stmt]. This form is not suitable for
        # out of order statements, as we want them in the form: [pc, [stmt1, stmt2, ...]]. This
        # the job of the optimizer, but for now we have to prepare IR accordingly, so we convert
        # each statement into the form: [pc, [stmt]].
        for s in self.__ir: s[1] = [s[1]]

        self._calc_stats()                          # get IR statistics

        dbg_prnt(DBG_LVL_1, "Compilation completed.")



    # ---------------------------------------------------------------------------------------------
    # get_ir(): Return the compiled IR.
    #
    # :Ret: The IR.
    #
    def get_ir( self ):
        return self.__ir



# -------------------------------------------------------------------------------------------------

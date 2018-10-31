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
# output.py:
#
# This module deal with the representation of the solution.
#
#
# * * * ---===== TODO list =====--- * * *
#
# [1]. Support the other formats (right now only 'gdb' is supported). To do that, make all 
#      functions dispatchers, that invoke internal ones (e.g., register() will use self.__format to
#      choose between __gdb_register(), __idc_register() or __raw_register()).
#
# -------------------------------------------------------------------------------------------------
from coreutils import *
import time



# -------------------------------------------------------------------------------------------------
# output: This class transforms the solution into the appropriate format and dumps it into a file.
#
class output( object ):
    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor. 
    #
    # :Arg format: The format to use
    #
    def __init__( self, fmt ):
        self.__format = fmt                         # current formate
        self.__output = ''                          # the final output string


        # check if format is valid
        if self.__format not in ['raw', 'gdb', 'idc']:
            fatal("Unknown format '%s'" % self.__format)
        
        if self.__format != 'gdb':
            fatal("Format '%s' is not implemented" % self.__format)



    # ---------------------------------------------------------------------------------------------
    # comment(): Add a comment to the output file.
    #
    # :Arg comment: Comment to add
    # :Ret: None.
    # 
    def comment( self, comment ):
        self.__output += '# %s\n' % comment



    # ---------------------------------------------------------------------------------------------
    # newline(): Simply add a blank newline.
    #
    # :Ret: None.
    # 
    def newline( self ):
        self.__output += '\n'



    # ---------------------------------------------------------------------------------------------
    # breakpoint(): Add a breakpoint to the output file.
    #
    # :Arg address: Address of the breakpoint
    # :Ret: None.
    # 
    def breakpoint( self, address ):
        self.__output += 'break *0x%x\n' % address



    # ---------------------------------------------------------------------------------------------
    # register(): Set a register.
    #
    # :Arg register: Register to set
    # :Arg value: Value to write (8 bytes)
    # :Ret: None.
    # 
    def register( self, register, value, comment='' ):        
        self.__output += 'set $%s = %s' % (register, value)

        if comment: 
            self.__output += '\t# ' + comment

        self.__output += '\n'



    # ---------------------------------------------------------------------------------------------
    # memory(): Write to memory.
    #
    # :Arg address: Address to write
    # :Arg value: Value that is being written
    # :Arg size: Size of the value
    # :Ret: None.
    # 
    def memory( self, address, value, size ):
        if size == 8 and value[0] != '{':
            cast = '(long long int)'
        else:
            cast = ''

        self.__output += 'set {char[%d]} (%s) = %s %s\n' % (size, address, cast, value)        



    # ---------------------------------------------------------------------------------------------
    # external(): External input (from socked, file, etc.)
    #
    # :Arg line: -
    # :Ret: None.
    # 
    def external( self, line ):
        fatal('output.external() is not implemented yet')



    # ---------------------------------------------------------------------------------------------
    # alloc(): Allocate some contigouous memory (pool).
    #
    # :Arg varname: Pool name
    # :Arg size: Pool size
    # :Ret: None.
    # 
    def alloc( self, varname, size ):
        self.__output += 'set %s = malloc(%d)\n' % (varname, size)



    # ---------------------------------------------------------------------------------------------
    # set(): Set a variable.
    #
    # :Arg name: Variable name
    # :Arg value: Variable's desired value
    # :Ret: None.
    # 
    def set( self, name, value ):
        self.__output += 'set %s = %s \n' % (name, value)



    # ---------------------------------------------------------------------------------------------
    # save(): Save the current output to a file.
    #
    # :Arg binary: Binary file name
    # :Ret: None.
    # 
    def save( self, binary ):
        now    = datetime.datetime.now()            # get current timestamp
        banner = textwrap.dedent("""\
            #
            # This file has been created by BOPC at: %s
            # 
        """ % now.strftime("%d/%m/%Y %H:%M"))       # create a banner


        # make sure that file has a unique name, as we can have >1 solutions
        filename = '%s_%x.%s' % (binary, time.time(), self.__format)

        try:    
            out = open(filename, 'w')               # create file

            out.write(banner)                       # write banner first
            out.write(self.__output)                # then output
            out.close()
           
            dbg_prnt(DBG_LVL_1, "Solution has saved as '%s'" % bolds(filename))
            dbg_prnt(DBG_LVL_2, "Solution file:\n%s" % banner + self.__output)


            dbg_prnt(DBG_LVL_2, "Waiting for a second to prevent solutions with the same timestamp...")
            time.sleep(1)                           # prevent solutions with the same filename
            
        except IOError, err:
            error("Cannot create output file: %s" % str(err))



# -------------------------------------------------------------------------------------------------

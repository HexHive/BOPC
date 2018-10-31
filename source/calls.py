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
# calls.py
#
# This module contains all declarations for system and library calls that SPL supports. A call is
# declared as a tuple (name, nargs, modregs):
#
#       name    : The library/system call name
#       nargs   : The number of its arguments. Set to INFINITY for variadic functions.
#       modregs : A list of all registers that are modified when the call returns. Note that rax 
#                 is always modified as it has the return value.
#
# To keep the implementation simple, We do not support library calls that take arguments on the
# stack.
#
# Also, it is possible to declare any custom calls that reside in the binary.
# -------------------------------------------------------------------------------------------------
from coreutils import *



# -------------------------------------------------------------------------------------------------
# Calling Conventions
# -------------------------------------------------------------------------------------------------
SYSCALL_CC = ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9']
LIBCALL_CC = ['rdi', 'rsi', 'rdx', 'r10', 'r8', 'r9']



# -------------------------------------------------------------------------------------------------
# Supported system calls
# -------------------------------------------------------------------------------------------------
syscalls__ = [
    # ssize_t read(int fd, void *buf, size_t count)
    ('read',    3,  ['rax', 'rcx', 'r10', 'r11']),

    # ssize_t write(int fd, const void *buf, size_t count)
    ('write',   3,  ['rax', 'rcx', 'r10', 'r11']),

    # void *sbrk(intptr_t increment)
    ('sbrk',    1,  ['rax', 'rcx', 'rdx', 'r10', 'r11']),

    # int brk(void *addr)
    ('brk',     1,  ['rax', 'rcx', 'rdx', 'r10', 'r11']),

    # int dup(int oldfd)
    ('dup',     1,  ['rax', 'rcx', 'r11']),

    # int dup2(int oldfd, int newfd)
    ('dup2',    2,  ['rax', 'rcx', 'r10', 'r11']),

    # unsigned int alarm(unsigned int seconds)
    ('alarm',   1,  ['rax', 'rcx', 'r10', 'r11']),


    '''
        Feel free to append more syscalls...
    '''
]



# -------------------------------------------------------------------------------------------------
# Supported library calls
# -------------------------------------------------------------------------------------------------
libcalls__ = [
    # int system(const char *command)
    ('system',  1,  ['rax', 'rcx', 'rdx', 'rdi', 'rsi', 'r8', 'r9', 'r10', 'r11']),

    # int puts(const char *s)
    ('puts',    1,  ['rax', 'rcx', 'rdx', 'rdi', 'rsi', 'r8', 'r9', 'r10', 'r11']),

    # int execve(const char *filename, char *const argv[], char *const envp[])
    ('execve',  3,  ['rax', 'rcx', 'rdx', 'r10', 'r11']),

    # int execv(const char *filename, char *const argv[])
    ('execv',   2,  ['rax', 'rcx', 'rdx', 'r10', 'r11']),
    
    # int execl(const char *path, const char *arg, ...);
    ('execl',   2,  ['rax', 'rcx', 'rdx', 'r10', 'r11']),

    # int printf(const char *format, ...)
    ('printf',  INFINITY,  ['rax', 'rcx', 'rdx', 'rsi', 'rdi',  'r8', 'r10', 'r11']),

    # ssize_t send(int sockfd, const void *buf, size_t len, int flags);
    # (we can ignore the 4th parameter for now)
    ('send',    3,  []),

    # void exit(int status)
    ('exit',    1,  []),


    '''
        Feel free to append more libcalls...
    '''
]



# -------------------------------------------------------------------------------------------------
# In case that you don't want to distinguish them
# -------------------------------------------------------------------------------------------------
calls__ = syscalls__ + libcalls__



# -------------------------------------------------------------------------------------------------
# Groups of function calls that have similar effects
# -------------------------------------------------------------------------------------------------
call_groups__ = [
    ['puts',   'printf'],
    ['execve', 'execv', 'execl' ],
]



# -------------------------------------------------------------------------------------------------
# find_syscall(): Search for a specific system call.
#
# :Arg name: Name of the syscall
# :Ret: If system call exists, function returns the associated entry in syscalls__. Otherwise None
#       is returned.
#
def find_syscall( name ):
    call = filter(lambda call: call[0] == name, syscalls__)

    if len(call) == 0:
        return None

    elif len(call) == 1:
        return call[0]

    else:
        raise Exception("System call '%s' has >1 entries in syscalls__ table." % name)



# -------------------------------------------------------------------------------------------------
# find_libcall(): Search for a specific library call.
#
# :Arg name: Name of the library call
# :Ret: If library call exists, function returns the associated entry in libcalls__. Otherwise None
#       is returned.
#
def find_libcall( name ):
    call = filter(lambda call: call[0] == name, libcalls__)

    if len(call) == 0:
        return None

    elif len(call) == 1:
        return call[0]

    else:
        raise Exception("Library call '%s' has >1 entries in libcalls__ table." % name)



# -------------------------------------------------------------------------------------------------
# find_call(): Search for a specific call (either library or system)
#
# :Arg name: Name of the call
# :Ret: If call exists, function returns the associated entry in calls__. Otherwise None is
#       returned.
#
def find_call( name ):
    sys = find_syscall(name)
    lib = find_libcall(name)

    return sys if sys else lib                      # logic OR



# -------------------------------------------------------------------------------------------------

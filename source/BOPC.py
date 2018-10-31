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
# BOPC.py:
#
#
# This is the main module of BOPC. It configures the environment and launches the other modules.
#
# -------------------------------------------------------------------------------------------------
from coreutils import *
import absblk     as A
import compile    as C
import optimize   as O
import mark       as M
import search     as S
import capability as P

import argparse
import textwrap
import ntpath
import os
import sys



# ------------------------------------------------------------------------------------------------
# Constant Definitions
# ------------------------------------------------------------------------------------------------
VERSION  = 'v2.1'                                   # current version
comments = ''                                       # Additional comments to display on startup



# -------------------------------------------------------------------------------------------------
# parse_args(): This function processes the command line arguments.
#
# :Ret: None.
#
def parse_args():
    # create the parser object and the groups
    parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)

    group_g = parser.add_argument_group('General Arguments')
    group_s = parser.add_argument_group('Search Options')
    group_c = parser.add_argument_group('Application Capability')
    group_d = parser.add_argument_group('Debugging Options')


    # -------------------------------------------------------------------------
    # Group for general arguments
    # -------------------------------------------------------------------------
    group_g.add_argument(
        '-b', "--binary",
        help     = "Binary file of the target application",
        action   = 'store',
        dest     = 'binary',
        required = False, # True
    )

    group_g.add_argument(
        '-a', "--abstractions",
        help     = "Work with abstraction file",
        choices  = ['save', 'load', 'saveonly'],
        default  = 'none',
        action   = 'store',
        dest     = 'abstractions',
        required = False
    )

    group_g.add_argument(
        "--emit-IR",
        help     = "Dump SPL IR to a file and exit",
        action   = 'store_const',
        const    = True,
        dest     = 'emit_IR',
        required = False
    )

    # action='count'
    group_g.add_argument(
        '-d',
        help     = "Set debugging level to minimum",
        action   = 'store_const',
        const    = DBG_LVL_1,
        dest     = 'dbg_lvl',
        required = False
    )

    group_g.add_argument(
        '-dd',
        help     = "Set debugging level to basic (recommended)",
        action   = 'store_const',
        const    = DBG_LVL_2,
        dest     = 'dbg_lvl',
        required = False
    )

    group_g.add_argument(
        '-ddd',
        help     = "Set debugging level to verbose (DEBUG ONLY)",
        action   = 'store_const',
        const    = DBG_LVL_3,
        dest     = 'dbg_lvl',
        required = False
    )

    group_g.add_argument(
        '-dddd',
        help     = "Set debugging level to print-everything (DEBUG ONLY)",
        action   = 'store_const',
        const    = DBG_LVL_4,
        dest     = 'dbg_lvl',
        required = False
    )

    group_g.add_argument(
        '-V', "--version",
        action   = 'version',
        version  = 'BOPC %s' % VERSION
    )


    # -------------------------------------------------------------------------
    # Group for searching arguments
    # -------------------------------------------------------------------------
    group_s.add_argument(
        '-s', "--source",
        help     = "Source file with SPL payload",
        action   = 'store',
        dest     = 'source',
        required = False
    )

    group_s.add_argument(
        '-e', "--entry",
        help     = "The entry point in the binary that payload starts",
        action   = 'store',
        dest     = 'entry',
        required = False
    )

    group_s.add_argument(
        '-O', "--optimizer",
        help     = "Use the SPL optimizer (Default: none)",
        choices  = ['none', 'ooo', 'rewrite', 'full'],
        action   = 'store',
        default  = 'none',
        dest     = 'optimizer',
        required = False
    )

    group_s.add_argument(
        '-f', "--format",
        help     = "The format of the solution (Default: raw)",
        choices  = ['raw', 'idc', 'gdb'],
        action   = 'store',
        default  = 'raw',
        dest     = 'format',
        required = False,
    )

    group_s.add_argument(
        "--find-all",
        help     = "Find all the solutions",
        action   = 'store_const',
        default  = 'one',
        const    = 'all',
        dest     = 'findall',
        required = False
    )


    # -------------------------------------------------------------------------
    # Group for debugging arguments
    # -------------------------------------------------------------------------
    group_d.add_argument(
        "--mapping-id",
        help     = "Run the Trace Searching algorithm on a given mapping ID",
        metavar  = 'ID',
        action   = 'store',
        default  = -1,
        dest     = 'mapping_id',
        required = False
    )

    group_d.add_argument(
        "--mapping",
        help     = "Run the Trace Searching algorithm on a given register mapping",
        metavar  = 'MAP',
        nargs    = '+',
        action   = 'store',
        default  = [],
        dest     = 'mapping',
        required = False
    )

    group_d.add_argument(
        "--enum-mappings",
        help     = "Enumerate all possible mappings and exit",
        action   = 'store_const',
        default  = False,
        const    = True,
        dest     = 'enum_mappings',
        required = False
    )

    group_d.add_argument(
        "--abstract-blk",
        help     = "Abstract a specific basic block and exit",
        metavar  = 'BLKADDR',
        action   = 'store',
        dest     = 'absblk',
        required = False
    )


    # -------------------------------------------------------------------------
    # Group for application capabilities
    # -------------------------------------------------------------------------
    group_c.add_argument(
        '-c', "--capability",
        help     = textwrap.dedent('''\
                    Measure application's capability. Options (can be many)

                    all\tSearch for all Statements
                    regset\tSearch for Register Assignments
                    regmod\tSearch for Register Modifications
                    memrd\tSearch for Memory Reads
                    memwr\tSearch for Memory Writes
                    call\tSearch for Function/System Calls
                    cond\tSearch for Conditional Jumps
                    load\tLoad capabilities from file
                    save\tSave capabilities to file
                    noedge\tDump statements and exit (don't calculate edges)'''),
        choices  = ['all', 'regset', 'regmod', 'memrd', 'memwr', 'call', 'cond',
                    'save', 'load', 'noedge'],
        metavar  = 'OPTIONS',
        nargs    = '+',                             # consume >=1 arguments (multiple options)
        action   = 'store',
        dest     = 'capabilities',
        required = False
    )


    if len(sys.argv) == 1:
        parser.print_help(sys.stderr)
        sys.exit(1)

    return parser.parse_args()                      # do the parsing (+ error handling)



# ---------------------------------------------------------------------------------------------
# load(): Load the target binary and generate its CFG.
#
# :Arg filename: Binary's file name
# :Ret: Function returns
#
def load( filename ):
    # load the binary (exception is thrown if name is invalid)
    project = angr.Project(filename, load_options={'auto_load_libs': False})


    # generate CFG
    dbg_prnt(DBG_LVL_0, "Generating CFG. It might take a while...")
    CFG = project.analyses.CFGFast()
    dbg_prnt(DBG_LVL_0, "CFG generated.")


    # normalize CFG (i.e. make sure that there are no overlapping basic blocks)
    dbg_prnt(DBG_LVL_0, "Normalizing CFG...")
    CFG.normalize()

    # normalize every function object as well
    for _, func in project.kb.functions.iteritems():
        if not func.normalized:
            dbg_prnt(DBG_LVL_4, "Normalizing function '%s' ..." % func.name)
            func.normalize()

    dbg_prnt(DBG_LVL_0, "Done.")


    emph("CFG has %s nodes and %s edges" %
                (bold(len(CFG.graph.nodes())), bold(len(CFG.graph.edges()))))


    # create a quick mapping between addresses and nodes (basic blocks)
    for node in CFG.graph.nodes():
        ADDR2NODE[ node.addr ] = node


    # create a quick mapping between basic block addresses and their corresponding functions
    for _, func in CFG.functions.iteritems():       # for each function
        for addr in func.block_addrs:               # for each basic block in that function
            ADDR2FUNC[ addr ] = func


    return project, CFG



# ---------------------------------------------------------------------------------------------
# abstract(): Abstract the CFG and apply any further abstraction-related operations.
#
# :Arg mark: A valid graph marking object.
# :Arg mode: Abstraction mode (load, save, saveonly, none)
# :Arg filename: Abstraction's file name (if applicable)
# :Ret: None.
#
def abstract( mark, mode, filename ):
    if mode == 'none':
        mark.abstract_cfg()                         # calculate the abstractions

    if mode == 'load':
        mark.load_abstractions(filename)            # simply load the abstractions

    elif mode == 'save':
        mark.abstract_cfg()                         # calculate the abstractions
        mark.save_abstractions(filename)            # and save them

    elif mode == 'saveonly':
        mark.abstract_cfg()
        mark.save_abstractions(filename)
        return -1

    return 0



# ---------------------------------------------------------------------------------------------
# capability_analyses(): Apply any (custom) analyses to the capabilities.
#
# :Arg cap: The capability object
# :Ret: None.
#
def capability_analyses( cap ):
    dbg_prnt(DBG_LVL_0, 'Applying additional Capability analyses...')
    return

    '''
    # analyze all islands
    # cap.analyze(P.CAP_LOOPS, P.CAP_STMT_MIN_DIST)

    # analyze a specific island
    # cap.analyze_island(0x400885, P.CAP_STMT_COMB_CTR)

    i = 0
    def foo( graph ):
        global i
        print 'Visualing island %d' % i
        cap.visualize(graph, 'island_%d' % i, show_labels=True)

        i += 1

        for _, d in graph.nodes_iter(data=True):
            print d['type'] # check capability.__add() for all keys


    # apply the callback to every island
    cap.callback( foo )
    '''


# -------------------------------------------------------------------------------------------------
# main(): This is the main function of BOPC.
#
# Ret: None.
#
if __name__ == '__main__':
    args = parse_args()                         # process arguments
    set_dbg_lvl( args.dbg_lvl )                 # set debug level in coreutils

    now  = datetime.datetime.now()              # get current time


    # -------------------------------------------------------------------------
    # Display banner
    # -------------------------------------------------------------------------
    print rainbow(textwrap.dedent('''
        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        %                                                                    %
        %                :::::::::   ::::::::  :::::::::   ::::::::          %
        %               :+:    :+: :+:    :+: :+:    :+: :+:    :+:          %
        %              +:+    +:+ +:+    +:+ +:+    +:+ +:+                  %
        %             +#++:++#+  +#+    +:+ +#++:++#+  +#+                   %
        %            +#+    +#+ +#+    +#+ +#+        +#+                    %
        %           #+#    #+# #+#    #+# #+#        #+#    #+#              %
        %          #########   ########  ###         ########                %
        %                                                                    %
        %                Block Oriented Programming Compiler                 %
        %                                                                    %
        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        '''))

    print comments
    print "[*] Starting BOPC %s at %s" % (VERSION, bolds(now.strftime("%d/%m/%Y %H:%M")))


    # -------------------------------------------------------------------------
    # BOPC operation: Emit SPL IR
    # -------------------------------------------------------------------------
    if args.emit_IR and args.source:
        IR = C.compile(args.source)
        IR.compile()                                # compile the SPL payload

        IR = O.optimize(IR.get_ir())
        IR.optimize(mode=args.optimizer)           # optimize IR (if needed)

        IR.emit(args.source)


    # -------------------------------------------------------------------------
    # BOPC operation: Trace Search
    # -------------------------------------------------------------------------
    elif args.source and args.entry:
        IR = C.compile(args.source)
        IR.compile()                                # compile the SPL payload

        IR = O.optimize(IR.get_ir())
        IR.optimize(mode=args.optimizer)           # optimize IR (if needed)


        # IR is useless; we're measuring capability
        project, CFG = load(args.binary)
        mark         = M.mark(project, CFG, IR, 'puts')

        if abstract(mark, args.abstractions, args.binary) > -1:

            entry = int(args.entry, 0)

            X = mark.mark_candidate(sorted(map(lambda s : tuple(s.split('=')), args.mapping)))

            if not X:
                print 'abort';
                exit()


        #   visualize('cfg_cand', entry=entry, options=VO_DRAW_CFG|VO_DRAW_CANDIDATE)

            # extract payload name (without the extenstion)
            payload_name = ntpath.basename(args.source)
            payload_name = os.path.splitext(payload_name)[0]


            try:
                options = {
                    'format'     : args.format,
                    'solutions'  : args.findall,
                    'mapping-id' : int(args.mapping_id),
                    'mapping'    : sorted(map(lambda s : tuple(s.split('=')), args.mapping)),
                    'filename'   : '%s-%s' % (args.binary, payload_name),
                    'enum'       : args.enum_mappings,

                    'simulate'   : False,
                    '#mappings'  : 0,
                    '#solutions' : 0
                }

            except ValueError:
                fatal("'mapping' argument must be an integer")


            tsearch = S.search(project, CFG, IR, entry, options)
            tsearch.trace_searching(mark)

            # -----------------------------------------------------------------
            # Show some statistics
            # -----------------------------------------------------------------
            emph("Trace Searching Statistics:" )
            emph("\tUsed Simulation? %s"  % bolds(options['simulate']))
            emph("\t%s Mapping(s) tried"  % bold(options['#mappings']))
            emph("\t%s Solution(s) found" % bold(options['#solutions']))


    # -------------------------------------------------------------------------
    # BOPC operation: Dump abstractions
    # -------------------------------------------------------------------------
    elif args.abstractions == 'saveonly':
        # IR is useless; we're only dumping abstractions
        project, CFG = load(args.binary)
        mark         = M.mark(project, CFG, None, 'puts')

        abstract(mark, args.abstractions, args.binary)


    # -------------------------------------------------------------------------
    # BOPC operation: Application Capability
    # -------------------------------------------------------------------------
    elif args.capabilities:
         # IR is useless; we're measuring capability
        project, CFG = load(args.binary)
        mark         = M.mark(project, CFG, None, 'puts')

        abstract(mark, args.abstractions, args.binary)

        # cfg is loaded with abstractions
        cap = P.capability(CFG, args.binary)

        options = 0

        for stmt in args.capabilities:
            options = options | {
                'all'    : P.CAP_ALL,
                'regset' : P.CAP_REGSET,
                'regmod' : P.CAP_REGMOD,
                'memrd'  : P.CAP_MEMRD,
                'memwr'  : P.CAP_MEMWR,
                'call'   : P.CAP_CALL,
                'cond'   : P.CAP_COND,
                'load'   : P.CAP_LOAD,
                'save'   : P.CAP_SAVE,
                'noedge' : P.CAP_NO_EDGE
            }[stmt]     # argparse ensures no KeyError

        cap.build(options=options)                  # build the Capability Graph
        cap.save()                                  # save nodes to a file
        cap.explore()                               # explore Islands

        capability_analyses( cap )


    # -------------------------------------------------------------------------
    # BOPC operation: Single block abstraction
    # -------------------------------------------------------------------------
    elif args.binary and args.absblk:
        project = angr.Project(args.binary, load_options={'auto_load_libs': False})

        load(args.binary)

        abstr   = A.abstract_ng(project, int(args.absblk, 0))

        dbg_prnt(DBG_LVL_0, 'Abstractions for basic block 0x%x:' % int(args.absblk, 0))
        for a, b in abstr:
            if a == 'regwr':
                dbg_prnt(DBG_LVL_0, '%14s :' % a)
                for c, d in b.iteritems():
                    dbg_prnt(DBG_LVL_0, '\t\t%s = %s' % (c, str(d)))

            else:
                dbg_prnt(DBG_LVL_0, '%14s : %s' % (a, str(b)))


    # -------------------------------------------------------------------------
    # invalid BOPC operation
    # -------------------------------------------------------------------------
    else:
        fatal('Invalid configuration argument')


    emph('')
    emph('BOPC has finished.', DBG_LVL_0)
    emph('Have a nice day!',        DBG_LVL_0)
    emph('Bye bye :)',              DBG_LVL_0)

    warn('A segmentation fault may occur now, due to an internal angr issue')



# ---------------------------------------------------------------------------------------

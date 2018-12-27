

# Block Oriented Programming Compiler (BOPC)

___


## What is BOPC

BOPC (stands for _BOP Compiler_) is a tool for automatically synthesizing arbitrary,
Turing-complete, _Data-Only_ payloads. BOPC finds execution traces in the binary that
execute the desired payload while adhering to the binary's Control Flow Graph (CFG).
This implies that the existing control flow hijacking defenses are not sufficient to
detect this style of execution, as execution does never violates the Control Flow
Integrity (CFI).

Essentially, we can say that Block Oriented Programming is _code reuse under CFI_. 

BOPC works with basic blocks (hence the name "block-oriented"). What it does is to find
a set of _functional_ blocks (i.e., blocks that perform useful computations). This step
is somewhat similar with finding Return Oriented Programming (ROP) gadgets.
Having the functional blocks, BOPC looks for _dispatcher_ blocks to that are used to
stitch functional blocks together. Compared to ROP (that we can move from one gadget
to the next without any limitation), here we can't do that as it would violate the CFI.
Instead, BOPC finds a proper sequence for dispatcher blocks that naturally lead the
execution from one functional block to the next one.
Unfortunately the problem of building _Data-Only_ payloads is NP-hard. 
However it turns out that in practice BOPC finds solution in a reasonable amount
of time.
For more details on how BOPC works, please refer to our [paper](./ccs18_paper.pdf).


To operate, BOPC requires 3 inputs:
* A target binary that has an _Arbitrary Memory Write_ (AWP) vulnerability (**hard requirement**)
* The desired payload, expressed in a high level language called SPL (stands for _SPloit Language_)
* The so-called "_entry point_", which is the first instruction in the binary that the
payload execution should start. There can be more than one entry points and determining it is
part of the vulnerability discovery process.


The output of BOPC is a set of "what-where" memory writes that indicate how the memory 
should be initialized (i.e., what values to write at which memory addresses). 
When the execution reaches the entry point and the memory is initialized according to
the output of BOPC, the target binary execute the desired payload instead of continuing
the original execution.


**Disclaimer:** This is a research project coded by a single guy. It's not a product,
so do **not** expect it to work perfectly under all scenarios. It works nicely for the
 provided test cases, but beyond that we cannot guarantee that will work as expected.

___


## Installation
Just run `setup.sh` :)

___


## How to use BOPC

BOPC started as a hacky project, so several changes made to adapt it into an scientific
context. That is, the implementation in the [paper](./ccs18_paper.pdf) is slightly
different from the actual implementation, as we omitted several implementation details
from the paper. The actual implementation overview is shown below:
![alt text](./source/images/BOPC_overview.png)



### Command line arguments explained

A good place to start are the command line arguments:

```
usage: BOPC.py [-h] [-b BINARY] [-a {save,load,saveonly}] [--emit-IR] [-d]
               [-dd] [-ddd] [-dddd] [-V] [-s SOURCE] [-e ENTRY]
               [-O {none,ooo,rewrite,full}] [-f {raw,idc,gdb}] [--find-all]
               [--mapping-id ID] [--mapping MAP [MAP ...]] [--enum-mappings]
               [--abstract-blk BLKADDR] [-c OPTIONS [OPTIONS ...]]

optional arguments:
  -h, --help            show this help message and exit

General Arguments:
  -b BINARY, --binary BINARY
                        Binary file of the target application
  -a {save,load,saveonly}, --abstractions {save,load,saveonly}
                        Work with abstraction file
  --emit-IR             Dump SPL IR to a file and exit
  -d                    Set debugging level to minimum
  -dd                   Set debugging level to basic (recommended)
  -ddd                  Set debugging level to verbose (DEBUG ONLY)
  -dddd                 Set debugging level to print-everything (DEBUG ONLY)
  -V, --version         show program's version number and exit

Search Options:
  -s SOURCE, --source SOURCE
                        Source file with SPL payload
  -e ENTRY, --entry ENTRY
                        The entry point in the binary that payload starts
  -O {none,ooo,rewrite,full}, --optimizer {none,ooo,rewrite,full}
                        Use the SPL optimizer (Default: none)
  -f {raw,idc,gdb}, --format {raw,idc,gdb}
                        The format of the solution (Default: raw)
  --find-all            Find all the solutions

Application Capability:
  -c OPTIONS [OPTIONS ...], --capability OPTIONS [OPTIONS ...]
                        Measure application's capability. Options (can be many)
                        
                        all	Search for all Statements
                        regset	Search for Register Assignments
                        regmod	Search for Register Modifications
                        memrd	Search for Memory Reads
                        memwr	Search for Memory Writes
                        call	Search for Function/System Calls
                        cond	Search for Conditional Jumps
                        load	Load capabilities from file
                        save	Save capabilities to file
                        noedge	Dump statements and exit (don't calculate edges)

Debugging Options:
  --mapping-id ID       Run the Trace Searching algorithm on a given mapping ID
  --mapping MAP [MAP ...]
                        Run the Trace Searching algorithm on a given register mapping
  --enum-mappings       Enumerate all possible mappings and exit
  --abstract-blk BLKADDR
                        Abstract a specific basic block and exit
```

Ok, there are a lot of options here (divided into 4 categories) as BOPC can do several things.

Let's start with the **General Arguments**. To avoid working directly with assembly, BOPC,
"abstracts" each basic block into a set of "actions". For more details, please check
[absblk.py](./source/absblk.py). Abstraction process symbolically executes each basic block
in the binary and carefully monitors its actions. The abstraction process can take from a few
minutes (for small binaries) to several hours (for the larger ones). Waiting that much every
time that you want to run BOPC does not sound a good idea, so BOPC uses an old trick: _caching_.

The abstraction process depends on the binary and not on the SPL payload nor the entry point,
so we only need to calculate them *once* per binary. Therefore, we have to calculate the
abstractions only one time, then save them into a file and each time loading them. 
The `save` and `saveonly` options save the abstractions into a file. The only difference is that
`saveonly` halts execution after it saves the abstractions, while `save` continues to search
for a solution. As you can guess, the `load` option loads the abstractions from a file.

The `--emit-IR` option is used to "dump" the IR representation of the SPL payload (this is
another intermediate result that you should not worry about it).

BOPC provides 5 verbosity levels: no option, `-d`, `-dd`, `-ddd` and `-dddd`. I recommend you
to use either the `-dd` or the `-ddd` to get a detailed progress status.

Let's get into the **Search Options** options. The most important arguments here are the
`--source` (which is a file that contains the SPL payload) and the `--entry` which is an
address inside the binary that indicates the entry point. Trace searching starts from the
entry point, so this is quite important.


The optimizer (`-O` option) is double edge knife. On the one hand, it optimizes the SPL
payload to make it more flexible. This means that it increases the likelihood to find a
solution. On the other hand, the search space (along with the execution time) is increased.
The decision is up to the user, hence the use of optimizer is optional. The 2 possible
optimizations are the _out of order execution_ (`ooo` option) and the _statement rewriting_
(`rewrite` option). 


The out-of-order optimization reorders payload statements.
Consider for example the following SPL payload:
```
	__r0 = 13;
	__r1 = 37;
```

To find a solution here, BOPC must find a functional block for the first statement (`__r0 = 13`)
then a functional block for the second statement (`__r1 = 37`) and a set of dispatcher blocks
to connect these two statements. However these functional blocks may be far apart so a dispatcher
may not exist. However there's no difference if you execute the `__r0 = 13` statement first
or second as it does not have any dependencies with the other statement. Thus if we rewrite
the payload as follows:
```
	__r1 = 37;
	__r0 = 13;
```

It may be possible to find another set dispatcher blocks, hopefully much smaller 
(path `A -> B` may be much longer than path `B -> A`) and find a solution.

Internally, this is a **two-step** process. First the optimizer **groups** independent
statements together (for more details take a look [here](./source/optimize.py)) and
generated and augmented SPL IR. Then, the trace search module, permutes statements
within each group, each time resulting in a different SPL payload. However all these
payloads are equivalent. As you can guess there are can be an exponential number of 
permutations, so this can take forever. To alleviate that, you can adjust
`N_OUT_OF_ORDER_ATTEMPTS` configuration parameter and tell BOPC to stop after trying 
**N** iterations, instead of trying all of them.



The statement rewriting is an under development optimization that rewrites
some statements that do not exist in the binary. For instance if the SPL payload
spawns a shell through 'execve()' but the target binary does not invoke
`execve()` at all, then BOPC fails as there are no functional blocks for that statement.
However, if the target binary invokes `execv()`, it may be possible to find a solution
by replacing `execve()` with `execv()`. The optimizer contains a list of possible replacements,
and adjust payload accordingly.


As we already explained, the output of BOPC is a set of "what-where" memory writes. There
are several ways to express the output. For instance they can be raw lines containing the
address, the value and the size of the data that should be written in memory. Or they can
be a gdb/IDA script that can run directly on the debugger and modify the memory accordingly.
The last option is the best one as it you only need to run the BOPC output into the debugger.
Currently only the `gdb` format is implemented.



The **Application Capability** options used to measure _Application's capabilities_, that
gives us upper bounds on **what** payloads the target binary is capable of executing.


Finally the **Debugging Options** assist the audit/debugging/development process. They are used
to bypass parts of the BOP work-flow. Do not use them unless you're doing changes in the code.
Recall that BOPC finds a mapping between virtual and host registers along with a mapping
between SPL variables and underlying memory addresses. If that mapping does not lead to
a solution it goes back and tries another one. If you want to focus on a specific mapping
(e.g., let's say that code crashes at mapping 458), you don't have to wait for BOPC to try
the first 457 mappings first. By supplying the `--mapping-id=458` option you can skip
all mappings and focus on that one. In case that you don't know the mapping number but you
know the actual mapping you can instead you the `--mapping` option: `--mapping=`__r0=rax __r1=rbx`



Finally, BOPC has a lot of configuration options. You see all of them in 
[config.py](./source/config.py) and adjust them according to our needs. The default
values are a nice trade off between accuracy and performance that I found during
then evaluation.


### An end to end example


```
./source/BOPC.py -dd -b $BINARY -a saveonly
```




___


## Final Notes (please read them carefully!)

* When the symbolic execution engine deals with filesystem (i.e., it has to `open` a file),
we have to provide it a valid file. Filename is defined in `SYMBOLIC_FILENAME` in 
[coreutils.py](./source/coreutils.py).

* If you want to visualize things, just uncomment the code in search.py. I'm too lazy to add
CLI flags to trigger it :P

* In case that addresses used by concolic execution do not work, adjust them from 
[simulate.py](./source/simulate.py)

* Make sure that `$rsp` is consistent in `dump()` in [simulate.py](./source/simulate.py)

* For any questions/concerns regarding the code, you can contact [ispo](https://github.com/ispoleet)

___


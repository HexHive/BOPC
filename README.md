

# Block Oriented Programming Compiler (BOPC)


___


### Installation
Just run `setup.sh` :)


### How to use BOPC

To get the abstractions:
```
./source/BOPC.py -dd -b $__binary__ -a saveonly
```

To get the capabilities:
```
./source/BOPC.py -dd -b $__binary__ -a load --capability all save

```

To dump all statements and exit:
```
./source/BOPC.py -dd -b $__binary__ -a load --capability $__stmt__ noedge

```

where `$__stmt__` is `{all, regset, regmod, memrd, memwr, call, cond}`

`-a load` loads the abstraction file. 
`-c` is the capabilities option. Check `-h` for more information.



### How to quickly find (and verify) a solution

The problem is that, there can be thousands of mappings (it's exponential based on the number
of registers and variables that are used). Each mapping can take up to a minute to test (assuming
out of order execution and other optimizations), so hexsploit may run for days or weeks.

In case that you have found a manual solution, you can ask hexsploit to quickly find too, without
trying all these mappings (that are probably won't find the desired solution).

Let's assume that you want to execute the following SPL payload:
```C
void payload() 
{ 
    string msg = "This is my random message! :)\0";

    __r0 = 0;
    __r1 = &msg;
    __r2 = 32;

    write( __r0, __r1, __r2 );

    // return 0x?? ;
}
```

Because we have a system call, we know the register mapping: `__r0 <-> rdi, __r1 <-> rsi, __r2 <-> rdx`.
Let's also assume that you have found a manual solution here:

```Assembly
.text:000000000041D0B5 loc_41D0B5:
.text:000000000041D0B5                 mov     edi, cs:scoreboard_fd ; fd
.text:000000000041D0BB                 mov     edx, 20h        ; n
.text:000000000041D0C0                 mov     esi, offset header ; buf
.text:000000000041D0C5                 call    _write
```

First, you run the abstraction on this basic block to extract the addresses:
```
time source/hexsploit.py -b eval/proftpd/proftpd -a load --abstract-blk 0x41D0B5
```

```
[22:02:07,822] [+] Abstractions for basic block 0x41d0b5:
[22:02:07,823] [+]          regwr :
[22:02:07,823] [+] 		rsp = {'writable': True, 'const': 576460752303359992L, 'type': 'concrete'}
[22:02:07,823] [+] 		rdi = {'sym': {}, 'memrd': None, 'type': 'deref', 'addr': <BV64 0x66e9e0>, 'deps': []}
[22:02:07,823] [+] 		rsi = {'writable': True, 'const': 6787008L, 'type': 'concrete'}
[22:02:07,823] [+] 		rdx = {'writable': False, 'const': 32L, 'type': 'concrete'}
[22:02:07,823] [+]          memrd : set([(<SAO <BV64 0x66e9e0>>, 32)])
[22:02:07,823] [+]          memwr : set([(<SAO <BV64 0x7ffffffffff07f8>>, <SAO <BV64 0x41d0ca>>)])
[22:02:07,823] [+]          conwr : set([(576460752303359992L, 64)])
[22:02:07,823] [+]       splmemwr : []
[22:02:07,823] [+]           call : {}
[22:02:07,823] [+]           cond : {}
[22:02:07,823] [+]        symvars : {}
[22:02:07,823] [*] 
```

Here, `__r0 <-> rdi` is loaded indirectly and the value of `__r1 <-> rsi` (which holds the `msg` 
variable) is `6787008L` or `678fc0` in hex. Then we enumerate all possible mappings (In our case
there are *287* mappinges, but there are instances that we have thousands of mappings):
```
time source/hexsploit.py -ddd -b eval/proftpd/proftpd -s payloads/print.spl -a load -e -1 --enum-mappings

```

Then we quickly search for the appropriate mapping. In our case is mapping *#89*:
```
[.... TRUNCATED FOR BREVITY ....]
[21:59:28,471] [*] Trying mapping #88:
[21:59:28,471] [*] 	Registers: __r0 <-> rdi | __r1 <-> rsi | __r2 <-> rdx
[21:59:28,471] [*] 	Variables: msg <-> *<BV64 0x7ffffffffff1440>
[21:59:28,614] [*] Trying mapping #89:
[21:59:28,614] [*] 	Registers: __r0 <-> rdi | __r1 <-> rsi | __r2 <-> rdx
[21:59:28,614] [*] 	Variables: msg <-> 0x678fc0L
[21:59:28,762] [*] Trying mapping #90:
[21:59:28,762] [*] 	Registers: __r0 <-> rdi | __r1 <-> rsi | __r2 <-> rdx
[21:59:28,762] [*] 	Variables: msg <-> *<BV64 r12_56287_64 + 0x28>
[.... TRUNCATED FOR BREVITY ....]
[22:00:04,709] [*] Trying mapping #287:
[22:00:04,709] [*] 	Registers: __r0 <-> rdi | __r1 <-> rsi | __r2 <-> rdx
[22:00:04,709] [*] 	Variables: msg <-> *<BV64 __add__(((0#32 .. rbx_294059_64[31:0]) << 0x5), r12_294068_64, 0x10)>
[22:00:04,979] [+] Trace searching algorithm finished with exit code 0
```

Now that we know the mapping, we can ask hexsploit to try only this mapping and not spend time on
the others (however it still has to iterate through them, so it may stay idle for some time):
```
time source/hexsploit.py -ddd -b eval/proftpd/proftpd -s payloads/print.spl -a load -f gdb -e 0x41D0B5 --mapping-id 89
```

We run this and 1 minute and 51 seconds, we get the solution:
```
#
# This file has been created by HexSploit at: 29/03/2018 22:04
# 
# Solution #1
# Mapping #89
# Registers: __r0 <-> rdi | __r1 <-> rsi | __r2 <-> rdx
# Variables: msg <-> 0x678fc0L
# 
# Simulated Trace: [(0, '41d0b5', '41d0b5'), (4, '41d0b5', '41d0b5'), (6, '41d0b5', '41d0b5'), (8, '41d0b5', '41d0b5'), (10, '41d0b5', '41d0b5')]
# 

break *0x403740
break *0x41d0b5

# Entry point
set $pc = 0x41d0b5 

# Allocation size is always bigger (it may not needed at all)
set $pool = malloc(20480)

# In case that rbp is not initialized
set $rbp = $rsp + 0x800 

# Stack and frame pointers aliases
set $stack = $rsp 
set $frame = $rbp 

set {char[30]} (0x678fc0) = {0x54, 0x68, 0x69, 0x73, 0x20, 0x69, 0x73, 0x20, 0x6d, 0x79, 0x20, 0x72, 0x61, 0x6e, 0x64, 0x6f, 0x6d, 0x20, 0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65, 0x21, 0x20, 0x3a, 0x29, 0x00}

set {char[8]} (0x66e9e0) = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}
```


### Notes (read them carefully!)

* When the symbolic execution engine deals with filesystem (i.e., it has to `open` a file),
we have to provide it a valid file. Filename is defined in `SYMBOLIC_FILENAME` in 
[coreutils.py](./source/coreutils.py).

* If you want to visualize things, just uncomment the code in search.py. I'm too lazy to add
CLI flags to trigger it :P

* In case that addresses used by concolic execution do not work, adjust them from 
[simulate.py](./source/simulate.py)

* Make sure that `$rsp` is consistent in `dump()` in [simulate.py](./source/simulate.py)


___


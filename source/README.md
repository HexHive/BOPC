

# Block Oriented Programming Compiler (BOPC)


___

### BOPC Implementation Overview

![alt text](./images/BOPC_overview.png)


### Source Code Overview


| File                             | Description                                 |
| ---------------------------------|---------------------------------------------|
| [BOPC.py](./BOPC.py)             | Main file |
| [absblk.py](./absblk.py)         | Basic block abstraction |
| [calls.py](./calls.py)           | Supported library and system calls |
| [capability.py](./capability.py) | Application Capability |
| [compile.py](./compile.py)       | SPL compiler |
| [config.py](./config.py)         | Configuration file |
| [coreutils.py](./coreutils.py)   | Shared utils across modules |
| [delta.py](./delta.py)           | Delta graph |
| [map.py](./map.py)               | Mapping across registers and variables |
| [mark.py](./mark.py)             | Marking and re-Marking CFG |
| [optimize.py](./optimize.py)     | SPL optimizer |
| [output.py](./output.py)         | Write solutions to a file |
| [path.py](./path.py)             | CFG shortest paths |
| [search.py](./search.py)         | Trace Searching algorithm |
| [simulate.py](./simulate.py)     | Concolic execution |


___
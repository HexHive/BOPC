

# Block Oriented Programming Compiler (BOPC)


___


### Installation
Just run `setup.sh` :)


### How to use BOPC

We apologize, but our detailed instructions on how to use BOPC are not available yet.
We are working on this to get ready by December :)



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


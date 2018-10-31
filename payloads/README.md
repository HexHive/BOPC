

# Block Oriented Programming Compiler (BOPC)
___


### SPL Payload Overview


| Payload                  | Description                                 |
|--------------------------|---------------------------------------------|
| [regset4](./regset4.spl) | Initialize 4 registers with arbitrary values |
| [regref4](./regref4.spl) | Initialize 4 registers with pointers to arbitrary memory |
| [regset5](./regset5.spl) | Initialize 5 registers with arbitrary values |
| [regref5](./regref5.spl) | Initialize 5 registers with pointers to arbitrary memory |
| [regmod](./regmod.spl)   | Initialize a register with an arbitrary value and modify it |
| [memrd](./memrd.spl)     | Read from arbitrary memory |
| [memwr](./memwr.spl)     | Write to arbitrary memory |
| [print](./print.spl)     | Display a message to stdout using write |
| [execve](./execve.spl)   | Spawn a shell through execve |
| [abloop](./abloop.spl)   | Perform an arbitrarily long bounded loop utilizing regmod |
| [infloop](./infloop.spl) | Perform an infinite loop that sets a register in its body |
| [ifelse](./ifelse.spl)   | An if-else condition based on a register comparison |
| [loop](./loop.spl)       | Conditional loop with register modification |


___

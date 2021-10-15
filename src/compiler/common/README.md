# Common modules 

This library contains modules that are used by two or more phases.

## Questions for studycafé 13/10
If-statements:
- Skal basic blocks termineres inden man laver en ny, eller skal de termineres til sidst ?
- Hvordan får man typen som skal bruges i alloca ?
- Hvad er sammenhængen mellem basic blocks i llvm og buildlets i koden ?

## Questions for meeting 15/10 
- In the merge block in IfExp, we're supposed to load the resulting value from th branches, but the load instruction tages an operand as second argument, what operand should be used here ?????

- Buildlets ???? they contains the instructions, but how are they connected to basic blocks and the CFG-builder?
    - basic blocks contains buildlets, yes ?
    - CFG-builder contains basic blocks (thus also buildlets)

- Icmp in ll.ml file : 
    - When doing ex EqOp : x == y
    - can we use the Icmp directly, or should we minus the operands and see if the result is equal to 0 ? We did it this way in ComArch, and someone in the studycafé mentioned it. 
    - depending on the answer, what the f is we supposed to use as the operands in Ll.Icmp :(

- ll.ml contains alot of x_to_string functions, what should we use them for?

- operands ?????????
    - how to get the relevant operands in ex. Ll.Icmp 😭
        - make local id to an operand, maybe


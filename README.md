# OPTI-MULTI-programming-language



OPTI-MULTI is a programming language that can accept any language on Turing machine. 
It is organized and executed in a similar manner to PDA’s and DFA’s. This is used to 
organize into short nodes until it reaches an end state. This shortens the space between
the actual diagram and the running code which eases the programmer to go from algorithmic
code to executing codes faster and easier.

The OPTI-MULTI consists of nodes containing operations along with transition statements.
This allows for control to leave the current node to execute a new node. There are two 
types of nodes: transition nodes and end nodes. Transition nodes can contain transition 
statements which evaluate expressions and if true, execute them. Each and every transition 
node must end with a default which makes sure that the execution leads to the end nodes. 
A return node cannot have any transition statements although it can return data, control, 
the data to the caller. All return nodes end with a return statement.The nodes can call 
the sub-state automata which will execute until they reach the end node. Nodes have the 
ability to make decisions based on the states of sibling automata that run parallel.

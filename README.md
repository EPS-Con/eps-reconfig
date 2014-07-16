eps-reconfig
============

Control synthesis for reconfigurable electric power distribution networks (inspired by tulip-control/contrib/AES)

Installation:
python, including packages networkx 
cvc4, a sat solver

There are two things required to create a synthesis controller before getting started: a netlist file corresponding to the circuit, and all guarantees and assumptions of the circuit. 

How to write a netlist file:
A netlist file is file describing all components in a circuit. For now, there are five types of component defined:
	contactors, denoted by C followed by a number
	buses, denoted by B followed by a number
	generators, denoted by G followed by a number
	APU, denoted by A followed by a number
	transformer rectifier, denoted by T followed by a number
Every port of a component is marked with a unique number. Examples of the five components in netlist file are listed below:
	C4 5 8 contactor
	B2 5 4 12 bus ac / B6 19 23 6 bus dc
	G1 0 1 generator
	A1 0 2 APU
	T5 12 9 TRU
where C4 indicates a contactor with ports 5 and 8, and B2 stands for an ac bus, B6 an dc bus. It doesn't matter for contactors and buses for which ports should be the first. For generators, APUs, and rectifier however, it follows the order of the power flow, or from ac to dc. Although in most cases, components like buses, generators and APUs are separated by contactors. There are cases where a rectifier can be connected directly to a bus. It is then very important to have some order on the ports of buses, especially the very last port. Since in our code, when transferring a netlist file into a directed graph, this last port will stand for a unique node of the component except for contactors.
All comments should begin with an '#', and all empty line will be ignored.
Finally, put an .end to the file. 

How to write requirements:
Once you got the netlist file, and checked that it is correct, you can then call functions to get prepared for synthesis. 
Call read_netlist() function to convert a netlist file into a digraph.
Then always call init() function, which will give declarations in a cvc4 file, and also fill in uncontrollable components tups and controllable components tups. 
After these two steps, define all essential buses that you wish to be powered on at all time. And also a set of components, usually generators and APUs that you don't want to parallel. Basic assumptions are to have at least one generator or APU and one rectifier healthy. Another optional assumptions are generator_priority().
Three basic guarantees implemented in the code are:
	All buses in the list given should be powered on at all time
	No paralleling among the list of components given
	Isolate the component given
The user can call multiple times of these functions to achieve guarantees. After calling all these functions, the user can then call synthesis_controller() function to synthesize the circuit.
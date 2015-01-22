'''
This is an example of a medium sized circuit with two generators and two APUs, three DC buses and two AC buses (see the netlist file medium_circuit.net)
'''
import networkx as nx
import matplotlib.pyplot as plt
import subprocess
from specs import *
from synthesis import *


filename = 'medium_circuit.net'
resultfile = 'result2.txt'
G = nx.DiGraph()
G = read_netlist(filename)
uncon_comp_tups = []
contactor_tups = []
declaration = init(G, uncon_comp_tups, contactor_tups)
G_assertions = no_paralleling_set(['G1','G2','A1','A2'], G)
e_bus_list = ['B1','B2','B3','B4','B5']
G_assertions += always_powered_on(e_bus_list, G)
G_assertions += rect_ac_dc_equ(G)
G_assertions += isolate('G1', G)
G_assertions += isolate('G2', G) 
G_assertions += isolate('A1', G)
G_assertions += isolate('A2', G)
t_tups = ['T1','T2']
for i in range(0, len(t_tups)):
    G_assertions += isolate(t_tups[i], G)   
A_assertions = generator_healthy(G)
A_assertions += rectifier_healthy(G)
nodes_number = G.nodes()
nodes_name_data = nx.get_node_attributes(G, 'name')
nodes_type_data = nx.get_node_attributes(G, 'type')
sat = synthesize_controller(G, 1, resultfile, uncon_comp_tups,
    contactor_tups, declaration, G_assertions, A_assertions)







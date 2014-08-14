''' 
This is an example of a large circuit with four generators, two APUs, and fourteen buses (see the netlist file large_circuit.net) 
'''
import networkx as nx
import matplotlib.pyplot as plt
import subprocess
from specs import *
from synthesis import *


filename = 'large_circuit.net'
resultfile = 'result3.txt'
G = nx.DiGraph()
G = read_netlist(filename)
uncon_comp_tups = []
contactor_tups = []
declaration = init(G, uncon_comp_tups, contactor_tups)
G_assertions = no_paralleling_set(['G1','G2','G3', 'G4','A1','A2'], G)
e_bus_list = ['B1','B2','B3','B4','B5','B6','B7','B8','B9','B10','B11','B12','B13','B14']
G_assertions += always_powered_on(e_bus_list, G)
G_assertions += rect_ac_dc_equ(G)
G_assertions += isolate('G1', G)
G_assertions += isolate('G2', G) 
G_assertions += isolate('G3', G)
G_assertions += isolate('G4', G)
G_assertions += isolate('A1', G)
G_assertions += isolate('A2', G)
t_tups = ['T1','T2','T3','T4','T5','T6','T7','T8']
for i in range(0, len(t_tups)):
    G_assertions += isolate(t_tups[i], G)   
A_assertions = generator_healthy(G)
A_assertions += rectifier_healthy(G)
nodes_number = G.nodes()
nodes_name_data = nx.get_node_attributes(G, 'name')
nodes_type_data = nx.get_node_attributes(G, 'type')
sat = synthesize_controller(G, 1, resultfile, uncon_comp_tups,
    contactor_tups, declaration, G_assertions, A_assertions)








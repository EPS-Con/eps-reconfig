'''Copyright (c) 2014, The Regents of the University of Michigan
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice, this
    list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions and the following disclaimer in the documentation
    and/or other materials provided with the distribution.

* Neither the name of the copyright holder nor the names of its
    contributors may be used to endorse or promote products derived from
    this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
         SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

# This is an example of simple_circuit
'''
import networkx as nx
import matplotlib.pyplot as plt
import subprocess
from specs import *
from synthesis import *


filename = 'simple_circuit'
resultfile = 'result1.txt'
G = nx.DiGraph()
G = read_netlist(filename)
uncon_comp_tups = []
contactor_tups = []
declaration = init(G, uncon_comp_tups, contactor_tups)
G_assertions = no_paralleling_set(['G1','G2'], G)
e_bus_list = ['B1','B2','B3','B4']
G_assertions += always_powered_on(e_bus_list, G)
G_assertions += rect_ac_dc_equ(G)
G_assertions += isolate('G1', G)
G_assertions += isolate('G2', G) 
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







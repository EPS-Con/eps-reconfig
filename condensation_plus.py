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

# this file contains one function that maybe useful for distributed controller 
# design
'''
import networkx as nx
import matplotlib.pyplot as plt

# The function takes in a DiGraph, and returns a tuple
# the first element of this tuple would be the condensation
# DiGraph, and the second element is a list of subgraphs
# corresponding to the node in the condensation Digraph C
def condensation_plus(G):
	C = nx.condensation(G)
	maps = {}
	maps = C.graph['mapping']

	num_of_c = C.number_of_nodes();
	nbunch = {}
	for num in range(0,num_of_c):
		nbunch[num] = []

	#search through and divide G.nodes() into groups
	for num in range(0,num_of_c):
		for name in G.nodes():
			if maps[name]==num:
				nbunch[num].append(name)

	G_sub = {};

	for i in range(0, num_of_c):
		G_sub[i] = G.subgraph(nbunch[i])

	result = [];
	result.append(C);
	result.append(G_sub);

	return result


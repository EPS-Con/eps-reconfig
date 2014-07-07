import networkx as nx
import matplotlib.pyplot as plt
import subprocess

def read_netlist(filename):
    f = open(filename,'r')
    content = f.read()
    f.close()
    
    G = nx.DiGraph()
    
    tups = content.split('\n')
    g_tups = []
    c_tups = []
    b_tups = []
    t_tups = []
    for i in range(0,len(tups)):
        line = tups[i]
        #skip empty line
        if line == '': continue
        #skip comment line
        elif line[0] == '#': continue
        #stop on reading .end
        elif line == '.end': break
        else:
            #declare nodes in directed graph
            x = line.split(' ')
            x_name = x[0]
            x_type = x[-1]
            x_num = x[-2]
            #if is bus
            if x_name[0]=='B':
                x_type = x[-2]+'_'+x[-1]
                x_num = x[-3]
                b_tups.append(line)
            elif x_name[0]=='C':
                c_tups.append(line)
            elif x_name[0]=='T':
                t_tups.append(line)
            elif x_name[0]=='G' or x_name[0]=='A':
                g_tups.append(line)
            #create nodes
            if x_type != 'contactor' and x_type != 'TRU':
                G.add_node(x_num,name=x_name,type=x_type)
            elif x_type == 'TRU':
                G.add_node(x_num,name=x_name+'_dc',type='rectifier_dc')
                G.add_node(x_num+'_ac',name=x_name+'_ac',type='rectifier_ac')
                G.add_edge(x_num+'_ac',x_num,type='wire')
    
    #create edges w/ contactor
    for i in range(0,len(c_tups)):
        line = c_tups[i].split(' ')
        c_in_port = line[1]
        c_out_port = line[2]
        dummy_node_tups = []
        node_in = searchnode(c_in_port,g_tups,b_tups,t_tups,dummy_node_tups,G)
        node_out = searchnode(c_out_port,g_tups,b_tups,t_tups,dummy_node_tups,G)
        G.add_edges_from([(node_in,node_out),(node_out,node_in)],
                         name=line[0],type=line[-1])
    
    #create edges w/o contactor, i.e. wire
    #assume only TRU can have a wire connected to other components
    for i in range(0,len(t_tups)):
        t_line = t_tups[i].split(' ')
        t_in_port = t_line[1]
        t_out_port = t_line[2]
        for j in range(0,len(b_tups)):
            b_line = b_tups[j].split(' ')
            if b_line[-1]=='AC':
                for k in range(1,len(b_line)-2):
                    if t_in_port==b_line[k]:
                        G.add_edges_from([(t_out_port+'_ac',b_line[-3]),
                                          (b_line[-3],t_out_port+'_ac')],type='wire')
                        break
            if b_line[-1]=='DC':
                for k in range(1,len(b_line)-2):
                    if t_out_port==b_line[k]:
                        G.add_edges_from([(t_out_port,b_line[-3]),
                                          (b_line[-3],t_out_port)],type='wire')
                        break
    return G

#if two nodes share one port which is not a components,
#define this node as this shared node + '_dummy'
def searchnode(port,g_tups,b_tups,t_tups,dummy_node_tups,G):
    for i in range(0,len(g_tups)):
        line = g_tups[i].split(' ')
        g_out_port = line[2]
        if port==g_out_port:
            return g_out_port
    for i in range(0,len(b_tups)):
        line = b_tups[i].split(' ')
        for j in range(1,len(line)-2):
            if port==line[j]:
                return line[-3]
    for i in range(0,len(t_tups)):
        line = t_tups[i].split(' ')
        t_in_port = line[1]
        t_out_port = line[2]
        if port==t_in_port:
            return t_out_port+'_ac'
        if port==t_out_port:
            return t_out_port
    for i in range(0,len(dummy_node_tups)):
        line = dummy_node_tups[i].split('_')
        dummy_node = line[0]
    G.add_node(port+'_dummy',name = port+'dummy', type='dummy')
    dummy_node_tups.append(port+'_dummy')
    return port+'_dummy'

#only call this function at the very beginning
#uncon_comp_tups stands for uncontrollable compononent tups
def init(G, uncon_comp_tups, contactor_tups):
    nodes_number = G.nodes()
    edges_number = G.edges()
    node_name_data = nx.get_node_attributes(G, 'name')
    edge_name_data = nx.get_edge_attributes(G, 'name')
    edge_type_data = nx.get_edge_attributes(G, 'type')
    node_type_data = nx.get_node_attributes(G, 'type')
    declaration = '(set-option :print-success false)\n'
    declaration += '(set-option :produce-models true)\n(set-logic QF_UF)\n'
    for i in range(0, len(nodes_number)):
        x = nodes_number[i]
        node_type = node_type_data[x]
        if node_type != 'dummy':
            clause = '(declare-fun ' + node_name_data[x] + ' () Bool)\n'
            if node_type == 'generator' or node_type == 'rectifier_dc':
                uncon_comp_tups.append(node_name_data[x])
            declaration += clause
    for i in range(0, len(edges_number)):
        idx = edges_number[i]
        edge_type = edge_type_data[idx]
        if edge_type == 'contactor':
            edge_name = edge_name_data[idx]
            flag = 0
            for j in range(0, len(contactor_tups)):
                if edge_name == contactor_tups[j]:
                    flag = 1
                    break
            if flag == 0: contactor_tups.append(edge_name)
    for i in range(0, len(contactor_tups)):
        clause = '(declare-fun ' + contactor_tups[i] + ' () Bool)\n'
        declaration += clause
    return declaration

#no-paralleling for the two elements given
def no_paralleling(node1, node2, G):
    nodes_number = G.nodes()
    edge_type_data = nx.get_edge_attributes(G,'type')
    node_name_data = nx.get_node_attributes(G,'name')
    edge_name_data = nx.get_edge_attributes(G,'name')
    num1 = num2 = 0
    for i in range(0, len(nodes_number)):
        x = nodes_number[i]
        if node_name_data[x] == node1:
            num1 = x
        elif node_name_data[x] == node2:
            num2 = x
    #check if components are valid
    if num1 == 0: 
        print 'Error: ' + node1 + ' Not Found'
        exit()
    if num2 == 0: 
        print 'Error: ' + node2 + ' Not Found'
        exit()
    tups = list(nx.all_simple_paths(G, num1, num2))
    clause = '(assert (not'
    if len(tups)>1: clause += ' (or'
    if tups != []:
        for k in range(0,len(tups)):
            clause += ' (and'
            one_path = tups[k]
            for x in range(0,len(one_path)-1):
                if edge_type_data[(one_path[x],one_path[x+1])]=='contactor':
                    clause += ' ' + edge_name_data[(one_path[x],one_path[x+1])]
            clause += ')'
        if len(tups)>1: clause += ')))\n'
        else: clause += '))\n'
    return clause

#no-paralleling for any two elements in name_tups provided by the user
def no_paralleling_set(name_tups, G):
    nodes_number = G.nodes()
    edge_type_data = nx.get_edge_attributes(G,'type')
    node_name_data = nx.get_node_attributes(G,'name')
    edge_name_data = nx.get_edge_attributes(G,'name')
    num_tups = []
    for i in range(0, len(name_tups)):
        for j in range(0, len(nodes_number)):
            x = nodes_number[j]
            if node_name_data[x] == name_tups[i]:
                num_tups.append(x)
        #check if there's invalid input component       
        if j == len(nodes_number):
            print 'Error: Component ' + e_bus_list[i] + ' Not Found'
            exit()
    specs_assert = ''
    for i in range(0, len(num_tups)-1):
        for j in range(i+1, len(num_tups)):
            tups = list(nx.all_simple_paths(G, num_tups[i], num_tups[j]))
            clause = '(assert (not'
            if len(tups)>1: clause += ' (or'
            if tups != []:
                for k in range(0,len(tups)):
                    clause += ' (and'
                    one_path = tups[k]
                    for x in range(0,len(one_path)-1):
                        if edge_type_data[(one_path[x],one_path[x+1])]=='contactor':
                            clause += ' ' + edge_name_data[(one_path[x],one_path[x+1])]
                    clause += ')'
                if len(tups)>1: clause += ')))\n'
                else: clause += '))\n'
            specs_assert += clause
    return specs_assert


def always_powered_on(e_bus_list, G):
    nodes_number = G.nodes()
    edge_type_data = nx.get_edge_attributes(G,'type')
    node_name_data = nx.get_node_attributes(G,'name')
    node_type_data = nx.get_node_attributes(G,'type')
    edge_name_data = nx.get_edge_attributes(G,'name')
    type_data = nx.get_node_attributes(G,'type')
    generator_list = []
    apu_list = []
    for i in range(0,nx.number_of_nodes(G)):
        x = nodes_number[i]
        if type_data[x]=='generator':
            generator_list.append(x)
        elif type_data[x]=='APU':
            apu_list.append(x)
    ac_bus_num = []
    dc_bus_num = []
    for i in range(0, len(e_bus_list)):
        for j in range(0, len(nodes_number)):
            x = nodes_number[j]
            if node_name_data[x] == e_bus_list[i]:
                if node_type_data[x] == 'bus_AC':
                    ac_bus_num.append(x)
                elif node_type_data[x] == 'bus_DC':
                    dc_bus_num.append(x)
                else:
                    print 'Error: Component ' + e_bus_list[i] + 'Not Found'
                    exit(1)
                break
    specs_assert = ''
    #ac bus
    for i in range(0,len(ac_bus_num)):
        bus_name = node_name_data[ac_bus_num[i]]
        clause = '(assert (= ' + bus_name
        if len(generator_list)+len(apu_list)>1:
            clause += '(or '
        for j in range(0,len(generator_list)):
            tups = list(nx.all_simple_paths(G,generator_list[j],ac_bus_num[i])) 
            for k in range(0,len(tups)):
                #add nodes along the path to the clause
                #add edges that have contactor to the clause
                clause += '(and'
                one_path = tups[k]
                for x in range(0,len(one_path)-1):
                    if node_type_data[one_path[x]]!='dummy':
                        clause += ' ' + node_name_data[one_path[x]]
                    if edge_type_data[(one_path[x],one_path[x+1])]=='contactor':
                        clause += ' ' + edge_name_data[(one_path[x],one_path[x+1])]
                clause += ')'
        if len(apu_list) != 0:
            for l in range(0,len(apu_list)):
                tups = list(nx.all_simple_paths(G,apu_list[l],ac_bus_num[i]))   
                for k in range(0,len(tups)):
                    #add nodes along the path to the clause
                    #add edges that have contactor to the clause
                    clause += '(and'
                    one_path = tups[k]
                    for x in range(0,len(one_path)-1):
                        if node_type_data[one_path[x]]!='dummy':
                            clause += ' ' + node_name_data[one_path[x]]
                        if edge_type_data[(one_path[x],one_path[x+1])]=='contactor':
                            clause += ' ' + edge_name_data[(one_path[x],one_path[x+1])]
                    clause += ')'
        if len(generator_list)+len(apu_list)>1:
            clause += ')))\n'
        else:
            clause += '))\n'
        specs_assert += clause

    #dc bus
    for i in range(0, len(dc_bus_num)):
        bus_name = node_name_data[dc_bus_num[i]]
        clause = '(assert (= ' + bus_name
        if len(ac_bus_num)>1:
            clause += '(or '
        for j in range(0, len(ac_bus_num)):
            tups = list(nx.all_simple_paths(G, ac_bus_num[j], dc_bus_num[i]))
            for k in range(0,len(tups)):
                clause += '(and'
                one_path = tups[k]
                for x in range(0,len(one_path)-1):
                    if node_type_data[one_path[x]]!='dummy' and node_type_data[one_path[x]]!='rectifier_dc':
                        clause += ' ' + node_name_data[one_path[x]]
                    if edge_type_data[(one_path[x],one_path[x+1])]=='contactor':
                        clause += ' ' + edge_name_data[(one_path[x],one_path[x+1])]
                clause += ')'
        if len(ac_bus_num)>1:
            clause += ')))\n'
        else:
            clause += '))\n'
        specs_assert += clause

    clause = '(assert (and'
    for i in range(0, len(e_bus_list)):
        clause += ' ' + e_bus_list[i]
    clause += '))\n'
    specs_assert += clause
    return specs_assert

#specify that the bus can only be powered on by a list of 
#generators or APUs
def powered_on_by(bus_name, g_list, G):
    nodes_number = G.nodes()
    edge_type_data = nx.get_edge_attributes(G,'type')
    node_name_data = nx.get_node_attributes(G,'name')
    node_type_data = nx.get_node_attributes(G,'type')
    edge_name_data = nx.get_edge_attributes(G,'name')
    for i in range(0, len(nodes_number)):
        x = nodes_number[i]
        if node_name_data[x] == bus_name:
            bus_num = x
    if i == len(nodes_number):
        print 'Error: ' + bus_name + ' Not Found'
        exit()
    g_num = []
    for i in range(0, len(g_list)):
        for j in range(0, len(nodes_number)):
            x = nodes_number[j]
            if node_name_data[x] == g_list[i]:
                g_num.append(x)
                break
        if j == len(nodes_number):
            print 'Error: ' + g_list[i] +' Not Found'
            exit()
    clause = '(assert (= ' + bus_name + '(or '
    for i in range(0,len(g_num)):
        tups = list(nx.all_simple_paths(G,g_num[i],bus_num))    
        for j in range(0,len(tups)):
            #add nodes along the path to the clause
            #add edges that have contactor to the clause
            clause += '(and'
            one_path = tups[j]
            for x in range(0,len(one_path)-1):
                if node_type_data[one_path[x]]!='dummy':
                    clause += ' ' + node_name_data[one_path[x]]
                if edge_type_data[(one_path[x],one_path[x+1])]=='contactor':
                    clause += ' ' + edge_name_data[(one_path[x],one_path[x+1])]
            clause += ')'
            #path_list.append(tups[k])
    clause += ')))\n'
    return clause

#at least one generator or APU is healthy
def generator_healthy(G):
    nodes_number = G.nodes()
    node_name_data = nx.get_node_attributes(G,'name')
    type_data = nx.get_node_attributes(G,'type')
    generator_list = []
    for i in range(0,nx.number_of_nodes(G)):
        x = nodes_number[i]
        if type_data[x]=='generator':
            generator_list.append(x)
    clause = '(assert (or'
    for i in range(0, len(generator_list)):
        g_name = node_name_data[generator_list[i]]
        clause += ' ' + g_name
    clause += '))\n'
    return clause

#at least one rectifier is healthy
#bind the ac part and dc part of a rectifier together in a sat problem
def rectifier_healthy(G):
    nodes_number = G.nodes()
    node_name_data = nx.get_node_attributes(G,'name')
    type_data = nx.get_node_attributes(G,'type')
    rectifier_list = []
    for i in range(0,nx.number_of_nodes(G)):
        x = nodes_number[i]
        if type_data[x]=='rectifier_dc':
            rectifier_list.append(x)
    specs_assert = ''
    clause = '(assert (or'
    for i in range(0, len(rectifier_list)):
        r_name = node_name_data[rectifier_list[i]]
        clause += ' ' + r_name
    clause += '))\n'
    specs_assert += clause
    return specs_assert

#equivalent the ac part and dc part of a rectifier
def rect_ac_dc_equ(G):
    nodes_number = G.nodes()
    node_name_data = nx.get_node_attributes(G,'name')
    type_data = nx.get_node_attributes(G,'type')
    rectifier_list = []
    for i in range(0,nx.number_of_nodes(G)):
        x = nodes_number[i]
        if type_data[x]=='rectifier_dc':
            rectifier_list.append(x)
    specs_assert = ''
    for i in range(0, len(rectifier_list)):
        clause = '(assert (='
        r_dc_name = node_name_data[rectifier_list[i]]
        r_ac_name = r_dc_name.replace('_dc', '_ac')
        clause += ' ' + r_ac_name + ' ' + r_dc_name + '))\n'
        specs_assert += clause
    return specs_assert

#allow user to set values of controllable components
#if value == 1, then set component to be true
#if value == 0, then set component to be false
def setValue(component, value, G):
    if component[0] == 'T':
        component += '_dc'
    if value == 1:
        clause = '(assert ' + component + ')\n'
    elif value == 0:
        clause = '(assert (not ' + component + '))\n'
    return clause

#if a component (not a contactor) turns unhealthy, 
#open all contactors next to it
def isolate(component, G):
    nodes_number = G.nodes()
    edges_number = G.edges()
    edge_type_data = nx.get_edge_attributes(G,'type')
    node_name_data = nx.get_node_attributes(G,'name')
    edge_name_data = nx.get_edge_attributes(G,'name')
    comp2 = component
    if component[0] == 'T':
        comp1 = component + '_ac'
        comp2 = component + '_dc'
    comp_num1 = comp_num2 = comp_num = 0
    for i in range(0, len(nodes_number)):
        x = nodes_number[i]
        if component[0] != 'T' and node_name_data[x] == component:
            comp_num = x
            break
        elif component[0] == 'T' and node_name_data[x] == comp2:
            comp_num2 = x
            comp_num1 = x + '_ac'
            break
    if i == len(nodes_number):
        print 'Error: ' + component + ' Not Found'
        exit()
    neighbor_idx = []
    if component[0] != 'T':
        for i in range(0, len(edges_number)):
            if edges_number[i][0] == comp_num:
                neighbor_idx.append(edges_number[i])
    else:
        for i in range(0, len(edges_number)):
            if edges_number[i][0] == comp_num1 or edges_number[i][0] == comp_num2:
                neighbor_idx.append(edges_number[i])
    clause = '(assert (=> (not ' + comp2 + ')'
    contactor_tups = []
    for i in range(0, len(neighbor_idx)):
        idx = neighbor_idx[i]
        if edge_type_data[idx] == 'contactor':
            edge_name = edge_name_data[idx]
            contactor_tups.append(edge_name)
    if len(contactor_tups) > 1:
        clause += ' (and '
    for i in range(0, len(contactor_tups)):
        clause += '(not ' + contactor_tups[i] + ')'
    if len(contactor_tups) > 1:
        clause += ')))\n'   
    elif len(contactor_tups) == 1:
        clause += '))\n'
    return clause

#APUs should only be turned on if some or all generators go unhealthy
def generator_priority(G):
    nodes_number = G.nodes()
    node_name_data = nx.get_node_attributes(G,'name')
    type_data = nx.get_node_attributes(G,'type')
    generator_list = []
    APU_list = []
    for i in range(0,nx.number_of_nodes(G)):
        x = nodes_number[i]
        if type_data[x]=='generator':
            generator_list.append(x)
        elif type_data[x]=='APU':
            APU_list.append(x)
    if len(APU_list) == 0:
        return
    clause = '(assert (=> '
    if len(generator_list) > 1:
        clause += '(and'
    for i in range(0, len(generator_list)):
        g_name = node_name_data[generator_list[i]]
        clause += ' ' + g_name
    clause += ') '
    if len(APU_list) > 1:
        clause += '(and '
    for i in range(0, len(APU_list)):
        apu_name = node_name_data[APU_list[i]]
        clause +=  '(not ' + apu_name + ')'
    clause += ')))\n'
    return clause





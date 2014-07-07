import networkx as nx
import matplotlib.pyplot as plt
import subprocess


#if one_solution is 1, then only produce one solution 
#that makes it satisfiable
#else this function will produce all possible solutions
def synthesize_controller(G, one_solution, outfilename, uncon_comp_tups, 
    contactor_tups, declaration, G_assertions, A_assertions):
    g_cvcfile = '../gcvcfile.smt2'
    a_cvcfile = '../acvcfile.smt2'
    cvc_mode = '--smtlib-strict'

    assump_decl = '(set-option :print-success false)\n'
    assump_decl += '(set-option :produce-models true)\n(set-logic QF_UF)\n'

    #create get-value clause
    switches = '('
    for i in range(0, len(contactor_tups)):
        switches += ' ' + contactor_tups[i]
    switches += ')'
    uncontrollable = '('
    for i in range(0, len(uncon_comp_tups)):
        uncontrollable += ' ' + uncon_comp_tups[i]
        clause = '(declare-fun ' + uncon_comp_tups[i] + ' () Bool)\n'
        assump_decl += clause
    uncontrollable += ')'
    
    checksat = '(check-sat)\n'
    x = declaration + G_assertions
    y = '(get-value ' + uncontrollable +')\n'
    z = '(get-value ' + switches + ')\n'
    #cvc4 file input for assumptions only
    af = open(a_cvcfile, 'w+')
    af.write(assump_decl+A_assertions+checksat)
    af.close()

    sat_tuples = 'sat_tuples:\n' 
    while True:
        env_result = subprocess.check_output(["cvc4", cvc_mode, a_cvcfile])
        tup = env_result.split('\n')
        #if there is an available environment condition
        if tup[-2] == 'sat':
            af = open(a_cvcfile, "a")
            af.write(y)
            af.close()
            env_result = subprocess.check_output(["cvc4", cvc_mode, a_cvcfile])
            tup = env_result.split('\n')
            #get ready for finding another environment condition
            sat_tuples += tup[-2] +':\n'
            s = tup[-2][1:].replace('(', '(= ')
            s0 = '(assert (not (and '+s+'))\n'
            s1 = '(assert (and '+s+')\n'
            af = open(a_cvcfile, "a")
            af.write(s0)
            af.write(checksat)
            af.close()
            #import this environment condition into gurantees
            gf = open(g_cvcfile, "w+")
            gf.write(x+s1+checksat)
            gf.close()
            g_result = subprocess.check_output(["cvc4", cvc_mode, g_cvcfile])
            tup = g_result.split('\n')
            if tup[-2] == 'sat':
                gf = open(g_cvcfile, "a")
                gf.write(z)
                gf.close()
                g_result = subprocess.check_output(["cvc4", cvc_mode, g_cvcfile])
                tup = g_result.split('\n')
                while True:
                    sat_tuples += '\t'+tup[-2]+'\n'
                    if one_solution==1:
                        break
                    s = tup[-2][1:].replace('(','(= ')
                    s2 = '(assert (not (and '+s+'))\n'
                    gf = open(g_cvcfile, "a")
                    gf.write(s2+checksat)
                    gf.close()
                    g_result = subprocess.check_output(["cvc4", cvc_mode, g_cvcfile])
                    tup = g_result.split('\n')
                    if tup[-2] == 'sat':
                        f = open(g_cvcfile, "a")
                        f.write(z)
                        f.close()
                        result = subprocess.check_output(["cvc4", cvc_mode, g_cvcfile])
                        tup = result.split('\n')
                    else:
                        break
        else:
            break
    of = open(outfilename, 'w+')
    of.write(sat_tuples)
    of.close()
    return 1

#obtain possible values for environment components
def generate_assump(G, outfilename, uncon_comp_tups, 
    declaration, assertions):
    g_cvcfile = "/Users/jingji/Desktop/testwu.smt2"
    cvc_mode = "--smtlib-strict"
    uncontrollable = '('
    for i in range(0, len(uncon_comp_tups)):
        uncontrollable += ' ' + uncon_comp_tups[i]
    uncontrollable += ')'
    f = open(g_cvcfile, "w+")
    checksat = '(check-sat)\n'
    x = declaration + assertions
    y = '(get-value ' + uncontrollable +')\n'
    
    f.write(x + checksat)
    f.close()
    env = ''

    while True:
        result = subprocess.check_output(["cvc4", cvc_mode, g_cvcfile])
        tup = result.split('\n')
        if tup[-2] == 'sat':
            f = open(g_cvcfile, "a")
            f.write(y)
            f.close()
            result = subprocess.check_output(["cvc4", cvc_mode, g_cvcfile])
            tup = result.split('\n')
            env += tup[-2] + '\n'
            s0 = tup[-2][1:].replace('(', '(= ')
            s0 = '(assert (not (and ' + s0 + '))\n'
            f = open(g_cvcfile, "a")
            f.write(s0)
            f.write('(check-sat)\n')
            f.close()
        else:
            break
    of = open(outfilename, 'w+')
    of.write(env)
    of.close()








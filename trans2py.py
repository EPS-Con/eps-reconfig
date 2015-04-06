# this GenCond function will generate a python
# file with a if-elif-else statements corresponds
# to the results obtained from the SAT solver
# this function takes an input file which is in
# smt-lib output format, and an output file which
# is a python format
def GenCond(infile, outfile):
    state = 'if '
    output = ''
    flag = 0
    num = 0
    with open(infile, 'r') as f:
        for line in f:
            if line=='' or line=='\n':
                break
            tups = line.split(') (')
            length = len(tups)
            # conditional clause
            if line[0]=='(':
                if flag==1:
                    continue
                flag = 1
                if num!=0:
                    state = 'elif '
                num += 1
                for i in range(0, length):
                    if i==0:
                        comp = tups[i][2:]
                    elif i==length-1:
                        comp = tups[i][:-4]
                    else:
                        comp = tups[i]
                    clause = comp.replace('true','== 1')
                    clause = clause.replace('false','== 0')
                    if i<length-1:
                        state += clause+' and '
                    else:
                        state += clause+':\n'
            # statements
            elif line[0]=='\t':
                flag = 0
                state = ''
                for i in range(0, length):
                    if i==0:
                        comp = tups[i][3:]
                    elif i==length-1:
                        comp = tups[i][:-3]
                    else:
                        comp = tups[i]
                    clause = comp.replace('true','= 1')
                    clause = clause.replace('false','= 0')
                    state += '\t'+clause+'\n'
            output += state

    state = 'else\n\t'
    state += 'disp(\'Cannot find a valid successor\')\n'

    output += state

    of = open(outfile,'w+')
    of.write(output)
    of.close()
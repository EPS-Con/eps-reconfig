#convert a truth lookup table into matlab file
def to_matlab(infile, outfile):
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
            if line[0]=='(':
                if flag==1:
                    continue
                flag = 1
                if num!=0:
                    state = 'elseif '
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
                        state += clause+' && '
                    else:
                        state += clause+'\n'
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
                    if i<length-1:
                        state += clause+'; '
                    else:
                        state += clause+';\n'
            output += state
    state = 'else\n'
    state += 'disp(\'Cannot find a valid successor\')\n'
    state += 'end'
    output += state
    of = open(outfile,'w+')
    of.write(output)
    of.close()

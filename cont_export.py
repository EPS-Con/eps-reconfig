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

# This function converts a truth lookup table into matlab if-else statements
'''
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

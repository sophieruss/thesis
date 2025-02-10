from host import parse_command, host
from sentry import parse_trace, sentry
from trace_file import *
import time

prog = [None] * 100

# I am not error checking at all. Assume the user is perfect. I.e. no R[32]
# assume M[0] = 0, S[0] = 0
# or assume a zero register instead.

with open('Python Simulator/programs/basic_loop.csv', 'r') as f:
    for i, line in enumerate(f):
        if line[0] == '#':
            break
        prog[i] = line.split()
        for x in range(1, len(prog[i])):
            prog[i][x] = int(prog[i][x])        

print(prog)

def main():

    with open('trace_history.json', 'w') as f:
        f.write('')
        
    h = host()
    s = sentry()
    h.S = 1

    ctr = 0
    while prog[h.pc]:
        print(h.pc)
        ctr += 1
        if ctr > 10:
            break
        if (parse_command(h, prog[h.pc])):
            # if h.pc == 8: 
            #     s.evil()                # R[5] = 500
                                        # pc == 7 || 8 would reject
            if(parse_trace(s)):
                pass
            else:
                print("Sentry rejects. Program halted.")
                return
    print("Program completed successfully.")
main()  

    
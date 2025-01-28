from host import parse_command
from sentry import parse_trace, evil
from trace_file import *
import time

program = [None] * 100

# fibonacci
# [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377]

# I am not error checking at all. Assume the user is perfect. I.e. no R[32]

# assume M[0] = 0, S[0] = 0

program[0] = ["Lw_T", 0, 0]         # R[0] = 0
program[1] = ["Addi", 1, 0, 1]      # R[1] = 1
program[2] = ["Addi", 2, 1, 0]      # R[2] = 1
program[3] = ["Add", 3, 1, 2]       # R[3] = 2
program[4] = ["Add", 4, 2, 3]       # R[4] = 3
program[5] = ["Add", 5, 3, 4]       # R[5] = 5
program[6] = ["Add", 6, 4, 5]       # R[6] = 8
program[7] = ["Add", 7, 5, 6]       # R[7] = 13
program[8] = ["Add", 8, 6, 7]       # R[8] = 21
program[9] = ["Add", 9, 7, 8]       # R[9] = 34
program[10] = ["Add", 10, 8, 9]     # R[10] = 55
program[11] = ["Add", 11, 9, 10]    # R[11] = 89
program[12] = ["Add", 12, 10, 11]   # R[12] = 144
program[13] = ["Add", 13, 11, 12]   # R[13] = 233
program[14] = ["Add", 14, 12, 13]   # R[14] = 377

def main():

    with open('trace_history.json', 'w') as f:
        f.write('')
                   
    pc = 0

    while program[pc]:
        if (parse_command(program[pc])):
            if pc == 8: 
                # change reg 5 -> prog[6] and[7] should reject. only??? 
                evil()
            if(parse_trace()):
                pc += 1
            else:
                print("Sentry rejects. Program halted.")
                break
main()  

    
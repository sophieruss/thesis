
import json

pc = 0          # pc
r = [0] * 32    # registers r -> X
R = [0] * 32    # register file r -> Z
M = {}          # memory
S = 0           # mode bit
program = {}    # Z -> commands
getQ = []
trace = []       
from commands import Add, Addi, Sub, Jump, Bgtz, Sw, Lw_U, Lw_T, Get, Put, trustedMode, untrustedMode, alert, returnn
from trace_file import send_trace

# assumption
M[0] = 0
S = 1


def fun_add(dest, src, temp):
    global pc, R, S, program, trace
    cmd = Add(dest, src, temp)
    program[pc] = cmd
    n_0 = R[src]
    n_1 = R[temp]
    n_2 = n_0 + n_1
    if S == 1:
        trace = [program[pc], n_0, n_1, n_2]
        
        # ok these two lines are allegedly after trace logic - ask!
        R[dest] = n_2
        pc += 1
    else:
        trace = []
    return send_trace(trace)
    

def fun_addi(dest, src, n_1):
    global pc, R, S, program, trace
    cmd = Addi(dest, src, n_1)
    program[pc] = cmd
    n_0 = R[src]
    n_2 = n_0 + n_1
    if S == 1:
        trace = [program[pc], n_0, n_2]
        R[dest] = n_2
        pc += 1
    else:
        trace = []
    return send_trace(trace)


def fun_sub(dest, src, temp):
    global pc, R, S, program, trace
    cmd = Sub(dest, src, temp)
    program[pc] = cmd
    n_0 = R[src]
    n_1 = R[temp]
    n_2 = n_0 - n_1
    if S == 1:
        trace = [program[pc], n_0, n_1, n_2]
        R[dest] = n_2
        pc += 1
    else:
        trace = []
    return send_trace(trace)

        
        

def fun_jump(n):
    global pc, program, S, trace
    cmd = Jump(n)
    program[pc] = cmd
    if S == 1:
        trace = [program[pc], n]
        pc = n

    else:
        trace = []
    return send_trace(trace)


def fun_bgtz_g(src, n):
    global pc, R, S, program, trace
    cmd = Bgtz(src, n)
    program[pc] = cmd
    n_1 = R[src]
    if S == 1 and n_1 > 0:
        trace = [program[pc], n_1, n]
        pc = n

    else:
        trace = []
    return send_trace(trace)


def fun_bgtz_l(src, n):
    global pc, R, S, program, trace
    cmd = Bgtz(src, n)
    program[pc] = cmd
    n_1 = R[src]
    if S == 1 and n_1 <= 0:
        trace = [program[pc], n_1, pc+1]
        pc += 1
    return send_trace(trace)

        
def fun_load_unt(src, dest):
    global pc, R, S, program, trace
    cmd = Lw_U(src, dest)
    program[pc] = cmd
    n_0 = R[src]
    n_1 = M[n_0]
    if S == 1:
        trace = [program[pc], n_1, pc+1]
        R[dest] = n_1
        pc += 1
    else:
        trace = []
    return send_trace(trace)


def fun_load(src, dest):
    global pc, R, S, program, trace
    cmd = Lw_T(src, dest)
    program[pc] = cmd
    n_0 = R[src]
    n_1 = M[n_0]
    if S == 1:
        trace = [program[pc], n_0, n_1]
        R[dest] = n_1
        pc += 1
    else:
        trace = []
    return send_trace(trace)

        
def fun_store(src, dest):
    global pc, R, S, program, trace
    cmd = Sw(src, dest)
    program[pc] = cmd
    n_0 = R[dest]
    n_1 = R[src]
    if S == 1:
        trace = [program[pc], n_0, n_1]
        M[n_0] = n_1
        pc += 1
    else:
        trace = []
    return send_trace(trace)
        
def fun_get(dest):
    global pc, R, S, program, trace
    cmd = Get(dest)
    program[pc] = cmd
    
    n = -1              # how to get n????
    getQ_0 = getQ + [n]   # does :: mean add it to queue?
    
    if S == 1:
        trace = [program[pc], n]
        R[dest] = n
        getQ = getQ_0
        pc += 1
    else:
        trace = []
    return send_trace(trace)
    
def fun_put(src):
    global pc, R, S, program, trace
    cmd = Put(src)
    program[pc] = cmd
    
    n = R[src]
    if S == 1:
        trace = [program[pc], n]
        pc += 1
    else:
        trace = []
    return send_trace(trace)
    
def fun_enable():
    global S, program
    cmd = trustedMode()
    program[pc] = cmd
    S = 1
    pc += 1

def fun_disable():
    global S, program
    cmd = untrustedMode()
    program[pc] = cmd
    S = 0
    pc += 1
    
def fun_alert():
    global program, trace
    cmd = alert()
    program[pc] = cmd
    if S == 1:
        trace = [program[pc]]
    return send_trace(trace)

def fun_returnn():
    global program, trace
    cmd = returnn()
    program[pc] = cmd
    if S == 1:
        trace = [program[pc]] 
    return send_trace(trace)

def print_program():
    print(f"host\tpc: {pc-1}\tR[]: {' '.join(map(str, R))}")

    
def parse_command(cmd):
    if cmd[0] == "Add":
        fun_add(cmd[1], cmd[2], cmd[3])
    elif cmd[0] == "Addi":
        fun_addi(cmd[1], cmd[2], cmd[3])
    elif cmd[0] == "Sub":
        fun_sub(cmd[1], cmd[2], cmd[3])
    elif cmd[0] == "Jump":
        fun_jump(cmd[1])
    elif cmd[0] == "Bgtz":
        if cmd[2] > 0:
            fun_bgtz_g(cmd[1], cmd[2])
        else:
            fun_bgtz_l(cmd[1], cmd[2])
    elif cmd[0] == "Sw":
        fun_store(cmd[1], cmd[2])
    elif cmd[0] == "Lw_U":
        fun_load_unt(cmd[1], cmd[2])
    elif cmd[0] == "Lw_T":
        fun_load(cmd[1], cmd[2])
    elif cmd[0] == "Get":
        fun_get(cmd[1])
    elif cmd[0] == "Put":
        fun_put(cmd[1])
    elif cmd[0] == "trustedMode":
        fun_enable()
    elif cmd[0] == "untrustedMode":
        fun_disable()
    elif cmd[0] == "alert":
        fun_alert()
    elif cmd[0] == "returnn":
        fun_returnn()
    else:
        raise ValueError(f"Unknown command: {cmd[0]}")
    print_program()
    return 1


def main():
    global S, R, pc
    
    with open('trace_history.json', 'w') as f:
        f.write('')
    print("hello host")
    
    S = 1
    R[1] = 1
    R[2] = 2
    R[3] = 3
    
    print_program()

    fun_add(1, 2, 3)
    # fun_addi(4, 1, 5)
    # # fun_jump(0)
    # fun_sub(1, 4, 3)
    print_program()

    return 0


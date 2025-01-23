#  TODO: might be a fundamental problem where I am setting this equal, and instead it should just be checking these "rules" are true?

pc = 0          # pc
r = [0] * 32    # registers r -> X
R = [0] * 32    # register file r -> Z
                # hash()
S = {}          # hash storage Z -> Z
program = {}
getQ = []
putQ = []
trace = None      # (command, [n0, n1, ...])
from commands import Add, Addi, Sub, Jump, Bgtz, Lw_U, Lw_T, Sw, Get, Put, alert, returnn
from trace_file import read_trace

def fun_add(dest, src, temp):
    global pc, R, S, program, trace
    # t_c = trace[0]          # a commands 
    # n_0 = trace[1][0]
    # n_1 = trace[1][1]
    # n_2 = trace[1][2]
    
    # what do I actually need to do. trace values already exist. 
    # Is this where I am checking / redoing calculation
    # i.e. I know the trace values are correct, but I need to check if they match
    # so check if R[src] == n_0, R[temp] == n_1, n[d] == n_0 + n_1
    
    # I am going to assume we're not redoing, and later just checking systems are same after??
    
    # cmd = Add(dest, src, temp)
    # if t_c == cmd && R[src] == n_0 && R[temp] == n_1 && R[dest] == n_2:
        
    # Are we supposed to be setting equal? Or is this just a check? 
    # Or actually is this nothing. But wouldn't we need R[src] to be set to n_0, so systems are in sync?      
    cmd = Add(dest, src, temp)
    program[pc] = cmd       # == trace[0]
    n_0 = R[src]            # == trace[1][0]          
    n_1 = R[temp]           # == trace[1][1]
    n_2 = n_0 + n_1         # == trace[1][2]  
    
    R[dest] = n_2
    pc += 1
    # P[1] return
    # P[0] alert

def fun_addi(dest, src, n_1):
    global pc, R, S, program, trace
    
    cmd = Addi(dest, src, n_1)
    program[pc] = cmd       # == trace[0]
    n_0 = R[src]            # == trace[1][0] 
    n_2 = n_0 + n_1         # == trace[1][1]
    
    # rule1 = program[pc] == trace[0]
    # rule2 = R[src] == trace[1][0]
    # rule3 = R[dest] == trace[1][1]
    # if rule1 && rule2 && rule3:

    R[dest] = n_2
    pc += 1

def fun_sub(dest, src, temp):
    global pc, R, S, program, trace
    
    cmd = Sub(dest, src, temp)
    program[pc] = cmd       # == trace[0]
    n_0 = R[src]            # == trace[1][0]
    n_1 = R[temp]           # == trace[1][1]
    n_2 = n_0 - n_1         # == trace[1][2]


    R[dest] = n_2
    pc += 1

def fun_jump(n):
    global pc, program, S, trace
    cmd = Jump(n)
    program[pc] = cmd       # == trace[0]

    pc = n

def fun_bgtz_g(src, n):
    global pc, R, S, program, trace
    cmd = Bgtz(src, n)
    program[pc] = cmd       # == trace[0]
    n_1 = R[src]            # == trace[1][0]
                            # n == trace[1][1] 
    if n_1 > 0:             # if or rule?
        pc = n              

def fun_bgtz_l(src, n):
    global pc, R, S, program, trace
    cmd = Bgtz(src, n)
    program[pc] = cmd       # == trace[0]
    n_1 = R[src]            # == trace[1][0]
    
    if n_1 <= 0:            # this might not be an if. it's a statement. if it's not true, than we dont do anything. which means systems will be different, and we alert
        pc += 1
        
def fun_load_unt(dest, src):
    global pc, R, S, program, trace
    cmd = Lw_U(src=src, dest=dest)
    program[pc] = cmd
    n_1 = R[src]            # == trace[1][0]
    n_2 = S[n_1]            # == trace[1][1]

    R[dest] = n_2
    pc += 1
    
def fun_load(dest, src):
    global pc, R, S, program, trace
    cmd = Lw_T(src=src, dest=dest)
    program[pc] = cmd       # == trace[0]
    n_0 = R[src]            # == trace[1][0]
    n_1 = trace[1][1]
    n_2 = S[n_0]            # == hash(n_1)

    R[dest] = n_1
    pc += 1
    
def fun_store(dest, src):
    global pc, R, S, program, trace
    cmd = Sw(src=src, dest=dest)
    program[pc] = cmd       # == trace[0]
    n_0 = R[dest]           # == trace[1][0]
    n_1 = R[src]            # == trace[1][1]
    n_2 = hash(n_1)
    
    S[n_0] = n_2
    pc += 1
    
def fun_get(dest):
    global pc, R, S, program, trace
    cmd = Get(dest)
    program[pc] = cmd       # == trace[0]
    n = getQ[0]             # == trace[1][0]
    getQ_ = getQ[1:]
    getQ == [n] + getQ_     #ARE WE CHECKING THIS
    
    R[dest] = n
    getQ = getQ_
    pc += 1

def fun_put(src):
    global pc, R, S, program, trace
    cmd = Put(src)
    program[pc] = cmd       # == trace[0]
    n = R[src]              # == trace[1][0]
    putQ_ = putQ + [n]
        
    putQ = putQ_
    pc += 1
    
def fun_alert():
    global program, pc, trace
    cmd = alert()
    program[pc] = cmd       # == trace[0]
    
    pc = 0
    
    
def fun_returnn():
    global program, pc, trace
    cmd = returnn()
    program[pc] = cmd       # == trace[0]
    
    # TODO: PC done?
    
def fun_accept(R_, S_, trace_, putQ_, getQ_, pc_): 
    global pc, R, S, trace, putQ, getQ
    R = R_
    S = S_
    trace = trace_
    putQ = putQ_
    getQ = getQ_
    pc = pc_    
    
def fun_reject():
    pc = 0
    
def fun_empty():
    pass



    
def print_program():
    print(f"pc: {pc}")
    print(f"r[]: {' '.join(map(str, r))}")
    print(f"R[]: {' '.join(map(str, R))}")
    print()


def main():
    global S, R, pc

    print("hi sentry")
    
    R[1] = 1
    R[2] = 2
    R[3] = 3
    
    global trace
    trace = read_trace()
    print(trace)
    
    # print_program()

    # fun_add(1, 2, 3)
    
    # print_program()

    return 0

main()

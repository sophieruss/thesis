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

# assumption
S[0] = 0

def fun_accept(R_, S_, trace_, putQ_, getQ_, pc_): 
    global pc, R, S, trace, putQ, getQ
    R = R_
    S = S_
    trace = trace_
    putQ = putQ_
    getQ = getQ_
    pc = pc_  
    # print("accept")
    return 1  
    
def fun_reject():
    pc = 0
    # print("reject")
    return 0
    
def fun_empty():
    pass
    # print("empty")
    return 2


def fun_add(dest, src, temp):
    global pc, R, S, program, trace
        
    cmd = Add(dest, src, temp)
    program[pc] = cmd       # == trace[0]
    n_0 = R[src]            # == trace[1][0]          
    n_1 = R[temp]           # == trace[1][1]
    n_2 = n_0 + n_1         # == trace[1][2]  
    
    # put here?  
    R[dest] = n_2
    pc += 1
    
    # rule1 = program[pc] == trace[0]     # check cmd, dest, src, temp - but also I literally got it from trace ?? 
    rule1 = True
    rule2 = R[src] == trace[1][0]
    rule3 = R[dest] == trace[1][2]      # false bc hasnt updated calculation
    rule4 = n_2 == trace[1][2]
        
    if trace == None or trace == []:
        return fun_empty()
    elif rule1 and rule2 and rule3 and rule4:
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()

def fun_addi(dest, src, n_1):
    global pc, R, S, program, trace
    
    cmd = Addi(dest, src, n_1)
    program[pc] = cmd       # == trace[0]
    n_0 = R[src]            # == trace[1][0] 
    n_2 = n_0 + n_1         # == trace[1][1]
    
    # put here?
    pc += 1
    R[dest] = n_2   
    #TODO: this is wrong? what is the point of fun_accept then. Is fun_accept supposed to update R? 
    
    # rule1 = program[pc] == trace[0]
    rule1 = 1
    rule2 = R[src] == trace[1][0]
    rule3 = R[dest] == trace[1][1]
    
    if trace == None or trace == []:
        return fun_empty()
    elif rule1 and rule2 and rule3:
        R_ = R.copy()
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()

def fun_sub(dest, src, temp):
    global pc, R, S, program, trace
    
    cmd = Sub(dest, src, temp)
    program[pc] = cmd       # == trace[0]
    n_0 = R[src]            # == trace[1][0]
    n_1 = R[temp]           # == trace[1][1]
    n_2 = n_0 - n_1         # == trace[1][2]
    
    pc += 1
    R[dest] = n_2

    # rule1 = program[pc] == trace[0]
    rule1 = 1
    rule2 = R[src] == trace[1][0]
    rule3 = R[dest] == trace[1][2]
    rule4 = n_2 == trace[1][2]
    
    if trace == None or trace == []:
        return fun_empty()
    elif rule1 and rule2 and rule3 and rule4:
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()

def fun_jump(n):
    global pc, program, S, trace
    cmd = Jump(n)
    program[pc] = cmd       # == trace[0]
    
    pc = n
    
    # rule1 = program[pc] == trace[0]
    rule1 = 1

    if trace == None or trace == []:
        return fun_empty()
    elif rule1:
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()


def fun_bgtz_g(src, n):
    global pc, R, S, program, trace
    cmd = Bgtz(src, n)
    program[pc] = cmd       # == trace[0]
    n_1 = R[src]            # == trace[1][0]
                            # n == trace[1][1] 
        
    pc = n
        
    # rule1 = program[pc] == trace[0]
    rule1 = 1
    rule2 = R[src] == trace[1][0]
    rule3 = n == trace[1][1]
    rule4 = n_1 > 0
    
    if trace == None or trace == []:
        return fun_empty()
    elif rule1 and rule2 and rule3 and rule4:
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()

def fun_bgtz_l(src, n):
    global pc, R, S, program, trace
    cmd = Bgtz(src, n)
    program[pc] = cmd       # == trace[0]
    n_1 = R[src]            # == trace[1][0]
    
    pc += 1
    
    # rule1 = program[pc] == trace[0]
    rule1 = 1
    rule2 = R[src] == trace[1][0]
    rule3 = n_1 <= 0
    
    if trace == None or trace == []:
        return fun_empty()
    elif rule1 and rule2 and rule3:
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()
        
def fun_load_unt(dest, src):
    global pc, R, S, program, trace
    cmd = Lw_U(src=src, dest=dest)
    program[pc] = cmd
    n_1 = R[src]            # == trace[1][0]
    n_2 = S[n_1]            # == trace[1][1]
    
    pc += 1
    R[dest] = n_2
    
    # rule1 = program[pc] == trace[0]
    rule1 = 1
    rule2 = R[src] == trace[1][0]
    rule3 = n_2 == trace[1][1]
    
    if trace == None or trace == []:
        return fun_empty()
    elif rule1 and rule2 and rule3:
        return fun_accept(R_, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()
    
def fun_load(dest, src):
    global pc, R, S, program, trace
    cmd = Lw_T(src=src, dest=dest)
    program[pc] = cmd       # == trace[0]
    n_0 = R[src]            # == trace[1][0]
    n_1 = trace[1][1]
    n_2 = S[n_0]            # == hash(n_1)
    
    pc += 1
    R[dest] = n_1
    
    # rule1 = program[pc] == trace[0]
    rule1 = 1
    rule2 = R[src] == trace[1][0]
    rule3 = n_2 == hash(n_1)
    
    if trace == None or trace == []:
        return fun_empty()
    elif rule1 and rule2 and rule3:
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()
    
def fun_store(dest, src):
    global pc, R, S, program, trace
    cmd = Sw(src=src, dest=dest)
    program[pc] = cmd       # == trace[0]
    n_0 = R[dest]           # == trace[1][0]
    n_1 = R[src]            # == trace[1][1]
    n_2 = hash(n_1)
    
    S[n_0] = n_2
    pc += 1
    
    # rule1 = program[pc] == trace[0]
    rule1 = 1
    rule2 = R[dest] == trace[1][0]
    rule3 = n_2 == trace[1][1]
    
    if trace == None or trace == []:
        return fun_empty()
    elif rule1 and rule2 and rule3:
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()
    
def fun_get(dest):
    global pc, R, S, program, trace
    cmd = Get(dest)
    program[pc] = cmd       # == trace[0]
    n = getQ[0]             # == trace[1][0]
    getQ_ = getQ[1:]
    # getQ == [n] + getQ_     #ARE WE CHECKING THIS, not sure how you could bc its the two lines above...
    
    R[dest] = n
    pc += 1
    getQ = getQ_
    
    
    # rule1 = program[pc] == trace[0]
    rule1 = 1
    rule2 = n == trace[1][0]
    rule3 = getQ == [n] + getQ_  #necessary?
    
    if trace == None or trace == []:
        return fun_empty()
    elif rule1 and rule2 and rule3:
        # R_ = R.copy()
        # R_[dest] = n
        # getQ = getQ_
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()


def fun_put(src):
    global pc, R, S, program, trace
    cmd = Put(src)
    program[pc] = cmd       # == trace[0]
    n = R[src]              # == trace[1][0]
    putQ_ = putQ + [n]      #does this need to be putQ.copy()?
    
    pc += 1
    putQ = putQ_
    
    # rule1 = program[pc] == trace[0]
    rule1 = 1
    rule2 = n == trace[1][0]
    rule3 = putQ_ == putQ + [n]
    
    if trace == None or trace == []:
        return fun_empty()
    elif rule1 and rule2 and rule3:
        # putQ_ = putQ.copy()
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()
    
def fun_alert():
    global program, pc, trace
    cmd = alert()
    program[pc] = cmd       # == trace[0]
    
    pc = 0
    
    # rule1 = program[pc] == trace[0]
    rule1 = 1
    
    # this seems very repetitive, can we do better?
    if trace == None or trace == []:
        return fun_empty()
    elif rule1:
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()

    
def fun_returnn():
    global program, pc, trace
    cmd = returnn()
    program[pc] = cmd       # == trace[0]
    
    # rule1 = program[pc] == trace[0]
    rule1 = 1
    
    if trace == None or trace == []:
        return fun_empty()
    elif rule1:
        # pass
        return fun_accept(R, S, trace, putQ, getQ, pc)
    else:
        return fun_reject()   
        
    # TODO: PC done?
    


    
def print_program():
    print(f"sentry\tpc: {pc-1}\tR[]: {' '.join(map(str, R))}")

def parse_trace():
    global trace

    trace = read_trace()
    ret = 1
    if trace[0].command == "add":
        ret = fun_add(trace[0].dest, trace[0].src, trace[0].temp)
    elif trace[0].command == "addi":
        ret = fun_addi(trace[0].dest, trace[0].src, trace[0].n_1)
    elif trace[0].command == "sub":
        ret = fun_sub(trace[0].dest, trace[0].src, trace[0].temp)
    elif trace[0].command == "jump":
        ret = fun_jump(trace[0].n)
    elif trace[0].command == "bgtz":
        if trace[0].n > 0:
            ret = fun_bgtz_g(trace[0].src, trace[0].n)
        else:
            ret = fun_bgtz_l(trace[0].src, trace[0].n)
    elif trace[0].command == "sw":
        ret = fun_store(trace[0].dest, trace[0].src)
    elif trace[0].command == "lw_U":
        ret = fun_load_unt(trace[0].dest, trace[0].src)
    elif trace[0].command == "lw_T":
        ret = fun_load(trace[0].dest, trace[0].src)
    elif trace[0].command == "get":
        ret = fun_get(trace[0].dest)
    elif trace[0].command == "put":
        ret = fun_put(trace[0].src)
    elif trace[0].command == "alert":
        ret = fun_alert()
    elif trace[0].command == "returnn":
        ret = fun_returnn()
    else:
        raise ValueError(f"Unknown command: {trace[0].command}")

    print_program()
    return ret

def evil():
    R[5] = 500

def main():
    global S, R, pc

    print("hi sentry")
    
    R[1] = 1
    R[2] = 2
    R[3] = 3
    
    parse_trace()
    
    print_program()

    return 0

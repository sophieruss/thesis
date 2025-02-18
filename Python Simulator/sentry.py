#  TODO: might be a fundamental problem where I am setting this equal, and instead it should just be checking these "rules" are true?

from commands import Add, Addi, Sub, Jump, Bgtz, Lw_U, Lw_T, Sw, Get, Put, alert, returnn
from trace_file import read_trace

class sentry:
    def __init__(self): 
        self.pc = 0                     # pc
        self.r = [0] * 32               # registers r -> X
        self.R = [0] * 32               # register file r -> Z
                                        # hash()
        self.S = {}                     # hash storage Z -> Z
        self.program = {}
        self.getQ = []
        self.putQ = []
        self.trace = None               # (command, [n0, n1, ...])

        # assumption
        self.S[0] = 0

    def fun_accept(self): 
        return 1  
        
    def fun_reject(self):
        self.pc = -1
        print("rejected")
        return 0
        
    def fun_empty(self):
        self.pc += 1                    # TODO: is this correct?
        return 2


    def fun_add(self, dest, src, temp):
            
        cmd = Add(dest, src, temp)
        self.program[self.pc] = cmd     # == trace[0]
        n_0 = self.R[src]               # == trace[1][0]   val at src       
        n_1 = self.R[temp]              # == trace[1][1]   val at tmp
        n_2 = n_0 + n_1                 # == trace[1][2]   val at dest
        
        
        # rule1 = self.program[self.pc] == trace[0]     # check cmd, dest, src, temp - but also I literally got it from trace ?? 
        rule1 = True
        rule2 = n_0 == self.trace[1][0]
        rule3 = n_1 == self.trace[1][1]                 # false bc hasnt updated calculation
        rule4 = n_2 == self.trace[1][2]
            
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1 and rule2 and rule3 and rule4:
            self.R[dest] = n_2                          # put here?  
            self.pc += 1
            return self.fun_accept()
        else:
            return self.fun_reject()

    def fun_addi(self, dest, src, n_1):
        
        cmd = Addi(dest, src, n_1)
        self.program[self.pc] = cmd     # == trace[0]
        n_0 = self.R[src]               # == trace[1][0] 
        n_2 = n_0 + n_1                 # == trace[1][1] 
        
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1
        rule2 = n_0 == self.trace[1][0]
        rule3 = n_2 == self.trace[1][1]
        
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1 and rule2 and rule3:
            self.pc += 1
            self.R[dest] = n_2  
            return self.fun_accept()
        else:
            return self.fun_reject()

    def fun_sub(self, dest, src, temp):
        
        cmd = Sub(dest, src, temp)
        self.program[self.pc] = cmd     # == trace[0]
        n_0 = self.R[src]               # == trace[1][0]
        n_1 = self.R[temp]              # == trace[1][1]
        n_2 = n_0 - n_1                 # == trace[1][2]
        
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1
        rule2 = n_0 == self.trace[1][0]
        rule3 = n_2 == self.trace[1][2]
        
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1 and rule2 and rule3:
            self.pc += 1
            self.R[dest] = n_2
            return self.fun_accept()
        else:
            return self.fun_reject()

    def fun_jump(self, n):
        cmd = Jump(n)
        self.program[self.pc] = cmd     # == trace[0]
                
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1

        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1:
            self.pc = n
            return self.fun_accept()
        else:
            return self.fun_reject()


    def fun_bgtz_g(self, src, n):
        cmd = Bgtz(src, n)
        self.program[self.pc] = cmd     # == trace[0]
        n_1 = self.R[src]               # == trace[1][0]
                                        # n == trace[1][1] 
                        
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1
        rule2 = n_1 == self.trace[1][0]
        rule3 = n == self.trace[1][1]
        rule4 = n_1 > 0
        
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1 and rule2 and rule3 and rule4:
            self.pc = n
            return self.fun_accept()
        else:
            return self.fun_reject()

    def fun_bgtz_l(self, src, n):
        cmd = Bgtz(src, n)
        self.program[self.pc] = cmd     # == trace[0]
        n_1 = self.R[src]               # == trace[1][0]
                
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1
        rule2 = n_1 == self.trace[1][0]
        rule3 = n_1 <= 0
        
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1 and rule2 and rule3:
            self.pc += 1
            return self.fun_accept()
        else:
            return self.fun_reject()
            
    def fun_load_unt(self, dest, src):
        cmd = Lw_U(src=src, dest=dest)
        self.program[self.pc] = cmd
        n_1 = self.R[src]               # == trace[1][0]
        n_2 = self.S[n_1]               # == trace[1][1]
        
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1
        rule2 = n_1 == self.trace[1][0]
        rule3 = n_2 == self.trace[1][1]
        
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1 and rule2 and rule3:
            self.pc += 1
            self.R[dest] = n_2
            return self.fun_accept()
        else:
            return self.fun_reject()
        
    def fun_load(self, dest, src):
        cmd = Lw_T(src=src, dest=dest)
        self.program[self.pc] = cmd     # == trace[0]
        n_0 = self.R[src]               # == trace[1][0]
        n_1 = self.trace[1][1]
        n_2 = self.S[n_0]               # == hash(n_1)
        
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1
        rule2 = n_0 == self.trace[1][0]
        rule3 = n_2 == hash(n_1)
        
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1 and rule2 and rule3:
            self.pc += 1
            self.R[dest] = n_1
            return self.fun_accept()
        else:
            return self.fun_reject()
        
    def fun_store(self, dest, src):
        cmd = Sw(src=src, dest=dest)
        self.program[self.pc] = cmd     # == trace[0]
        n_0 = self.R[dest]              # == trace[1][0]
        n_1 = self.R[src]               # == trace[1][1]
        n_2 = hash(n_1)
        
        
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1
        rule2 = n_0 == self.trace[1][0]
        rule3 = n_2 == self.trace[1][1]
        
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1 and rule2 and rule3:
            self.S[n_0] = n_2
            self.pc += 1
            return self.fun_accept()
        else:
            return self.fun_reject()
        
    def fun_get(self, dest):
        cmd = Get(dest)
        self.program[self.pc] = cmd     # == trace[0]
        n = self.getQ[0]                # == trace[1][0]
        getQ_ = self.getQ[1:]
        
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1
        rule2 = n == self.trace[1][0]
        
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1 and rule2:
            self.R[dest] = n
            self.pc += 1
            self.getQ = getQ_
            return self.fun_accept()
        else:
            return self.fun_reject()


    def fun_put(self, src):
        cmd = Put(src)
        self.program[self.pc] = cmd     # == trace[0]
        n = self.R[src]                 # == trace[1][0]
        
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1
        rule2 = n == self.trace[1][0]
        
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1 and rule2:
            self.pc += 1
            self.putQ = self.putQ + [n]
            return self.fun_accept()
        else:
            return self.fun_reject()
        
    # TODO: Should this go to reject? What should pc be?
    def fun_alert(self):
        cmd = alert()
        self.program[self.pc] = cmd       # == trace[0]
        # self.pc = 0 infinite loop issue
        self.pc = -1
        
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1
        
        # this seems very repetitive, can we do better?
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1:
            return self.fun_accept()
        else:
            return self.fun_reject()

    # TODO: What to do with pc, so that it doesnt step off, doesnt infinite loop, stops
    def fun_returnn(self):
        cmd = returnn()
        self.program[self.pc] = cmd     # == trace[0]
        
        # rule1 = self.program[pc] == trace[0]
        rule1 = 1
        
        if self.trace == None or self.trace == []:
            return self.fun_empty()
        elif rule1:
            self.pc = -1                             # wrong, but now it stops (no infinite loop)
            return self.fun_accept()
        else:
            return self.fun_reject()   
            
        # TODO: PC done?
        
    def evil(self):
        self.R[5] = 500
        self.R[2] = 10
    
    def print_program(self):
        print(f"sentry\tpc: {self.pc}\tR[]: {' '.join(map(str, self.R))}")

def parse_trace(self):

    self.trace = read_trace()
    ret = 1
    if self.trace[0].command == "add":
        ret = self.fun_add(self.trace[0].dest, self.trace[0].src, self.trace[0].temp)
    elif self.trace[0].command == "addi":
        ret = self.fun_addi(self.trace[0].dest, self.trace[0].src, self.trace[0].n_1)
    elif self.trace[0].command == "sub":
        ret = self.fun_sub(self.trace[0].dest, self.trace[0].src, self.trace[0].temp)
    elif self.trace[0].command == "jump":
        ret = self.fun_jump(self.trace[0].n)
    elif self.trace[0].command == "bgtz":
        if self.R[self.trace[0].src] > 0:
            ret = self.fun_bgtz_g(self.trace[0].src, self.trace[0].n)
        else:
            ret = self.fun_bgtz_l(self.trace[0].src, self.trace[0].n)
    elif self.trace[0].command == "sw":
        ret = self.fun_store(self.trace[0].dest, self.trace[0].src)
    elif self.trace[0].command == "lw_U":
        ret = self.fun_load_unt(self.trace[0].dest, self.trace[0].src)
    elif self.trace[0].command == "lw_T":
        ret = self.fun_load(self.trace[0].dest, self.trace[0].src)
    elif self.trace[0].command == "get":
        ret = self.fun_get(self.trace[0].dest)
    elif self.trace[0].command == "put":
        ret = self.fun_put(self.trace[0].src)
    elif self.trace[0].command == "alert":
        ret = self.fun_alert()
    elif self.trace[0].command == "returnn":
        ret = self.fun_returnn()
    else:
        raise ValueError(f"Unknown command: {self.trace[0].command}")

    self.print_program()
    return ret

def main():
    s = sentry()

    print("hi sentry")
    
    s.R[1] = 1
    s.R[2] = 2
    s.R[3] = 3
    
    parse_trace(s)
    
    s.print_program()

    return 0
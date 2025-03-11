import json
    
from commands import Add, Addi, Sub, Jump, Bgtz, Sw, Lw_U, Lw_T, Get, Put, trustedMode, untrustedMode, alert, returnn
from trace_file import send_trace


class host:
    def __init__(self): 
        self.pc = 0          # pc
        self.r = [0] * 32    # registers r -> X
        self.R = [0] * 32    # register file r -> Z
        self.M = {}          # memory
        self.S = 0           # mode bit
        self.program = {}    # Z -> commands
        self.getQ = []
        self.trace = []   

        # assumption
        self.M[0] = 0

    # state, program -> state
    def fun_add(self, dest, src, temp):
        cmd = Add(dest, src, temp)
        self.program[self.pc] = cmd
        n_0 = self.R[src]
        n_1 = self.R[temp]
        n_2 = n_0 + n_1
        if self.S == 1:
            self.trace = [self.program[self.pc], n_0, n_1, n_2]
            
            # ok these two lines are allegedly after trace logic - ask!
            self.R[dest] = n_2
            self.pc += 1
        else:
            self.trace = []
        return send_trace(self.trace)
        

    def fun_addi(self, dest, src, n_1):
        cmd = Addi(dest, src, n_1)
        self.program[self.pc] = cmd
        n_0 = self.R[src]
        n_2 = n_0 + n_1
        if self.S == 1:
            self.trace = [self.program[self.pc], n_0, n_2]
            self.R[dest] = n_2
            self.pc += 1
        else:
            self.trace = []
        return send_trace(self.trace)


    def fun_sub(self, dest, src, temp):
        cmd = Sub(dest, src, temp)
        self.program[self.pc] = cmd
        n_0 = self.R[src]
        n_1 = self.R[temp]
        n_2 = n_0 - n_1
        if self.S == 1:
            self.trace = [self.program[self.pc], n_0, n_1, n_2]
            self.R[dest] = n_2
            self.pc += 1
        else:
            self.trace = []
        return send_trace(self.trace)

            
    def fun_jump(self, n):
        cmd = Jump(n)
        self.program[self.pc] = cmd
        if self.S == 1:
            self.trace = [self.program[self.pc], n]
            self.pc = n

        else:
            self.trace = []
        return send_trace(self.trace)


    def fun_bgtz_g(self, src, n):
        cmd = Bgtz(src, n)
        self.program[self.pc] = cmd
        n_1 = self.R[src]
        if self.S == 1 and n_1 > 0:
            self.trace = [self.program[self.pc], n_1, n]
            self.pc = n

        else:
            self.trace = []
        return send_trace(self.trace)


    def fun_bgtz_l(self, src, n):
        cmd = Bgtz(src, n)
        self.program[self.pc] = cmd
        n_1 = self.R[src]
        if self.S == 1 and n_1 <= 0:
            self.trace = [self.program[self.pc], n_1, self.pc+1]
            self.pc += 1
        return send_trace(self.trace)

            
    def fun_load_unt(self, src, dest):
        cmd = Lw_U(src, dest)
        self.program[self.pc] = cmd
        n_0 = self.R[src]
        n_1 = self.M[n_0]
        if self.S == 1:
            self.trace = [self.program[self.pc], n_1, self.pc+1]
            self.R[dest] = n_1
            self.pc += 1
        else:
            self.trace = []
        return send_trace(self.trace)


    def fun_load(self, src, dest):
        self.S = 1
        
        cmd = Lw_T(src, dest)
        self.program[self.pc] = cmd
        n_0 = self.R[src]
        n_1 = self.M[n_0]
        if self.S == 1:
            self.trace = [self.program[self.pc], n_0, n_1]
            self.R[dest] = n_1
            self.pc += 1
        else:
            self.trace = []
        return send_trace(self.trace)

            
    def fun_store(self, src, dest):
        cmd = Sw(src, dest)
        self.program[self.pc] = cmd
        n_0 = self.R[dest]
        n_1 = self.R[src]
        if self.S == 1:
            self.trace = [self.program[self.pc], n_0, n_1]
            self.M[n_0] = n_1
            self.pc += 1
        else:
            self.trace = []
        return send_trace(self.trace)
            
    def fun_get(self, dest):
        cmd = Get(dest)
        self.program[self.pc] = cmd
        
        self.n = -1              # how to get n????
        getQ_0 = self.getQ + [self.n]   # does :: mean add it to queue?
        
        if self.S == 1:
            self.trace = [self.program[self.pc], self.n]
            self.R[dest] = self.n
            self.getQ = getQ_0
            self.pc += 1
        else:
            self.trace = []
        return send_trace(self.trace)
        
    def fun_put(self, src):
        cmd = Put(src)
        self.program[self.pc] = cmd
        
        self.n = self.R[src]
        if self.S == 1:
            self.trace = [self.program[self.pc], self.n]
            self.pc += 1
        else:
            self.trace = []
        return send_trace(self.trace)
        
    def fun_enable(self):
        cmd = trustedMode()
        self.program[self.pc] = cmd
        self.S = 1
        self.pc += 1

    def fun_disable(self):
        cmd = untrustedMode()
        self.program[self.pc] = cmd
        self.S = 0
        self.pc += 1

    def fun_alert(self):
        cmd = alert()
        self.program[self.pc] = cmd
        if self.S == 1:
            self.trace = [self.program[self.pc]]
        return send_trace(self.trace)

    def fun_returnn(self):
        cmd = returnn()
        self.program[self.pc] = cmd
        if self.S == 1:
            self.trace = [self.program[self.pc]]
            self.pc = -1                             # wrong, but now it stops (no infinite loop)
        return send_trace(self.trace)

    def print_program(self):
        print(f"host\tpc: {self.pc}\tR[]: {' '.join(map(str, self.R))}")

    
def parse_command(host, cmd):
    if cmd[0] == "Add":
        host.fun_add(cmd[1], cmd[2], cmd[3])
    elif cmd[0] == "Addi":
        host.fun_addi(cmd[1], cmd[2], cmd[3])
    elif cmd[0] == "Sub":
        host.fun_sub(cmd[1], cmd[2], cmd[3])
    elif cmd[0] == "Jump":
        host.fun_jump(cmd[1])
    elif cmd[0] == "Bgtz":
        if host.R[cmd[1]] > 0:
            host.fun_bgtz_g(cmd[1], cmd[2])
        else:
            host.fun_bgtz_l(cmd[1], cmd[2])
    elif cmd[0] == "Sw":
        host.fun_store(cmd[1], cmd[2])
    elif cmd[0] == "Lw_U":
        host.fun_load_unt(cmd[1], cmd[2])
    elif cmd[0] == "Lw_T":
        host.fun_load(cmd[1], cmd[2])
    elif cmd[0] == "Get":
        host.fun_get(cmd[1])
    elif cmd[0] == "Put":
        host.fun_put(cmd[1])
    elif cmd[0] == "trustedMode":
        host.fun_enable()
    elif cmd[0] == "untrustedMode":
        host.fun_disable()
    elif cmd[0] == "alert":
        host.fun_alert()
    elif cmd[0] == "returnn":
        host.fun_returnn()
    else:
        raise ValueError(f"Unknown command: {cmd[0]}")
    host.print_program()
    return 1


def main():
    
    with open('Python Simulator/programs/trace_history.json', 'w') as f:
        f.write('')
    print("hello host")
    
    h = host()  

    h.S = 1
    h.R[1] = 1
    h.R[2] = 2
    h.R[3] = 3
    
    h.print_program()

    h.fun_add(1, 2, 3)
    # fun_addi(4, 1, 5)
    # # fun_jump(0)
    # fun_sub(1, 4, 3)
    h.print_program()

    return 0

pc = 0          # pc
r = [0] * 32    # registers r -> X
R = [0] * 32    # register file r -> Z
                # hash()
M = {}          # hash storage Z -> Z


program = {}

from commands import Add, Addi, Sub, Jump, Bgtz


def fun_add(dest, src, temp):
    global pc, R, S, program
    cmd = Add(dest, src, temp)
    program[pc] = cmd
    n_0 = R[src]
    n_1 = R[temp]
    n_2 = n_0 + n_1
    
    R[dest] = n_2
    pc += 1

def fun_addi(dest, src, n_1):
    global pc, R, S, program
    cmd = Addi(dest, src, n_1)
    program[pc] = cmd
    n_0 = R[src]
    n_2 = n_0 + n_1

    R[dest] = n_2
    pc += 1

def fun_sub(dest, src, temp):
    global pc, R, S, program
    cmd = Sub(dest, src, temp)
    program[pc] = cmd
    n_0 = R[src]
    n_1 = R[temp]
    n_2 = n_0 - n_1

    R[dest] = n_2
    pc += 1

def fun_jump(n):
    global pc, program, S
    cmd = Jump(n)
    program[pc] = cmd

    pc = n

def fun_bgtz_g(src, n):
    global pc, R, S, program
    cmd = Bgtz(src, n)
    program[pc] = cmd
    n_1 = R[src]
    if n_1 > 0:
        pc = n

def fun_bgtz_l(src, n):
    global pc, R, S, program
    cmd = Bgtz(src, n)
    program[pc] = cmd
    n_1 = R[src]
    if n_1 <= 0:
        pc += 1


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
    
    print_program()

    fun_add(1, 2, 3)
    
    print_program()

    return 0

main()

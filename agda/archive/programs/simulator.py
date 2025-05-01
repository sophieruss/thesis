INPUT = "Python Simulator/programs/basic_loop.csv"
# INPUT = "Python Simulator/programs/fib.csv"
OUTPUT = 'Agda/archive/programs/outputs/OUT.agda'
firstline = OUTPUT.replace('/', '.').replace('.agda', '')
from dataclasses import dataclass
from typing import List, Optional, NamedTuple

# Initialize empty registers (32 zeros)
empty_reg = [0] * 32

# Initialize arrays with None (size 100)
program = [None] * 100
# registers = [None] * 100
traces = [None] * 100
pcs = [None] * 100
states = [None] * 100
num_states = 0  # Number of states processed

@dataclass
class State:
    pc: int
    registers: List[int]
    mode: bool
    UR: int
    SR: List[int]
    ret_pc: int

    @classmethod
    def create(cls, pc: int, registers: List[int], mode: bool, UR: int, SR: List[int], ret_pc: int) -> 'State':
        if len(registers) != 32 or len(SR) != 32:
            raise ValueError("Registers must have exactly 32 elements")
        return cls(pc, registers.copy(), mode, UR, SR.copy(), ret_pc)

def agdaList(oldlist):
    new = ' ∷ '.join(str(x) for x in oldlist)
    return new + ' ∷ []'

def helper(line, pc):
    global program, traces, pcs, states, num_states  # Declare globals
    next_pc = pc+1 # default next_pc is pc + 1
    prog, trace = None, None
    prev_reg = empty_reg.copy() # default register is empty_reg
    if states[num_states-1]:
        prev_reg = states[num_states-1].registers.copy()
    reg = prev_reg.copy()  # copy previous registers

    mode, ur, srs, retpc = None , None , None, None # default values

    match (line[0]):
        case 'Add':
            a = int(line[1])
            b = int(line[2])
            c = int(line[3])
            prog = f"Add (# {a}) (# {b}) (# {c})"
            sum =  prev_reg[b] + prev_reg[c]
            reg[a] = sum
            trace = f"⟨ {prog} , {prev_reg[b]} ∷ {prev_reg[c]} ∷ {reg[a]} ∷ [] ⟩"
                    
        case 'Sub':
            a = int(line[1])
            b = int(line[2])
            c = int(line[3])
            prog = f"Sub (# {a}) (# {b}) (# {c})"
            reg[a] = prev_reg[b] - prev_reg[c]
            trace = f"⟨ {prog} , {prev_reg[b]} ∷ {prev_reg[c]} ∷ {reg[a]} ∷ [] ⟩"
        
        case 'Addi':
            a = int(line[1])
            b = int(line[2])
            c = int(line[3])
            prog =  f"Addi (# {a}) (# {b}) {c}"
            reg[a] = prev_reg[b] + c
            trace = f"⟨ {prog} , {prev_reg[b]} ∷ {reg[a]} ∷ 0 ∷ [] ⟩"

        case "Jump":
            a = int(line[1])
            prog = f"Jump {line[1]}"
            trace = f"⟨ {prog} , {a} ∷ 0 ∷ 0 ∷ [] ⟩"
            next_pc = int(line[1])
            
        case "Bgtz":
            reg = prev_reg.copy()
            prog = f"Bgtz (# {line[1]}) {line[2]}"
            if (prev_reg[int(line[1])] > 0):
                next_pc = int(line[2])
                trace = f"⟨ {prog} , {prev_reg[int(line[1])]} ∷ {int(line[2])} ∷ 0 ∷ [] ⟩"
            else:
                trace = f"⟨ {prog} , {prev_reg[int(line[1])]} ∷ {pc+1} ∷ 0 ∷ [] ⟩"     
                

        case "Call-Unt":
            reg = prev_reg.copy()
            prog = f"Call-Unt {line[1]}"
            trace = f"⟨ Call-Unt-Sentry , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
            next_pc = int(line[1])
            mode = False # change mode to false
            srs = prev_reg.copy()
            retpc = pc + 1 # save the return pc
            
        case "Return-Unt":
            reg = prev_reg.copy() #change
            prog = f"Return-Unt"
            trace = f"⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
            mode = True # change mode to true
            
        case "Return":
            reg = prev_reg.copy()
            prog = "Return"
            trace = "⟨ Return , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
            
        case "Alert":
            reg = prev_reg.copy()
            prog = "Alert"
            trace = "⟨ Alert , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
            
        case "Load-UR":
            dest = int(line[1])
            reg = prev_reg.copy()
            prog = f"Load-UR (# {dest})"
            trace = f"⟨ Load-UR (# {dest}) , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
            ur = prev_reg[dest]

        case "Put-UR":
            reg = prev_reg.copy()
            prog = f"Put-UR (# {int(line[1])})"
            trace = f"⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
            
        case "NoOp":
            prog = "NoOp"
            trace = "⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
                       
        case _:
                prog = "NoOp"
                trace = "⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
         
    # print("---------")
    # print(f"Line: {line}, PC: {pc}, Next PC: {next_pc}, Program: {prog}, Trace: {trace}")   
    # print(states[pc-1])
    if states[num_states-1]:
        states[num_states] = State.create(next_pc, reg, mode if mode is not None else states[pc-1].mode, ur if ur is not None else states[pc-1].UR, srs if srs is not None else states[pc-1].SR, retpc if retpc is not None else states[pc-1].ret_pc)
    else:
        states[0] = State.create(next_pc, reg, True, 0, empty_reg, 0) # first state is always true mode

    # print('Processing line:', pc, '->', line)
    # print(states)
    return prog, trace, next_pc

def proof_helper(prog, stateA, trace):
    match prog.split()[0]:
        case 'Add':
            return f"step-Add prog state-{stateA} ? refl ?"
        case 'Sub':
            return f"step-Sub prog state-{stateA} ? refl ?"
        case 'Addi':
            return f"step-Addi prog state-{stateA} ? refl ?"
        case 'Jump':
            return f"step-Jump prog state-{stateA} ? ? refl ?"
        case 'Bgtz':
            if (int(trace.split()[6]) > 0):
                return f"step-Bgtz-g prog state-{stateA} ? ? refl ?"
            return f"step-Bgtz-l prog state-{stateA} ? ? refl ?"
        # case 'Enable':
        #     return f"step-Enable prog state-{stateA} ? refl"
        # case 'Disable':
            return f"step-Disable prog state-{stateA} ? refl"
        case 'Call-Unt':
            return f"step-Call-Unt prog state-{stateA} ? ? ? refl ?"
        # case 'Call-Unt-Sentry':
        #     return f"step-Call-Unt-Sentry ?"
        case 'Return-Unt':
            return f"step-Ret-Unt prog state-{stateA} ? ? ? refl"
        case 'Return':
            return f"step-Return prog state-{stateA} ? refl"
        case 'Alert':
            return f"step-Alert prog state-{stateA} ? refl"
        case 'Load-UR':
            return f"step-Load-UR prog state-{stateA} ? refl ?"
        case 'Put-UR':
            return f"step-Put-UR prog state-{stateA} ? refl ? ? ?"
        # case Load-UR-Sentry
        case _:
            return f"step-NoOp prog state-{stateA} ? refl refl"
           

def readfile():    
    with open(INPUT, 'r') as f:
        lines = []
        for line in f:
            if line.strip() == '':
                break
            lines.append(line)
        return lines

def main():
    
    global program, traces, pcs, states, num_states  # Declare globals
    num_states = 0  # not the number of instruction(could be >), because we could loop
    f = readfile()
    
    empty_state = State.create(0, empty_reg, True, 0, empty_reg, 0)
    
    i = 0
    while i < len(f) and num_states < 50:
        line = f[i]

        if line[0] == '#':
            break
        if line == '\n':
            continue
        line = line.split()
        # prev_state = empty_state 
        # if (num_states>0):
        #     prev_state = states[num_states-1]
        
        # a, b, c = helper(line, i)
        # if (a is None or b is None or c == -1):
        #     print(f"Error processing line {i}: {line}")
        #     i +=1
        # else:
        program[num_states], traces[num_states], next_pc = helper(line, i)
        pcs[num_states] = i
        # i +=1
        i = next_pc
        # if next_pc != -1:
        #     # i = next_pc
        #     i = next_pc # need to increment this bc its one off for some reason
        # else:
        #     i = i + 1 # increment pc!
        num_states += 1 
        
        # i = i + 1
        # num_states += 1 
        
        # if next_pc != -1:
        #     i = next_pc + 1 # need to increment this bc its one off for some reason
        # else:
        #     i = i + 1 # increment pc!
        
        print ("~\t\t ", i , num_states)       

        
        
    print("Program has " + str(len(program)) + " instructions")
    # print("Program has " + str(len(registers)) + " registers")
    print("Program has " + str(len(traces)) + " traces")
    print("Program has " + str(len(pcs)) + " pcs")
    print("Program has " + str(num_states) + " states")
    print(states[:num_states])

    program = program[:num_states]
    registers = [empty_reg] + [states[i].registers for i in range(num_states-1)]
    # registers = [states[i].registers for i in range(num_states)]

    # remove last register (we wouldnt use it?), and add the starting state
    traces = traces[:num_states]
    pcs = pcs[:num_states]
           
    states = states[:num_states]
    
        
    with open(OUTPUT, 'w') as f:
        f.write("module " + firstline + " where\n" +
                "open import agda.commands\n" +
                "open import agda.host  renaming (State to Hstate)\n" +
                "open import agda.sentry\n" +
                "open import Data.Nat using (ℕ; compare; _≤_; _≥_;  _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )\n" +
                "open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)\n" +
                "open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)\n" +
                "open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)\n" +
                "open import Relation.Nullary using (¬_; contradiction; yes; no)\n" +
                "open import Data.Empty using (⊥; ⊥-elim)\n" +
                "open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; _≥?_)\n" +
                "open import Function.Base using (flip)\n" +
                "open import Data.Product using (∃; ∃-syntax; _×_; _,_; Σ)\n" +
                "open import Data.Bool using (Bool; true; false; if_then_else_)\n" +
                "open import Agda.Builtin.List\n\n" +
                
                "proj : Hstate → State\n" +
                "proj [[ pc , registers , mode , UR , SR , ret-pc ]] = [ pc , registers ]\n")
        
        f.write(f"prog : Program {len(registers)}\n")
        f.write(f"prog = program ({agdaList(program)})\n")
        
        for i in range(0, len(registers)):
            f.write(f"r-{i} ")
        f.write(" : Vec ℕ 32\n")
        
        for i in range(0, len(registers)):
            f.write(f"r-{i} = {agdaList(registers[i])}\n")
        
        
        
        for i in range(0, len(traces)):
            # f.write(f"state-{i} = [[ {states[i].pc} , r-{i} , {states[i].mode} , {states[i].UR} , agdalist(states[i].SR) , {states[i].ret_pc} ]]\n")
            f.write(f"state-{i} = [[ {pcs[i]} , r-{i} , {str(states[i].mode).lower()} , {states[i].UR} , r-0 , {states[i].ret_pc} ]]\n")

        for i in range(0, len(registers)):
            f.write(f"τ-{i} ")
        f.write(" : Trace\n") 
            
        for i in range(0, len(traces)):
            f.write(f"τ-{i} = {traces[i]} \n")
            
        for i in range(0, len(traces)-1):
            f.write(f"{i}→{i+1} : prog , state-{i} —→ state-{i+1} , τ-{i}\n")
            proof = proof_helper(program[i], i, traces[i])
            f.write(f"{i}→{i+1} = {proof}\n")
            
    print("Yay!!! Agda program (with holes) is in `" + OUTPUT + "`")

main()



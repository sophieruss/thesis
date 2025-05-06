# --------------------------
# Configuration and Constants
# --------------------------
INPUT = "Agda/proofs/example.csv"
OUTPUT = 'Agda/proofs/OUTPUT.agda'
MAX_STATES = 12
firstline = OUTPUT.replace('/', '.').replace('.agda', '')

from dataclasses import dataclass
from typing import List, Optional, NamedTuple

# --------------------------
# Data Structures
# --------------------------
@dataclass
class State:
    pc: int
    registers: List[int]
    mode: bool
    UR: int
    SR: int             # reg list has already been made, just label it
    ret_pc: int

    @classmethod
    def create(cls, pc: int, registers: List[int], mode: bool, UR: int, SR: int, ret_pc: int) -> 'State':
        if len(registers) != 32:
            raise ValueError("Registers must have exactly 32 elements")
        return cls(pc, registers.copy(), mode, UR, SR, ret_pc)
    
    
# Initialize empty registers (32 zeros)
empty_reg = [0] * 32

# Initialize arrays with None (size 100)
program = [None] * 100
traces = [None] * 100
pcs = [None] * 100
states = [None] * 100
num_states = 0  # Number of states processed
# next_mode = True  # Initial mode for the first state
next_state = State.create(0, empty_reg, True, 0, 0, 0) # Initial state for the first instruction
trusted_state_restore = State.create(0, empty_reg, True, 0, 0, 0) # State for untrusted instructions

# --------------------------
# Helper Functions
# --------------------------
def agdaList(oldlist):
    """Convert Python list to Agda list format"""
    new = ' ∷ '.join(str(x) for x in oldlist)
    return new + ' ∷ []'

def helper(line, pc):
    """Process a single instruction line and return program, trace, and next PC"""
    global program, traces, pcs, states, num_states, next_state, trusted_state_restore
    
    # Default values
    next_pc = pc + 1
    prog, trace = None, None
    prev_reg = empty_reg.copy()
    
    if states[num_states-1]:
        prev_reg = states[num_states-1].registers.copy()
    
    reg = prev_reg.copy()
    mode = next_state.mode
    ur = next_state.UR
    srs = next_state.SR
    retpc = next_state.ret_pc

    # Process different instruction types
    match (line[0]):
        case 'Add':
            a, b, c = int(line[1]), int(line[2]), int(line[3])
            prog = f"Add (# {a}) (# {b}) (# {c})"
            reg[a] = prev_reg[b] + prev_reg[c]
            trace = f"⟨ {prog} , {prev_reg[b]} ∷ {prev_reg[c]} ∷ {reg[a]} ∷ [] ⟩"
                    
        case 'Sub':
            a, b, c = int(line[1]), int(line[2]), int(line[3])
            prog = f"Sub (# {a}) (# {b}) (# {c})"
            reg[a] = prev_reg[b] - prev_reg[c]
            trace = f"⟨ {prog} , {prev_reg[b]} ∷ {prev_reg[c]} ∷ {reg[a]} ∷ [] ⟩"
        
        case 'Addi':
            a, b, c = int(line[1]), int(line[2]), int(line[3])
            prog = f"Addi (# {a}) (# {b}) {c}"
            reg[a] = prev_reg[b] + c
            trace = f"⟨ {prog} , {prev_reg[b]} ∷ {reg[a]} ∷ 0 ∷ [] ⟩"

        case "Jump":
            next_pc = int(line[1])
            prog = f"Jump {line[1]}"
            trace = f"⟨ {prog} , {next_pc} ∷ 0 ∷ 0 ∷ [] ⟩"
            
        case "Bgtz":
            reg = prev_reg.copy()
            reg_idx, target = int(line[1]), int(line[2])
            prog = f"Bgtz (# {reg_idx}) {target}"
            if prev_reg[reg_idx] > 0:
                next_pc = target
                trace = f"⟨ {prog} , {prev_reg[reg_idx]} ∷ {target} ∷ 0 ∷ [] ⟩"
            else:
                trace = f"⟨ {prog} , {prev_reg[reg_idx]} ∷ {pc+1} ∷ 0 ∷ [] ⟩"
                
        case "Call-Unt":
            reg = prev_reg.copy()
            target = int(line[1])
            prog = f"Call-Unt {target}"
            trace = f"⟨ Call-Unt-Sentry , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
            next_pc = target
            
            next_state.mode = False                             
            next_state.ret_pc = pc + 1
            next_state.SR = num_states  #I think this will give previous reg state                                   
            
            
        case "Return-Unt":
            reg = states[srs].registers
            prog = "Return-Unt"
            trace = "⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
            next_state.mode = True
            next_pc = next_state.ret_pc
            
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
            reg[dest] = ur
            prog = f"Load-UR (# {dest})"
            trace = f"⟨ Load-UR (# {dest}) , {ur} ∷ 0 ∷ 0 ∷ [] ⟩"

        case "Put-UR":
            reg = prev_reg.copy()
            prog = f"Put-UR (# {int(line[1])})"
            trace = "⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
            next_state.UR = reg[int(line[1])]
            
        case "NoOp":
            prog = "NoOp"
            trace = "⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
                       
        case _:
            prog = "NoOp"
            trace = "⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
    
    if mode is False:
        trace = "⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩"

    # Update state
    if states[num_states-1]:
        states[num_states] = State.create(
            next_pc, 
            reg, 
            mode if mode is not None else states[num_states-1].mode,
            ur if ur is not None else states[num_states-1].UR,
            srs if srs is not None else states[num_states-1].SR,
            retpc if retpc is not None else states[num_states-1].ret_pc
        )
    else:
        states[0] = State.create(next_pc, reg, True, 0, 0, 0)

    return prog, trace, next_pc

def proof_helper(prog, stateA, trace):
    """Generate Agda proof steps for different instructions"""
    match prog.split()[0]:
        case 'Add': return f"step-Add prog state-{stateA} ? refl ?"
        case 'Sub': return f"step-Sub prog state-{stateA} ? refl ?"
        case 'Addi': return f"step-Addi prog state-{stateA} ? refl ?"
        case 'Jump': return f"step-Jump prog state-{stateA} ? ? refl ?"
        case 'Bgtz':
            return (f"step-Bgtz-g prog state-{stateA} ? refl refl ?" 
                   if int(trace.split()[6]) > 0 else 
                   f"step-Bgtz-l prog state-{stateA} ? refl refl ?")
        case 'Call-Unt': return f"step-Call-Unt prog state-{stateA} ? ? refl refl ?"
        case 'Return-Unt': return f"step-Ret-Unt prog state-{stateA} ? ? refl refl"
        case 'Return': return f"step-Return prog state-{stateA} ? refl"
        case 'Alert': return f"step-Alert prog state-{stateA} ? refl"
        case 'Load-UR': return f"step-Load-UR prog state-{stateA} ? refl ?"
        case 'Put-UR': return f"step-Put-UR prog state-{stateA} ? refl refl ?"
        case _: return f"step-NoOp prog state-{stateA} ? refl refl"
        
def sentry_proof_helper(prog, stateA, trace):
    """Generate Agda proof steps for different instructions"""
    match prog.split()[0]:
        case 'Add': return f"step-Add τ-{stateA} prog (proj state-{stateA}) ? refl refl ?"
        case 'Sub': return f"step-Sub τ-{stateA} prog (proj state-{stateA}) ? refl refl ?"
        case 'Addi': return f"step-Addi τ-{stateA} prog (proj state-{stateA}) ? refl refl ?"
        case 'Jump': return f"step-Jump τ-{stateA} prog (proj state-{stateA}) ? ? refl refl"
        case 'Bgtz':
            return (f"step-Bgtz-g τ-{stateA} prog (proj state-{stateA}) ? ? refl refl refl" 
                   if int(trace.split()[6]) > 0 else 
                   f"step-Bgtz-l τ-{stateA} prog (proj state-{stateA}) ? refl refl refl ?")
        case 'Call-Unt': return f"step-Call-Unt-Sentry τ-{stateA} prog (proj state-{stateA}) ? ? refl ? refl"
        # case 'Return-Unt': return f"step-Ret-Unt τ-{stateA} prog (proj state-{stateA}) ? ? refl refl"
        case 'Return': return f"step-Return τ-{stateA} prog (proj state-{stateA}) ? refl refl"
        case 'Alert': return f"step-Alert τ-{stateA} prog (proj state-{stateA}) ? refl refl"
        case 'Load-UR': return f"step-Load-UR τ-{stateA} prog (proj state-{stateA}) ? refl ? refl"
        # case 'Put-UR': return f"step-Put-UR τ-{stateA} prog (proj state-{stateA}) ? refl refl ?"
        case _: return f"step-NoOp τ-{stateA} prog (proj state-{stateA}) ? refl refl"

def readfile():    
    """Read input file and return non-empty lines"""
    with open(INPUT, 'r') as f:
        lines = []
        for line in f:
            if line.strip() == '':
                break
            lines.append(line)
        return lines

# --------------------------
# Main Program
# --------------------------
def main():
    global program, traces, pcs, states, num_states
        
    # Initialize
    num_states = 0
    f = readfile()
    empty_state = State.create(0, empty_reg, True, 0, empty_reg, 0)
    
    # Process each line
    i = 0
    while i < len(f) and num_states < MAX_STATES:
        line = f[i]

        # Skip comments and empty lines
        if line[0] == '#' or line == '\n':
            i += 1
            continue
            
        line = line.split()
        program[num_states], traces[num_states], next_pc = helper(line, i)
        pcs[num_states] = i
        i = next_pc
        num_states += 1
        

    # Finalize data arrays
    program = program[:num_states]
    registers = [empty_reg] + [states[i].registers for i in range(num_states-1)]
    traces = traces[:num_states]
    pcs = pcs[:num_states]
    states = states[:num_states]
    
    absolute_program = sorted([(pcs[i], program[i]) for i in range(num_states)], key=lambda x: x[0])
    absolute_program = [instr for _, instr in absolute_program]

    
    # Write Agda output file
    with open(OUTPUT, 'w') as f:
        # Write header
        f.write(f"module {firstline} where\n")
        f.write("""open import agda.commands
open import agda.host  renaming (State to Hstate)
open import agda.sentry
open import Data.Nat using (ℕ; compare; _≤_; _≥_;  _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)
open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)
open import Relation.Nullary using (¬_; contradiction; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; _≥?_)
open import Function.Base using (flip)
open import Data.Product using (∃; ∃-syntax; _×_; _,_; Σ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Agda.Builtin.List\n\n""")
        
        f.write("proj : Hstate → State\n")
        f.write("proj [[ pc , registers , mode , UR , SR , ret-pc ]] = [ pc , registers ]\n")
        
        # Write program definition
        f.write(f"prog : Program {len(registers)}\n")
        f.write(f"prog = program ({agdaList(absolute_program)})\n")
        
        # Write registers
        for i in range(len(registers)):
            f.write(f"r-{i} ")
        f.write(" : Vec ℕ 32\n")
        
        for i in range(len(registers)):
            f.write(f"r-{i} = {agdaList(registers[i])}\n")
        
        # Write states
        for i in range(len(traces)):
            f.write(f"state-{i} = [[ {pcs[i]} , r-{i} , {str(states[i].mode).lower()} , {states[i].UR} , r-{states[i].SR} , {states[i].ret_pc} ]]\n")

        # Write traces
        for i in range(len(traces)):
            f.write(f"τ-{i} ")
        f.write(" : Trace\n") 
            
        for i in range(len(traces)):
            f.write(f"τ-{i} = {traces[i]} \n")
            
        # Write proof steps
        for i in range(len(traces)-1):
            if i == 0 or i == len(traces)-2:  # Edge cases
                if i == 0:
                    f.write(f"-- Don't print the first step. This is a NoOp that sets up the world\n")
                    f.write(f"-- {i}→{i+1} : prog , state-{i} —→ state-{i+1} , τ-{i}\n")
                else:
                    f.write(f"-- This last step parses weird. Case by case at the moment. Double check this.\n")
                    if program[i] == ("Return") or program[i].startswith("Alert"):
                        f.write(f"{i}→{i+1} : prog , state-{i} —→ state-{i} , τ-{i}\n")
                        proof = proof_helper(program[i], i, traces[i])
                        f.write(f"{i}→{i+1} = {proof}\n")
                    else:
                        f.write(f"Maybe bad program? Does not end in Return or Alert.\n")
                        f.write(f"-- {i}→{i+1} : prog , state-{i} —→ state-{i+1} , τ-{i}\n")
                        proof = proof_helper(program[i], i, traces[i])
                        f.write(f"-- {i}→{i+1} = {proof}\n")
            else:
                f.write(f"{i}→{i+1} : prog , state-{i} —→ state-{i+1} , τ-{i}\n")
                proof = proof_helper(program[i], i, traces[i])
                f.write(f"{i}→{i+1} = {proof}\n")
            
        print(f"✔ Host Agda output written to {OUTPUT}")



        # write_sentry
        f.write(f"\n\n-- Sentry\n")
        i = 1
        while i < len(traces) - 1:
            if i == len(traces)-2:  # Edge cases
                f.write(f"-- This last step parses weird. Case by case at the moment. Double check this.\n")
                if program[i] == ("Return") or program[i].startswith("Alert"):
                    f.write(f"s_{i}→{i+1} : τ-{i} , prog , (proj state-{i}) —→ (proj state-{i})\n")
                    proof = sentry_proof_helper(program[i], i, traces[i])
                    f.write(f"s_{i}→{i+1} = {proof}\n")
                else:
                    f.write(f"Maybe bad program? Does not end in Return or Alert.\n")
                    f.write(f"-- s_{i}→{i+1} : prog , (proj state-{i}) —→ (proj state-{i+1}) , τ-{i}\n")
                    proof = sentry_proof_helper(program[i], i, traces[i])
                    f.write(f"-- s_{i}→{i+1} = {proof}\n")
                i +=1
            else:
                if program[i].startswith("Call-Unt"):
                    # Find matching Return-Unt
                    end = i + 1
                    while end < len(traces)-1 and "Return-Unt" not in program[end]:
                        end += 1
                    end += 1
                    # Write the combined step
                    f.write(f"s_{i}→{end} : τ-{i} , prog , (proj state-{i}) —→ (proj state-{end})\n")
                    proof = sentry_proof_helper(program[i], i, traces[i])
                    f.write(f"s_{i}→{end} = {proof}\n")
                    i = end
                else:
                    # Normal step
                    f.write(f"s_{i}→{i+1} : τ-{i} , prog , (proj state-{i}) —→ (proj state-{i+1})\n")
                    proof = sentry_proof_helper(program[i], i, traces[i])
                    f.write(f"s_{i}→{i+1} = {proof}\n")
                    i += 1
                
                
        print(f"✔ Sentry Agda output written to {OUTPUT}")



if __name__ == "__main__":
    main()
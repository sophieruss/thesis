INPUT = "Python Simulator/programs/basic_loop.csv"
OUTPUT = 'Agda/programs/outputs/OUT.agda'
firstline = OUTPUT.replace('/', '.').replace('.agda', '')

def helper(prev_reg, line, pc):
    next_pc = -1
    prog, trace = None, None
    reg = prev_reg.copy()
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
            next_pc = int(line[1]) - 1 # because we will increment it later
            
        case "Bgtz":
            reg = prev_reg.copy()
            prog = f"Bgtz (# {line[1]}) {line[2]}"
            if (prev_reg[int(line[1])] > 0):
                next_pc = int(line[2]) - 1 # because we will increment it later
                trace = f"⟨ {prog} , {prev_reg[int(line[1])]} ∷ {int(line[2])} ∷ 0 ∷ [] ⟩"

            else:
                trace = f"⟨ {prog} , {prev_reg[int(line[1])]} ∷ {pc+1} ∷ 0 ∷ [] ⟩"     
                
        case "Enable":
            prog = "Enable"
            trace = "⟨ Enable , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
    
        case "Disable":
            prog = "Disable"
            trace = "⟨ Disable , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
            
        case "NoOp":
            prog = "Disable"
            trace = "⟨ Disable , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
                       
        case _: #for all instructions I don't have yet, just increment pc +1
            prog = "Enable"
            trace = "⟨ Enable , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
        
    return prog, reg, trace, next_pc

def proof_helper(prog, stateA, trace):
    match prog.split()[0]:
        case 'Add':
            return f"step-Add prog state-{stateA} ? refl"
        case 'Sub':
            return f"step-Sub prog state-{stateA} ? refl"
        case 'Addi':
            return f"step-Addi prog state-{stateA} ? refl"
        case 'Jump':
            return f"step-Jump prog state-{stateA} ? ? refl"
        case 'Bgtz':
            if (int(trace.split()[6]) > 0):
                return f"step-Bgtz-g prog state-{stateA} ? ? ? refl"
            return f"step-Bgtz-l prog state-{stateA} ? ? ? refl"
        case 'Enable':
            return f"step-Enable prog state-{stateA} ? refl"
        case 'Disable':
            return f"step-Disable prog state-{stateA} ? refl"
        case _:
            return f"step-NoOp prog state-{stateA} ? refl"
           
def agdaList(oldlist):
    new = ' ∷ '.join(str(x) for x in oldlist)
    return new + ' ∷ []'

def readfile():    
    with open(INPUT, 'r') as f:
        lines = []
        for line in f:
            if line.strip() == '':
                break
            lines.append(line)
        return lines

def main():
    program, registers, traces, pcs = [None] * 100, [None] * 100, [None] * 100, [None] * 100
    empty_reg = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    num_states = 0  # not the number of instruction(could be >), because we could loop
    f = readfile()
    
    i = 0
    while i < len(f) and num_states < 50:
        line = f[i]
    # for i, line in enumerate(f):
        if line[0] == '#':
            break
        if line == '\n':
            continue
        line = line.split() 
        prev_reg = empty_reg       
        if (num_states>0):
            prev_reg = registers[num_states-1]
                        
        program[num_states], registers[num_states], traces[num_states], next_pc = helper(prev_reg, line, i)
        pcs[num_states] = i
        if next_pc != -1:
            i = next_pc + 1 # need to increment this bc its one off for some reason
        else:
            i = i + 1 # increment pc!
        num_states += 1        
        
        
    program = program[:num_states]
    registers = [empty_reg] + registers[:num_states-1]
    # remove last register (we wouldnt use it?), and add the starting state
    traces = traces[:num_states]
    pcs = pcs[:num_states]
           
        
    with open(OUTPUT, 'w') as f:
        f.write("module " + firstline + " where\n" +
                "open import agda.commands\n" + 
                "open import agda.host\n" +
                "open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )\n" +
                "open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)\n" +
                "open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)\n" +
                "open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)\n" +
                "open import Data.Bool using (Bool; true; false)\n" +
                "open import Agda.Builtin.List\n")
        
        f.write(f"prog : Program {len(registers)}\n")
        f.write(f"prog = program ({agdaList(program)})\n")
        
        for i in range(0, len(registers)):
            f.write(f"r-{i} ")
        f.write(" : Vec ℕ 32\n")   
        
        for i in range(0, len(registers)):
            f.write(f"r-{i} = {agdaList(registers[i])}\n")
        
        for i in range(0, len(traces)):
            f.write(f"state-{i} = [ {pcs[i]} , r-{i} , true ]\n")
            
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


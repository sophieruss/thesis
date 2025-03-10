INPUT = "Python Simulator/programs/fib.csv"
OUTPUT = 'Agda/programs/outputs/simulator.agda'
firstline = OUTPUT.replace('/', '.').replace('.agda', '')

def helper(prev_reg, line):
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
            
        case "Bgtz":
            reg = int(line[1])
            pc = int(line[2])
            prog = f"Bgtz (# {line[1]}) {line[2]}"
            trace = f"⟨ {prog} , {prev_reg[reg]} ∷ {pc} ∷ 0 ∷ [] ⟩"
        
        case _:
            prog = "NoOp"
            trace = "⟨ NoOp , 0 ∷ 0 ∷ 0 ∷ [] ⟩"
        
    return prog, reg, trace

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
            if (trace.split()[3] > 0):
                return f"step-Bgtz-g prog state-{stateA} ? ? ? refl"
            return f"step-Bgtz-l prog state-{stateA} ? ? ? refl"
        case _:
            return f"step-NoOp prog state-{stateA} ? refl"
           
def agdaList(oldlist):
        new = ' ∷ '.join(str(x) for x in oldlist)
        return new + ' ∷ []'

        
with open(INPUT, 'r') as f:
    
    program, registers, traces = [None] * 100, [None] * 100, [None] * 100
    empty_reg = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

    num_instructions = 0
    for i, line in enumerate(f):
        if line[0] == '#':
            break
        if line == '\n':
            continue
        line = line.split() 
        prev_reg = empty_reg       
        if (i>0):
            prev_reg = registers[i-1]
        program[i], registers[i], traces[i] = helper(prev_reg, line)
        num_instructions += 1
    program = program[:num_instructions]
    registers = [empty_reg] + registers[:num_instructions-1]
    # remove last register (we wouldnt use it?), and add the starting state
    traces = traces[:num_instructions]
           
        
    with open(OUTPUT, 'w') as f:
        f.write("module " + firstline + " where\n" +
                "open import agda.commands\n" + 
                "open import agda.host\n" +
                "open import Data.Nat using (ℕ; compare; _≤_; _<_; _>_; _+_; _∸_; zero; suc; s<s; z<s; z≤n; s≤s )\n" +
                "open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)\n" +
                "open import Data.Vec.Base using (Vec; _∷_; []; replicate; lookup; updateAt; length)\n" +
                "open import Data.Fin using (Fin; zero; suc; #_; fromℕ<)\n" +
                "open import Agda.Builtin.List\n")
        
        f.write(f"prog : Program {len(registers)}\n")
        f.write(f"prog = program ({agdaList(program)})\n")
        
        for i in range(0, len(registers)):
            f.write(f"r-{i} ")
        f.write(" : Vec ℕ 32\n")   
        
        for i in range(0, len(registers)):
            f.write(f"r-{i} = {agdaList(registers[i])}\n")
        
        for i in range(0, len(traces)):
            f.write(f"state-{i} = [ {i} , r-{i} ] \n")
            
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





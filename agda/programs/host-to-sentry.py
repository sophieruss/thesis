INPUT = 'Agda/programs/outputs/loop.agda'
OUTPUT = 'Agda/programs/outputs/OUT-Sentry.agda'
host_and_sentry = False #keep host code in outputted file

# sort of works with agda/host-testcases.agda
# 1. change emptyTracs to the correct trace (they will be holes)
# 2. for `step—→` lines, put 'sentry_'prefix to the proofs


def process_lines(line1, line2):
    tokens1 = line1.split()
    tokens2 = line2.split()
        
    if tokens1[1] == ":":
        step = tokens1[0]
        p = tokens1[2]
        statea = tokens1[4]
        arrow = tokens1[5]
        stateb = tokens1[6]
        comma2 = tokens1[7]
        trace = " ".join(tokens1[8:])
        if trace == "emptyTrace":
            trace = "{! !}"
        modified_line1 = f"sentry_{step} : {trace} , {p} , {statea} {arrow} {stateb}"        
    
        step2 = tokens2[0]
        step_type = tokens2[2]
        everything_else = " ".join(tokens2[3:])
        modified_line2 = f"sentry_{step} = {step_type} {trace} {everything_else}"

        return modified_line1, modified_line2
    return None, None
                
def translate(input_file, output_file, host_and_sentry):
    with open(input_file, 'r') as infile, open(output_file, 'w') as outfile:
        lines = infile.readlines()
        i = 0
        while i < len(lines):
            line = lines[i]
            stripped_line = line.strip()  
            
            indent = (len(line) - len(line.lstrip(' '))) * ' '
            
            if ":" in line and  "—→" in line and "--" != stripped_line[0:2]:

                if i + 1 < len(lines):
                    next_line = lines[i + 1]
                    next_stripped_line = next_line.strip()
                    next_indent = (len(next_line) - len(next_line.lstrip(' '))) * ' '


                    modified_line1, modified_line2 = process_lines(stripped_line, next_stripped_line)
                    
                    if host_and_sentry: #write the host lines part
                        outfile.write(line)
                        outfile.write(next_line)
                    
                    outfile.write(indent + modified_line1 + "\n")
                    outfile.write(next_indent + modified_line2 + "\n\n")
                    
                    i += 2
                else:
                    outfile.write(indent + stripped_line + "\n")
                    i += 1
            elif "module" in line:
                out = output_file.split("/")[-1].split(".")[0]
                outfile.write("module Agda.programs.outputs."+ out +" where\nopen import agda.sentry\n")
                i += 1
            elif "state" in line:
                stripped_line = stripped_line.replace(', true ', '')
                outfile.write(indent + stripped_line + "\n")
                i += 1
            else:
                outfile.write(indent + stripped_line + "\n")
                i += 1


translate(INPUT, OUTPUT, host_and_sentry)            

print("Yay!! Sentry eqivalent is in: `" + OUTPUT + "`")

import json
from commands import Add, Addi, Sub, Jump, Bgtz, Sw, Lw_U, Lw_T, Get, Put, trustedMode, untrustedMode, alert, returnn


def send_trace(trace):
    trace = trace[0].__dict__, trace[1:]

    with open('trace.json', 'w') as f:
        json.dump(trace, f)
        f.write('\n')
    
    with open('trace_history.json', 'a') as f:
        json.dump(trace, f)
        f.write('\n')
    
    return 1
        
        

                
def read_trace():
    with open('trace.json', 'r') as f:
        trace = json.load(f)
    cmd = trace[0]
    
    if cmd['command'] == 'add':
        cmd = Add(cmd['dest'], cmd['src'], cmd['temp'])
    elif cmd['command'] == 'addi':
        cmd = Addi(cmd['dest'], cmd['src'], cmd['n_1'])
    elif cmd['command'] == 'sub':
        cmd = Sub(cmd['dest'], cmd['src'], cmd['temp'])
    elif cmd['command'] == 'jump':
        cmd = Jump(cmd['n'])
    elif cmd['command'] == 'bgtz':
        cmd = Bgtz(cmd['src'], cmd['n'])
    elif cmd['command'] == 'sw':
        cmd = Sw(cmd['src'], cmd['dest'])
    elif cmd['command'] == 'lw_U':
        cmd = Lw_U(cmd['src'], cmd['dest'])
    elif cmd['command'] == 'lw_T':
        cmd = Lw_T(cmd['src'], cmd['dest'])
    elif cmd['command'] == 'get':
        cmd = Get(cmd['dest'])
    elif cmd['command'] == 'put':
        cmd = Put(cmd['src'])
    else:
        raise ValueError(f"Unknown command: {cmd['command']}")
        
    trace = (cmd, trace[1])
    return trace
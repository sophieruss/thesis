import json

def send_trace(trace):
    trace = trace[0].__dict__, trace[1:]

    with open('trace.json', 'w') as f:
        json.dump(trace, f)
        f.write('\n')
    
    with open('trace_history.json', 'a') as f:
        json.dump(trace, f)
        f.write('\n')
                
def read_trace():
    with open('trace.json', 'r') as f:
        trace = json.load(f)
    return trace
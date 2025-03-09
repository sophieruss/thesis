# thesis
my super fire thesis

## Python Simulator
1. There is `Host.py` and `Sentry.py`, whose semantics are defined by paper
2. `Commands.py` outlines commands for both machines, as significant overlap
3. Trace values are sent from Host to Sentry via `trace.json`
4. The `Simulator.py` is the main file to run; Here, the program is defined, and Host and Sentry and properly called.

## Agda
1. `steps.agda` defines steps system can take. Its verification is on `testcases.agda` and `deterministic.agda`  
2. `commands.agda` outlines commands for both machines, as significant overlap
3. `host.agda` defines the host machine. Its verification is on `host-testcases.agda`
4. `sentry.agda` defines the sentry machine. Its verification is on `sentry-testcases.agda`

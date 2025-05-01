# thesis
my super fire thesis

## Agda
1. `commands.agda` outlines commands for both machines, as significant overlap
2. `host-new.agda` defines the host machine. Its verification is on `deterministic-host-new.agda`
3. `sentry-new.agda` defines the sentry machine. Its verification is on `deterministic-sentry-new.agda`
4. `host-to-sentry-new-big` is main proof showing systems are in sync
5. `a-new-proof-unt-call` is a collection of perhaps trivial properties of system 

### Archive Folder
*(Historical versions, abandoned approaches, and paths wrongfully pursued)*  
- `steps.agda` is the original template for host and sentry. It defines general steps the system can take. Its verification is on `testcases.agda` and `deterministic.agda`
- `host` `deterministic-host` `sentry` `deterministic-sentry` are all previous iterations
- `postulate-prf` was the iteration of host-sentry proof that attempted to prove that if sentry took a step, host could take an equivalent step(s). It requires a postulate, and generally has issues.
- ~`host-testcases` `sentry-testcases` `fib`, are old testcases. Not supported by current version of system.~
- ~`programs` folder includes script to convert programs in .txt files to .agda proofs. Not supported by current version of system.~

## Python Simulator
1. There is `Host.py` and `Sentry.py`, whose semantics are defined by paper
2. `Commands.py` outlines commands for both machines, as significant overlap
3. Trace values are sent from Host to Sentry via `trace.json`
4. The `Simulator.py` is the main file to run; Here, the program is defined, and Host and Sentry and properly called.

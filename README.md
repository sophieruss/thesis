# thesis
my super fire thesis

## Agda
1. `commands.agda` outlines commands for both machines, as significant overlap
2. `host.agda` defines the host machine. Its verification is on `deterministic-host.agda`
3. `sentry.agda` defines the sentry machine. Its verification is on `deterministic-sentry.agda`
4. `host-and-sentry` is main proof showing systems are in sync
5. `trivial-proofs` is a collection of perhaps trivial properties of system
6. `example.csv` is an example program.  Host and sentry proofs are in `example.agda`

#### Archive Folder
*(Historical versions and abandoned approaches)*  
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

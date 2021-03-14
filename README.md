# SAT_Solving_Problem_3

## Disclosure

We implemented all mandatory and optional (bonus) tasks. Our algorithm successfully solves most problems
within the time frame of 1min, and often even in matter of seconds, which we are very proud of.
However, we want to explicitly mention the fact that the following two problem types listed below could
*not* be solved properly:

SAT: ii16, ii32, ii8, par
UNSAT: hole8/9

A main problem was that those problems with over 20.000 clauses had a notably deterimental effect on the performance
and, thus, slowed down the CDCL algorithm crucially.

For that reason, in order to generate the plots some of the above mentioned problem types were moved
to a different folder (named "malfunction").

We have also noticed that different hyperparameters & heuristics performed differently well on different problems.

## Running the program:

### Files

> $ SAT_Solver.exe -file "../inputs/test/sat/unit.cnf"

### Directories

Single Directory:

> SAT_Solver.exe -dir "../inputs/test/sat" "../inputs/test/unsat"

Up to two Directories:

> SAT_Solver.exe -dir "../inputs/test/sat" "../inputs/test/unsat"

## Generating the plots:

After you have run a Directory of Problem you can generate a plot for the steps and times.

### Steps Plot:

> python plot-steps.py

### Times Plot:

> python plot-times.py

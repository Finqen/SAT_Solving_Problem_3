# SAT_Solving_Problem_3

## Disclosure

We implemented all mandatory and optional (bonus) tasks. Our algorithm successfully solves most problems
within the time frame of 1min, and often even in matter of seconds, which we are very content of.
However, we want to explicitly mention the fact that the following two problem types listed below could
*not* be solved properly:

SAT: ii16a1-ii16e2 & UNSAT: Hole 7,8,9

And the following problems took notably longer than expected:

SAT: aim-200-3

We know a main problem is the way we implemented the backpropagation as it does not scale efficiently
with large number of clauses (>19.000) as it is the case for the ii16 problem. We suspect for the respective unsat problems
that similar applies once new clauses are being added repetitively or that the choice of heuristics might be
counter-productive for those specific problems, specially as there are clearly harder unsat problems that our algorithm
was successful at solving.

For that reasons, in order to generate the plots some of the above mentioned problem types were moved
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
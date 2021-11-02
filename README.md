# SAT-solver-DPLL-CNF

This code is the solution to one of exercises from the book: "Certified Programming with Dependent Types" by Adam Chlipala.

Part II
Programming with Dependent Types
Chapter 6, Subset Types and Variations.

0.4 From Subset, Exercise #3.

Implement the DPLL satisfiability decision procedure for boolean formulas in conjunc-
tive normal form, with a dependent type that guarantees its correctness. An example
of a reasonable type for this function would be ∀ f : formula, {truth : tvals | formu-
laTrue truth f } + {∀ truth, ¬ formulaTrue truth f }. Implement at least the basic
backtracking algorithm as defined here:

http://en.wikipedia.org/wiki/DPLL_algorithm

It might also be instructive to implement the unit propagation and pure literal elimi-
nation optimizations described there or some other optimizations that have been used
in modern SAT solvers.

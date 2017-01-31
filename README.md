# Coq-std++

This project contains an extended "Standard Library" for Coq called coq-std++.
The key features of this library are as follows:

- It provides a great number of definitions and lemmas for common data
  structures such as lists, finite maps, finite sets, and finite multisets.
- It uses type classes for common notations (like `∅`, `∪`, and Haskell-style
  monad notations) so that these can be overloaded for different data structures.
- It uses type classes to keep track of common properties of types, like it
  having decidable equality or being countable or finite.
- Most data structures are represented in canonical ways so that Leibniz
  equality can be used as much as possible (for example, for maps we have
  `m1 = m2` iff `∀ i, m1 !! i = m2 !! i`). On top of that, the library provides
  setoid instances for most types and operations.
- It provides various tactics for common tasks, like an ssreflect inspired
  `done` tactic for finishing trivial goals, a simply breadth-first solver
  `naive_solver`, an equality simplifier `simplify_eq`, a solver `solve_proper`
  for proving compatibility of functions with respect to relations, and a solver
  `set_solver` for goals involving set operations.
- It is entirely axiom free.

# History

Coq-std++ has originally been developed by Robbert Krebbers as part of his
formalization of the C programming language in his PhD thesis, called
[CH2O](http://robbertkrebbers.nl/thesis.html). After that, Coq-std++ has been
part of the [Iris project](http://iris-project.org), and has continued to be
developed by Robbert Krebbers, Ralf Jung, and Jacques Henri-Jourdan.

## Prerequisites

This version is known to compile with:

 - Coq 8.6

## Building Instructions

Run `make` to build the full development.

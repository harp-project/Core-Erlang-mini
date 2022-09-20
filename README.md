# Core Erlang Mini

This project aims to investigate possible formalisations of program equivalence (behavioural, contextual, CIU equivalence and logical relations) using a small subset of Core Erlang, including lists, pattern matching and recursion.

# Requirements

This project only depends on Coq, version 8.15.0 or later.

# Installation

`make` compiles the library

# Contents

The formalisation of the sequential language:

- `Basics.v` contains simple extensions about the standard library
- `ExpSyntax.v` contains the formal syntax of language under investigation
- `ExpManipulation.v` contains the definition of substitutions, renamings
- `Scoping.v` contains the scoping rules for the language
- `SubstSemantics.v` contains the dynamic semantics of the language
- `LogRel.v` contains the logical relations
- `Compatibility.v` contains the compatibility (congruence) proofs of the logical relations
- `CIU.v` contains "CIU-equivalence" definition
- `CTX.v` contains contextual equivalence definitions, proofs about equality of equivalences
- `Equivs.v` contains simple expression equivalence proofs

The formalisation of the concurrent language:

- `ConcurrentFunSemantics.v` contains the process-local and inter-process (system) semantics of Core Erlang.
- `Examples.v` contains a number of program evaluation proofs using the concurrent semantics.
- `ConcurrentProperties.v` contains proofs about the properties of the concurrent semantics.
- `Bisimulations.v` contains program equivalence definitions and proofs.

# Related work

This work is based on the following related work:

- Operational Semantics and Program Equivalence: https://link.springer.com/chapter/10.1007/3-540-45699-6_8
- Autosubst: https://link.springer.com/chapter/10.1007%2F978-3-319-22102-1_24
- Contextual Equivalence for a Probabilistic Language with
Continuous Random Variables and Recursion: https://dl.acm.org/doi/pdf/10.1145/3236782

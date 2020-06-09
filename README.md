CNF.jl
======

A library for manipulating Conjunctive Normal Form (CNF) formulae.

We implement:

1. Basic logic operations
   - Conjunction (`∧`)
   - Disjunction (`∨`)
   - Negation (`¬`)
2. Formula reduction (`trim!`)
3. Formula restriction/partial evaluation (`|`)
4. Formula evaluation (`ϕ()`, where `ϕ` is a CNF)
5. Shannon's Decomposition (`shannon`, `shannon!`)
6. Extracting formula scope (`get_vars`)
7. Counting variables (`count_vars`)
8. Formula equality (`==`, `!=`, `is_⊤`, `is_⊥`)
9. Clause membership (`∈`, `∋`)
10. Unique hash for equivalent CNFs (`hash`)
11. String representation for CNFs (`string`)
12. CNF copies (`copy`)
13. Iterating over all valuations (`valuations`)
12. String representation for instantiations and literals (`inst_str`, `lit_str`)
13. Composing disjunctions or conjunctions out of a set of literals (`and`, `or`)
14. Removing duplicate literals (`rmdups!`, `rmdups`)

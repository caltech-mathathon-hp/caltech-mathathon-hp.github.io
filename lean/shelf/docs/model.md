# The model and the statements

The statements of the two theorems are the team's. We use them unchanged, so
that the shelf proof and the team's proof are proofs of the same statements.

The team's own description is in
[`vendor/protein_folding/docs/model.md`](../vendor/protein_folding/docs/model.md):
the lattice, what a fold is, which pairs of `H`'s count, how an input is written
as a word, and what NP, NP-hard and a polynomial-time reduction mean there. In
short:

- The lattice is `ℤ³`. A fold places every letter of the string, `H` and `P`,
  on a different site, with consecutive letters on neighbouring sites.
- HP STRING-FOLD: given a string and a number, is there a fold with at least
  that many pairs of `H`'s on neighbouring sites?
- PERFECT HP STRING-FOLD: given a string and `n`, is there a fold whose `H`'s
  are exactly the points of a cube of side `n`?
- Polynomial time is about Turing machines, Mathlib's
  `Turing.TM2ComputableInPolyTime`. A reduction is a function with such a
  machine that sends yes-instances to yes-instances and no-instances to
  no-instances.

## What the shelf proof adds to the model

- **The source problem.** EXACT PACKING is `Shelf.ExactAccepts`: positive sizes
  `a₁, …, a_k`, `m` bins of capacity `B`, and a split of the items into `m`
  groups of total size `B`. The numbers are written in unary
  (`Packing.instanceEncoding`). The team's source problem,
  `Packing.ModifiedAccepts`, is the same with every size even
  (`Shelf.modifiedAccepts_iff`), and it is the one the reduction starts from.
- **Contacts.** The paper counts pairs of `H`'s on neighbouring sites that are
  not neighbours in the string. The team's statement counts all pairs of `H`'s
  on neighbouring sites. The two numbers differ by the number of places where
  the string has `HH`, and the team's reduction from the perfect problem to the
  threshold problem does this bookkeeping.
- **The cube.** In the shelf proof the cube is at the origin, `Q n = cube 0 n`.
  A perfect fold can always be moved there (`Shelf.perfect_iff_exists_fills`).

# The route of the proof

## The chain of reductions

The final theorems say that two folding problems are NP-complete. Hardness comes
from a chain, and only one link of it is ours.

1. Every problem in NP reduces to SAT. This is the Cook–Levin theorem. It is
   not proved in Lean: it is the hypothesis `hCL : SAT.CookLevin` of the final
   theorems.
2. SAT reduces to EXACT PACKING with even sizes and numbers written in unary.
   This is the team's (`SATPacking.modifiedBinPackingUnary_NPHard`).
3. **EXACT PACKING reduces to PERFECT HP STRING-FOLD. This is the shelf proof,
   and it is what this folder adds** (`Shelf.shelfKarp`).
4. PERFECT HP STRING-FOLD reduces to HP STRING-FOLD. This is the team's
   (`hpNPHard_of_perfectNPHard`).

That both folding problems are in NP is the team's too.

The team's library has its own proof of link 3, by a different string. The two
proofs end in the same statements, `PerfectHPStringFoldNPComplete` and
`HPStringFoldNPComplete`, which are defined once, in the team's library.

## The shelf reduction

An instance of EXACT PACKING is a list of sizes `a₁, …, a_k`, a number of bins
`m` and a capacity `B`, with `∑ aᵢ = m · B`. The question is whether the items
can be split into `m` groups of total size `B` each.

We first normalise the instance (`Shelf.normalise`): all sizes and `B` are
multiplied by 6, and if `m` is even we add one item of size `B` and one bin.
Then we write a string `S` and a side `n = m (B + 1) + 3` (`Shelf.shelfWord`,
`Shelf.side`). The string has `n³` letters `H`, so in a perfect fold they fill a
cube of side `n`.

One edge of the cube is the shelf. In a perfect fold the `m + 1` separators,
which are single `H`'s, lie on the shelf and cut it into `m` gaps, and every
gap turns out to have exactly `B` points. Every item is a run of `aᵢ` letters
`H`, and it lies in one gap. So the string has a perfect fold exactly when the
items can be packed into the bins.

- **Theorem 12** (`Shelf.foldGivesPacking`): from a perfect fold of `S` we read
  off an exact packing. Files `Tether`, `LongPath`, `EdgeDistance`, `ShelfLine`,
  `Converse`.
- **Theorem 16** (`Shelf.packingGivesFold`): from an exact packing we build a
  perfect fold of `S`, site by site. Files `Walk`, `Core`, `Routing`, `Tiling`,
  `Layout` and the other files whose names start with `Layout`, `Forward`.
- **Polynomial time** (`Shelf.shelfMap_polyTime`): a Turing machine checks the
  input, normalises it and writes `S` and `n`. Files `NormaliseComputable`,
  `WordComputable`, `NPComplete`.

## Where Lean differs from the paper

- The paper takes `∑ aᵢ = m · B` as part of what an instance is. A machine gets
  any input, so the reduction checks this first and sends a bad input to a
  string that has no perfect fold.
- The team's source problem asks in addition that every size is even. The
  reduction makes the team's check, and on the inputs that pass it is the
  reduction of the paper.
- The paper cites Garey and Johnson for the hardness of the source problem. In
  Lean it comes from the team's reduction from SAT.
- Lemma 13 says that certain directions exist. In Lean we write them down.
- In Theorem 16 we do not prove directly that the `H`'s cover the cube. They
  are inside it, there are `n³` of them and they are on different sites, which
  is enough.

The [README](../README.md#differences-from-the-paper) says more about each of
these.

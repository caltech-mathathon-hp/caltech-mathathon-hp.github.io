# The route of the proof

## The chain of reductions

The final theorems say that two folding problems are NP-complete. Hardness comes
from a chain, and only one link of it is ours.

1. Every problem in NP reduces to SAT. This is the Cook–Levin theorem, and it
   is the team's (`SAT.CookLevinUniversal.cookLevin`). From a machine that
   checks certificates, a Turing machine writes a formula that can be satisfied
   exactly when the machine accepts some certificate.
2. SAT reduces to EXACT PACKING with even sizes and numbers written in unary.
   This is the team's (`SATPacking.modifiedBinPackingUnary_NPHard`).
3. **EXACT PACKING reduces to PERFECT HP STRING-FOLD. This is the shelf proof,
   and it is what this folder adds** (`Shelf.shelfKarp`).
4. PERFECT HP STRING-FOLD reduces to HP STRING-FOLD. This is the team's
   (`hpNPHard_of_perfectNPHard`).

That both folding problems are in NP is the team's too.

Every link is proved in Lean, so the final theorems have no hypothesis
(`Shelf.Unconditional.perfectHPStringFold_NPComplete` and
`Shelf.Unconditional.hpStringFold_NPComplete`). Link 1 was the last one: until
the team proved it, the final theorems had it as a hypothesis,
`hCL : SAT.CookLevin`, and `Shelf/NPComplete.lean` still has them in that form.

The team's library has its own proof of link 3, by a different string. The two
proofs end in the same statements, `PerfectHPStringFoldNPComplete` and
`HPStringFoldNPComplete`, which are defined once, in the team's library.
`Shelf/Unconditional.lean` has the team's chain with nothing assumed as well
(`Shelf.Unconditional.TeamRoute`).

## Which version of our proof this is

The website's page
[A proof with bins on one edge](https://caltech-mathathon-hp.github.io/one-edge-proof/)
has two strings for link 3. Its seventeen cards use the longer one, with
separators that are rods of `B + 6` letters `H` and two walls. Its section
[Folding a small instance](https://caltech-mathathon-hp.github.io/one-edge-proof/#folding-a-small-instance)
uses the shorter one, with separators that are single `H`'s and two tethers
instead of the walls. Lean checks the shorter one, the shelf version, and the
rest of this page is about it. The longer string is not in Lean.

Lean's string and the one the website folds differ only when `m` is even: Lean
puts the item that the normalisation adds first in the list of items, and the
website puts it last. Our write-up does not say where it goes. Theorems 12 and
16 are proved for the items in any order, so they cover both.

Theorem 12, Theorem 16 and the other numbers below are those of our write-up of
the shelf version.

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

## Where Lean differs from our write-up

- Our write-up takes `∑ aᵢ = m · B` as part of what an instance is. A machine gets
  any input, so the reduction checks this first and sends a bad input to a
  string that has no perfect fold.
- The team's source problem asks in addition that every size is even. The
  reduction makes the team's check, and on the inputs that pass it is the
  reduction of our write-up.
- Our write-up cites Garey and Johnson for the hardness of the source problem. In
  Lean it comes from the team's reduction from SAT and the team's proof of the
  Cook–Levin theorem.
- Lemma 13 says that certain directions exist. In Lean we write them down.
- In Theorem 16 we do not prove directly that the `H`'s cover the cube. They
  are inside it, there are `n³` of them and they are on different sites, which
  is enough.

The [README](../README.md#differences-from-our-write-up) says more about each of
these.

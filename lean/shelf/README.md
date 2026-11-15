# The shelf proof in Lean

This folder formalizes, in Lean 4 with Mathlib, the proof in
[`proof/paper/paper.tex`](../proof/paper/paper.tex) that HP protein folding on the
cubic lattice is NP-complete. All lemma numbers below are the paper's.

The statement of the theorem is not ours. It is the one in the team's Lean
library (`lean/cubic` on the branch `lean-certificates` of the website
repository). An unchanged copy of that library is in
[`vendor/protein_folding`](vendor/protein_folding), and this project is built
against the copy; [`vendor/README.md`](vendor/README.md) says which commit it was
copied from. We prove that statement by a different reduction.

## What we prove ourselves, and what we take from the team's library

The theorem is proved by a chain of reductions. Only one link of the chain is
the shelf proof.

| Step | Where it comes from |
|---|---|
| SAT is NP-hard (Cook–Levin) | a hypothesis `hCL : SAT.CookLevin` of the final theorems, as in the team's library |
| SAT reduces to EXACT PACKING with even sizes and numbers in unary | the team's library (`SATPacking.modifiedBinPackingUnary_NPHard`) |
| **EXACT PACKING reduces to PERFECT HP STRING-FOLD** | **this folder: the shelf proof, Sections 2 to 5 of the paper, and a Turing machine that computes the reduction** |
| PERFECT HP STRING-FOLD reduces to HP STRING-FOLD | the team's library (`hpNPHard_of_perfectNPHard`) |
| both folding problems are in NP | the team's library (`perfectHPStringFold_inNP`, `hpStringFold_inNP`) |

Inside the shelf proof we also reuse the team's lemmas about the cube wherever
the two proofs need the same fact: an isolated `H` lies on the skeleton, a path
on the skeleton has at most `9n - 10` vertices, edges that do not touch are far
apart. The file `Shelf/Cube.lean` has the dictionary between the words of the
paper and the names in that library.

The two final theorems are in `Shelf/NPComplete.lean`:

```lean
theorem perfectHPStringFold_NPComplete (hCL : SAT.CookLevin) : PerfectHPStringFoldNPComplete
theorem hpStringFold_NPComplete (hCL : SAT.CookLevin) : HPStringFoldNPComplete
```

The hypothesis `hCL` says that SAT is NP-hard. It is the only thing that is
assumed. There is no `sorry` and no axiom of our own anywhere:
`lake env lean checks/Axioms.lean` prints the axioms each main result depends
on, and these are only `propext`, `Classical.choice` and `Quot.sound`, the three
axioms of Lean and Mathlib themselves.

## Build

```bash
cd lean
lake exe cache get     # compiled Mathlib, about 300 MB to download
lake build             # compiles the team's library (a few minutes) and ours
lake env lean checks/Axioms.lean
```

Lean `v4.24.0` and Mathlib `v4.24.0`, the same as the team's library. The first
command downloads Mathlib and the packages Mathlib needs. Nothing else is
fetched: the team's library is the copy in `vendor/`. Nothing in this folder is
sent anywhere.

## The certificate

These files say what is proved, for a reader who does not want to read the
proofs, and for the website. They have the same names and the same format as
the ones in the team's library (`vendor/protein_folding/docs` and
`vendor/protein_folding/checks`), so the website's generator reads the two
projects in the same way.

| File | What it is |
|---|---|
| [`docs/theorem-index.md`](docs/theorem-index.md) | the main results: the statement in the paper, the Lean name, the file, and whether it is a definition, proved, or proved given Cook–Levin |
| [`docs/proof-route.md`](docs/proof-route.md) | the chain of reductions, the shelf reduction on one page, and where Lean differs from the paper |
| [`docs/model.md`](docs/model.md) | the model and the statements, which are the team's |
| [`docs/verification.md`](docs/verification.md) | how to check the proof yourself, and how to read what Lean prints |
| [`checks/ShelfHardness.lean`](checks/ShelfHardness.lean) | prints the statement and the axioms of the 16 main results |
| [`checks/publication-axioms.txt`](checks/publication-axioms.txt) | what it prints |
| [`checks/Axioms.lean`](checks/Axioms.lean) | prints the axioms of every lemma of the paper |

After a change to the proofs, write the output again:

```bash
lake env lean checks/ShelfHardness.lean > checks/publication-axioms.txt
```

## Lemma map

Status is one of

- `proved`: a theorem in the build (for a Turing machine: the machine, with the
  proof that it computes the map in polynomial time), no `sorry`, no axioms
  beyond the three above;
- `defined`: a definition that the statements use;
- `stated`: the claim is in the build as a `Prop`, and is not proved yet;
- `planned`: not in the build yet; the name is the one it will have.

Every row is now `proved` or `defined`.

Files are in `lean/`; a file marked "team:" is in the team's library, under
`vendor/protein_folding/ProteinFolding/`.

<!-- lemma-map:start -->
| Paper | What it says | Lean name | File | Status |
|---|---|---|---|---|
| Theorem 1 | PERFECT HP STRING-FOLD is NP-complete (the statement) | `PerfectHPStringFoldNPComplete` | team: `Cubic/MainTheorem.lean` | defined |
| Theorem 1 | PERFECT HP STRING-FOLD is NP-complete, given the Cook–Levin theorem | `perfectHPStringFold_NPComplete` | `Shelf/NPComplete.lean` | proved |
| Theorem 1, membership | a fold is a certificate that is checked in polynomial time | `perfectHPStringFold_inNP` | team: `Cubic/Proofs/NPMembership.lean` | proved |
| Theorem 1, hardness | PERFECT HP STRING-FOLD is NP-hard, given the Cook–Levin theorem | `perfectHPStringFold_NPHard` | `Shelf/NPComplete.lean` | proved |
| Theorem 1, hardness | Theorems 12 and 16 make the reduction correct on every input | `reductionCorrect_of` | `Shelf/MainTheorem.lean` | proved |
| Theorem 1, hardness | the reduction is correct on every input | `reductionCorrect` | `Shelf/NPComplete.lean` | proved |
| Theorem 1, hardness | the map that the machine computes is a reduction from the team's source problem | `shelfMap`, `shelfMap_correct`, `shelfKarp` | `Shelf/NPComplete.lean` | proved |
| Theorem 1, polynomial time | a Turing machine normalises the instance in polynomial time | `normaliseComputable` | `Shelf/NormaliseComputable.lean` | proved |
| Theorem 1, polynomial time | a Turing machine writes the string and the side of the cube in polynomial time | `machineWord_eq`, `shelfPairComputable` | `Shelf/WordComputable.lean` | proved |
| Theorem 1, polynomial time | a Turing machine computes the reduction in polynomial time | `shelfMap_polyTime` | `Shelf/NPComplete.lean` | proved |
| Corollary 2 | HP STRING-FOLD is NP-complete (the statement) | `HPStringFoldNPComplete` | team: `Cubic/MainTheorem.lean` | defined |
| Corollary 2 | HP STRING-FOLD is NP-complete, given the Cook–Levin theorem | `hpStringFold_NPComplete` | `Shelf/NPComplete.lean` | proved |
| Corollary 2, proof | the perfect problem reduces to the threshold problem | `hpNPHard_of_perfectNPHard` | team: `Cubic/Proofs/PerfectToHPComputable.lean` | proved |
| Section 2.1 | EXACT PACKING, and that it contains the team's source problem | `ExactAccepts`, `modifiedAccepts_iff` | `Shelf/Source.lean` | proved |
| Section 2.1 | EXACT PACKING with even sizes and numbers in unary is NP-hard, given the Cook–Levin theorem | `SATPacking.modifiedBinPackingUnary_NPHard` | team: `Cubic/Proofs/SATPackingComputable.lean` | proved |
| Lemma 3, Corollary 4 | a fold has the maximum number of contacts exactly when its `H`'s fill a cube | `packsCube_iff_bond_threshold` | team: `Cubic/Proofs/GeometryMain.lean` | proved |
| Section 2.2 | the cube `Q`, the skeleton, edges, end nodes, the clamp map | `Q`, `clamp`, `IsEnd`, `EdgeSkeleton`, `CubeEdge` | `Shelf/Cube.lean` | defined |
| Section 2.2 | a perfect fold can be translated so that the `H`'s occupy `Q` | `perfect_iff_exists_fills` | `Shelf/FoldBasics.lean` | proved |
| Lemma 5 | the clamp map does not increase distances, and sends an outer site to its point of `Q` | `latticeDistance_clamp_le`, `clamp_eq_of_adj` | `Shelf/Tether.lean` | proved |
| Lemma 6 | an isolated `H` lies on the skeleton | `Isolated.on_skeleton` | `Shelf/Tether.lean` | proved |
| Lemma 7 | Tether Lemma: `H`'s joined by `g` letters `P` are at distance at most `g - 1` | `tether` | `Shelf/Tether.lean` | proved |
| Lemma 8 | the `H`'s of a dense run form a simple path on the skeleton | `RunAt.nodup`, `RunAt.isChain`, `RunAt.on_skeleton` | `Shelf/Tether.lean` | proved |
| Lemma 9 | a simple path on the skeleton has at most `9n - 10` vertices; at equality three edges are free and do not touch | `longPath_length_le`, `longPath_free_edges` | `Shelf/LongPath.lean` | proved |
| Lemma 9, as used in Theorem 12 | a path that avoids a longest path lies on one free edge, and fills it if it has `n - 2` vertices | `path_in_free_edge`, `filler_fills_free_edge` | `Shelf/LongPath.lean` | proved |
| Lemma 10 | edges that do not touch are at distance at least `n - 1`, with end nodes opposite end nodes at equality | `far_edges`, `far_edges_eq`, `far_edges_end` | `Shelf/EdgeDistance.lean` | proved |
| Section 3 | the normalisation does not change the answer | `normalised_normalise`, `exists_exact_normalise_iff` | `Shelf/Source.lean` | proved |
| Section 3 | the string `S` and the side `n` of the cube | `shelfWord`, `side`, `shelfReduction` | `Shelf/Word.lean` | defined |
| Section 3 | the features of `S` that Section 4 uses | `Anatomy` | `Shelf/Anatomy.lean` | defined |
| Section 3 | `S` has these features | `shelfAnatomy` | `Shelf/WordAnatomy.lean` | proved |
| Lemma 11 | `S` has exactly `n³` letters `H` | `hydrophobicCount_shelfWord` | `Shelf/Count.lean` | proved |
| Theorem 12 | a perfect fold of `S` gives an exact packing | `foldGivesPacking` | `Shelf/Converse.lean` | proved |
| Theorem 12, Steps 1 to 4 | the separators and the items lie on one edge, the first and last separator at its ends | `shelf_of_fills` | `Shelf/Converse.lean` | proved |
| Theorem 12, Steps 5 to 7 | on that edge every gap between separators holds items of total size `B` | `packing_of_shelf_line` | `Shelf/ShelfLine.lean` | proved |
| Section 5 | sites by coordinates, rows of sites | `pt`, `line` | `Shelf/Sites.lean` | defined |
| Section 5 | a list of different sites that spells `S`, consecutive ones adjacent, with the `H`'s in `Q` and the `P`'s outside, is a perfect fold | `perfect_of_walk` | `Shelf/Walk.lean` | proved |
| Lemma 13 | laying a dense run: every `H` of the run with the `P` before and after it; different skeleton points give different sites | `tokSites_isChain`, `tokSites_nodup` | `Shelf/Walk.lean` | proved |
| Lemma 14 | Core Lemma: a path through all points of `Q` outside the skeleton | `corePath` | `Shelf/Core.lean` | proved |
| Lemma 15 | Routing Lemma: disjoint routes for the linkers | `routes` | `Shelf/Routing.lean` | proved |
| Section 5.2 | the columns that the items occupy on the shelf, from the packing | `exists_tiling` | `Shelf/Tiling.lean` | proved |
| Section 5.2, Table 1 | the sites of the fold, piece by piece, and what the proof uses about the core, the run `A`, the items and the linkers | `layout`, `layoutWord`, `Parts.Good` | `Shelf/Layout.lean` | defined |
| Section 5.2, Table 1 | the run `A`: tokens along nine edges of the cube, through eight corners, with their normals | `aTokens`, `aTokens_linked`, `aTokens_nodup` | `Shelf/ATokens.lean` | proved |
| Section 5.2, Table 1 | the fillers, the separators and the items as tokens on three edges, with their `H`'s on different points | `shelfTokens_valid`, `shelfTokens_nodup` | `Shelf/LayoutTokens.lean` | proved |
| Section 5.2, Table 1 | the tethers and the other single `P`'s: different sites, outside the cube, not next to any skeleton point | `plain_nodup`, `plain_off` | `Shelf/LayoutPlain.lean` | proved |
| Section 5.2, Table 1 | the linkers, from the Routing Lemma: the right lengths, disjoint, away from everything else | `exists_linkers` | `Shelf/Linkers.lean` | proved |
| Theorem 16 | the string, read with every isolated `H` grouped with the `P` before and the `P` after it | `shelfWord_eq_layoutWord` | `Shelf/Regroup.lean` | proved |
| Theorem 16 | the fold spells the string: the `H`'s are in the cube, the `P`'s outside | `layout_fits` | `Shelf/LayoutFits.lean` | proved |
| Theorem 16 | consecutive sites of the fold are adjacent | `layout_isChain` | `Shelf/LayoutChain.lean` | proved |
| Theorem 16 | no site of the fold is used twice | `layout_nodup` | `Shelf/LayoutNodup.lean` | proved |
| Theorem 16 | an exact packing gives a core, a run `A`, columns for the items and linkers that fit together | `exists_good_parts` | `Shelf/Forward.lean` | proved |
| Theorem 16 | an exact packing gives a perfect fold of `S` | `packingGivesFold` | `Shelf/Forward.lean` | proved |
| Theorem 16, inputs that are not instances | the string they are sent to has no perfect fold | `noInstance_rejected` | `Shelf/MainTheorem.lean` | proved |
<!-- lemma-map:end -->

The older write-up `proof/proof.tex` numbers the same lemmas differently:
Lemmas 3, 6, 7, 8, 9, 10, 11 of the paper are its Lemmas 1, 2, 3, 4, 5, 6, 7;
Lemma 5 is its Lemma 8(b); Lemmas 13, 14, 15 are its Lemmas 9, 11, 10; Theorems
12 and 16 are its Theorems 2 and 3.

## What stays on paper

- **Cook–Levin.** That SAT is NP-hard is a hypothesis of the final theorems, not
  a proof. Mathlib does not have this theorem, and the team's library makes the
  same choice.
- **The citation for the source problem.** The paper cites Garey and Johnson for
  the fact that EXACT PACKING is NP-hard with numbers in unary. In Lean this
  comes from the team's reduction from SAT instead, so it is proved, given
  Cook–Levin.
- **Contacts.** The paper counts contacts between `H`'s that are not neighbours
  in the string. The team's statement counts all adjacent pairs of `H`'s,
  neighbours included; the two numbers differ by the number of factors `HH`.
  The team's reduction from the perfect problem to the threshold problem does
  this bookkeeping, so the last sentence of Lemma 11 (`h(S) = N₀ - 1`) has no
  counterpart here.

## Differences from the paper

In the paper `∑ aᵢ = m · B` is part of what an instance is. A Turing machine
gets arbitrary input, so the Lean reduction first checks this equation and that
all numbers are positive (`Guard`), and sends an input that fails the check to
the empty string with `n = 1`, which has no perfect fold
(`noInstance_rejected`). This map is `shelfReduction`, and `reductionCorrect`
says that it is correct on every input.

The problem that the team's library proves NP-hard is EXACT PACKING with one more
condition: every size is even. So the map of the final reduction, `shelfMap`,
makes the team's check, which also rejects an input with an odd size, and on the
inputs that pass it is `shelfReduction`. Nothing is lost: an instance with even
sizes is an instance of EXACT PACKING (`modifiedAccepts_iff`).

The paper says in one line that the string can be written down in polynomial
time. In Lean this is a statement about Turing machines, and the machine is put
together from the machines of the team's library: one for the check, one for
the normalisation, one that writes the string. The last one writes each item as
`P^(λ-2) (PPH)^a` instead of `P^λ H (PPH)^(a-1)`; the two are the same word when
`a ≥ 1` (`machineWord_eq`), and after the check every size is positive.

Lemma 13 says that normals for a dense run exist. In Lean we write the normals
down instead: `P D(r) P = (PHP)^r`, so the run is a list of tokens, each an `H`
on a skeleton point with its two `P`'s on outer sites, and along an edge the
`P`'s alternate between the two faces. The proof of Lemma 13 becomes two facts
about tokens (`tokSites_isChain`, `tokSites_nodup`).

In Theorem 16 we do not prove part (c), that the `H`'s cover the cube. They are
inside the cube and there are `n³` of them on different sites, and the team's
library concludes from this that they fill it (`perfect_of_walk`).

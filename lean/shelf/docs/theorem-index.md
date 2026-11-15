# From our write-up to Lean: the main results

This project checks the shelf version of our one-edge proof, the one whose
string the website spells out under
[Spelling the string](https://caltech-mathathon-hp.github.io/one-edge-proof/#spelling-the-string).
The first column says what each result is and gives its number in our write-up
of that version. The [README](../README.md#which-string-lean-checks) says how
this version differs from the seventeen cards on the website.

Names are prefixed by `ProteinFolding.` unless another prefix is shown; ours
are in `ProteinFolding.Shelf`, the others are the team's. This is the short
list. The table in the [README](../README.md#lemma-map) has every lemma of the
write-up.

| Concept in our write-up | Declaration | Source / status |
| --- | --- | --- |
| Section 1: strings, folds and contacts | `Residue`, `Sequence`, `Fold`, `bondCount` | [team: Common/Statement](../vendor/protein_folding/ProteinFolding/Common/Statement.lean), definitions |
| Section 1: HP STRING-FOLD and PERFECT HP STRING-FOLD | `HPInstance.Accepts`, `PerfectHPStringFold` | [team: Cubic/Statement](../vendor/protein_folding/ProteinFolding/Cubic/Statement.lean), definitions |
| What NP-complete means, and how an input is written | `InNP`, `NPHard`, `NPComplete`, `KarpReduces`, `hpEncoding`, `perfectEncoding` | [team: Common/Complexity](../vendor/protein_folding/ProteinFolding/Common/Complexity.lean), [team: Cubic/Encodings](../vendor/protein_folding/ProteinFolding/Cubic/Encodings.lean), definitions |
| Section 2.1: EXACT PACKING | `Packing.Instance`, `Shelf.ExactAccepts` | [team: Cubic/Proofs/PackingSources](../vendor/protein_folding/ProteinFolding/Cubic/Proofs/PackingSources.lean), [Shelf/Source](../Shelf/Source.lean), definitions |
| Section 2.1: the team's source problem is EXACT PACKING with even sizes | `Shelf.modifiedAccepts_iff` | [Shelf/Source](../Shelf/Source.lean), unconditional proof |
| Section 3: the normalisation, the string `S`, the side `n` of the cube | `Shelf.normalise`, `Shelf.shelfWord`, `Shelf.side`, `Shelf.shelfReduction` | [Shelf/Source](../Shelf/Source.lean), [Shelf/Word](../Shelf/Word.lean), definitions |
| Lemma 11: `S` has exactly `n³` letters `H` | `Shelf.hydrophobicCount_shelfWord` | [Shelf/Count](../Shelf/Count.lean), unconditional proof |
| Lemma 7, the Tether Lemma: `H`'s joined by `g` letters `P` are at distance at most `g - 1` | `Shelf.tether` | [Shelf/Tether](../Shelf/Tether.lean), unconditional proof |
| Lemma 9: a simple path on the skeleton has at most `9n - 10` vertices, and at equality three edges are free | `Shelf.longPath_length_le`, `Shelf.longPath_free_edges` | [Shelf/LongPath](../Shelf/LongPath.lean), unconditional proofs |
| Lemma 10: edges that do not touch are far apart | `Shelf.far_edges`, `Shelf.far_edges_eq`, `Shelf.far_edges_end` | [Shelf/EdgeDistance](../Shelf/EdgeDistance.lean), unconditional proofs |
| Theorem 12: a perfect fold of `S` gives an exact packing | `Shelf.foldGivesPacking` | [Shelf/Converse](../Shelf/Converse.lean), unconditional proof |
| Lemma 14, the Core Lemma: a path through all points of the cube outside the skeleton | `Shelf.corePath` | [Shelf/Core](../Shelf/Core.lean), unconditional proof |
| Lemma 15, the Routing Lemma: disjoint routes for the linkers | `Shelf.routes` | [Shelf/Routing](../Shelf/Routing.lean), unconditional proof |
| Section 5.2, Table 1: the sites of the fold | `Shelf.layout` | [Shelf/Layout](../Shelf/Layout.lean), definition |
| Theorem 16: an exact packing gives a perfect fold of `S` | `Shelf.packingGivesFold` | [Shelf/Forward](../Shelf/Forward.lean), unconditional proof |
| Theorems 12 and 16 together: the reduction is correct on every input | `Shelf.reductionCorrect` | [Shelf/NPComplete](../Shelf/NPComplete.lean), unconditional proof |
| Theorem 1, polynomial time: a Turing machine computes the reduction | `Shelf.shelfMap_polyTime` | [Shelf/NPComplete](../Shelf/NPComplete.lean), unconditional proof |
| The shelf reduction, from the team's source problem to PERFECT HP STRING-FOLD | `Shelf.shelfKarp` | [Shelf/NPComplete](../Shelf/NPComplete.lean), unconditional proof |
| Theorem 1, membership: both folding problems are in NP | `hpStringFold_inNP`, `perfectHPStringFold_inNP` | [team: Cubic/Proofs/NPMembership](../vendor/protein_folding/ProteinFolding/Cubic/Proofs/NPMembership.lean), unconditional proofs |
| Section 2.1: the source problem is NP-hard, with numbers in unary | `SATPacking.modifiedBinPackingUnary_NPHard` | [team: Cubic/Proofs/SATPackingComputable](../vendor/protein_folding/ProteinFolding/Cubic/Proofs/SATPackingComputable.lean), assumes Cook–Levin |
| Corollary 2, proof: the perfect problem reduces to the threshold problem | `hpNPHard_of_perfectNPHard` | [team: Cubic/Proofs/PerfectToHPComputable](../vendor/protein_folding/ProteinFolding/Cubic/Proofs/PerfectToHPComputable.lean), unconditional proof |
| The Cook–Levin theorem: SAT is NP-hard | `SAT.CookLevin`; `SAT.CookLevinUniversal.cookLevin` | [Statement](../vendor/protein_folding/ProteinFolding/Common/CookLevin.lean); [the team's proof](../vendor/protein_folding/ProteinFolding/Common/CookLevinProofUniversal.lean), unconditional proof |
| Theorem 1, hardness: PERFECT HP STRING-FOLD is NP-hard | `PerfectHPStringFoldNPHard`; `Shelf.Unconditional.perfectHPStringFold_NPHard` | [Statement](../vendor/protein_folding/ProteinFolding/Cubic/MainTheorem.lean); [proof](../Shelf/Unconditional.lean), unconditional proof |
| Theorem 1: PERFECT HP STRING-FOLD is NP-complete | `PerfectHPStringFoldNPComplete`; `Shelf.Unconditional.perfectHPStringFold_NPComplete` | Same files; unconditional proof |
| Corollary 2: HP STRING-FOLD on the cubic lattice is NP-complete | `HPStringFoldNPComplete`; `Shelf.Unconditional.hpStringFold_NPComplete` | Same files; unconditional proof |
| The step before: Theorem 1 and Corollary 2 with the Cook–Levin theorem as a hypothesis | `Shelf.perfectHPStringFold_NPHard`, `Shelf.perfectHPStringFold_NPComplete`, `Shelf.hpStringFold_NPComplete` | [Shelf/NPComplete](../Shelf/NPComplete.lean), assumes Cook–Levin |
| The team's two final theorems, by the team's string, with nothing assumed | `Shelf.Unconditional.TeamRoute.perfectHPStringFold_NPComplete`, `Shelf.Unconditional.TeamRoute.hpStringFold_NPComplete` | [Shelf/Unconditional](../Shelf/Unconditional.lean), unconditional proofs |

The last column says how each row stands: a definition, a proof with no
assumption ("unconditional"), or a proof that has the Cook–Levin theorem as a
hypothesis ("assumes Cook–Levin"). No row is an assumption: the Cook–Levin
theorem has a row of its own, and it is proved.

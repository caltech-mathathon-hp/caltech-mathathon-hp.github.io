# Paper-to-Lean index

Names are prefixed by `ProteinFolding.` unless another prefix is shown.
The source files are authoritative; declarations below are not extra assumptions.

| Paper concept | Declaration | Source / status |
| --- | --- | --- |
| Section 2: HP words, folds and bonds | `Residue`, `Sequence`, `Fold`, `hhBonds`, `bondCount`, `energy` | [Common/Statement](../ProteinFolding/Common/Statement.lean), definitions |
| Section 2: fixed cubic graph and HP decision problem | `cubicLattice`, `HPInstance.Accepts` | [Cubic/Statement](../ProteinFolding/Cubic/Statement.lean), definitions |
| Section 2: perfect folding | `PacksCube`, `PerfectHPStringFold` | [Cubic/Statement](../ProteinFolding/Cubic/Statement.lean), definitions |
| Encoding and meaning of NP-completeness | `hpEncoding`, `perfectEncoding`, `InNP`, `NPHard`, `NPComplete` | [Encodings](../ProteinFolding/Cubic/Encodings.lean), [Complexity](../ProteinFolding/Common/Complexity.lean) |
| Theorem 3.2: perfect packing iff maximum bond threshold | `perfectIffThreshold_holds` | [Proofs/Main](../ProteinFolding/Cubic/Proofs/Main.lean), unconditional proof |
| Footnote 1: membership in NP | `hpStringFold_inNP`, `perfectHPStringFold_inNP` | [NPMembership](../ProteinFolding/Cubic/Proofs/NPMembership.lean), unconditional proofs |
| Strong numerical hardness used for packing | `SATPacking.modifiedBinPackingUnary_NPHard` | [SATPackingComputable](../ProteinFolding/Cubic/Proofs/SATPackingComputable.lean), assumes Cook–Levin |
| Section 3.2: both directions of the packing-to-folding reduction, by an alternative frame | `CubicPacking.packingToPerfect_correct` | [PackingReductionCorrect](../ProteinFolding/Cubic/Proofs/PackingReductionCorrect.lean), unconditional proof |
| Polynomial-time reduction to perfect folding | `CubicPacking.packingToPerfect_karp` | [PackingReductionCorrect](../ProteinFolding/Cubic/Proofs/PackingReductionCorrect.lean), unconditional proof |
| Perfect folding to HP threshold folding | `perfect_karpReduces_hp` | [PerfectToHPComputable](../ProteinFolding/Cubic/Proofs/PerfectToHPComputable.lean), unconditional proof |
| Main step: PERFECT HP STRING-FOLD NP-hard | `PerfectHPStringFoldNPHard`; `perfectHPStringFold_NPHard` | [Statement](../ProteinFolding/Cubic/MainTheorem.lean); [proof](../ProteinFolding/Cubic/Proofs/Main.lean) with Cook–Levin |
| PERFECT HP STRING-FOLD NP-complete | `PerfectHPStringFoldNPComplete`; `perfectHPStringFold_NPComplete` | Same files; proof with Cook–Levin |
| Main theorem: cubic HP STRING-FOLD NP-complete | `HPStringFoldNPComplete`; `hpStringFold_NPComplete` | Same files; proof with Cook–Levin |
| Explicit remaining premise | `SAT.CookLevin` | [Common/CookLevin](../ProteinFolding/Common/CookLevin.lean), proposition only |

For the reduction's geometric witnesses, see
[PackingFrameCompleteness](../ProteinFolding/Cubic/Proofs/PackingFrameCompleteness.lean)
and [PackingFrameSoundness](../ProteinFolding/Cubic/Proofs/PackingFrameSoundness.lean).
Actual machine data are provided by
[PackingToPerfectComputable](../ProteinFolding/Cubic/Proofs/PackingToPerfectComputable.lean)
and the [verifier modules](../ProteinFolding/Cubic/Proofs/NPMembership.lean).
The source import graph is recorded in [source-manifest.json](../checks/source-manifest.json).

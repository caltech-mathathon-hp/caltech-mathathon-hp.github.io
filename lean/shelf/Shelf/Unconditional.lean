import Shelf.NPComplete
import ProteinFolding.Cubic.Proofs.Main
import ProteinFolding.Common.CookLevinProofUniversal

/-!
# The theorems with no hypothesis

The final theorems of `Shelf/NPComplete.lean` take the Cook–Levin theorem as a
hypothesis, `hCL : SAT.CookLevin`: SAT is NP-hard. The team has since proved it
in Lean (`SAT.CookLevinUniversal.cookLevin`, in the files
`ProteinFolding/Common/CookLevinProof*.lean` of `vendor/protein_folding`). Here we
put that proof in the place of the hypothesis. Nothing is assumed any more.

The second part does the same for the team's own final theorems, which go from
bin packing to perfect folding by the team's string instead of ours.
-/

namespace ProteinFolding.Shelf.Unconditional

open ProteinFolding

/-! ## By our reduction -/

/-- **Theorem 1, hardness.** PERFECT HP STRING-FOLD is NP-hard. -/
theorem perfectHPStringFold_NPHard : PerfectHPStringFoldNPHard :=
  Shelf.perfectHPStringFold_NPHard SAT.CookLevinUniversal.cookLevin

/-- **Theorem 1.** PERFECT HP STRING-FOLD is NP-complete. -/
theorem perfectHPStringFold_NPComplete : PerfectHPStringFoldNPComplete :=
  Shelf.perfectHPStringFold_NPComplete SAT.CookLevinUniversal.cookLevin

/-- **Corollary 2.** HP STRING-FOLD on the cubic lattice is NP-complete. -/
theorem hpStringFold_NPComplete : HPStringFoldNPComplete :=
  Shelf.hpStringFold_NPComplete SAT.CookLevinUniversal.cookLevin

/-! ## By the team's reduction

These are the team's theorems `ProteinFolding.perfectHPStringFold_NPComplete` and
`ProteinFolding.hpStringFold_NPComplete`, with the team's proof of the Cook–Levin
theorem in the place of their hypothesis. The statements are the same as above;
the string that the proof builds is the team's. -/

namespace TeamRoute

/-- PERFECT HP STRING-FOLD is NP-complete, by the team's reduction. -/
theorem perfectHPStringFold_NPComplete : PerfectHPStringFoldNPComplete :=
  _root_.ProteinFolding.perfectHPStringFold_NPComplete SAT.CookLevinUniversal.cookLevin

/-- HP STRING-FOLD on the cubic lattice is NP-complete, by the team's reduction. -/
theorem hpStringFold_NPComplete : HPStringFoldNPComplete :=
  _root_.ProteinFolding.hpStringFold_NPComplete SAT.CookLevinUniversal.cookLevin

end TeamRoute

end ProteinFolding.Shelf.Unconditional

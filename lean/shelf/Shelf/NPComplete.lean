import ProteinFolding.Cubic.Proofs.PackingToPerfectComputable
import ProteinFolding.Cubic.Proofs.SATPackingComputable
import ProteinFolding.Cubic.Proofs.NPMembership
import ProteinFolding.Cubic.Proofs.PerfectToHPComputable
import Shelf.Converse
import Shelf.Forward
import Shelf.NormaliseComputable
import Shelf.WordComputable

/-!
# Theorem 1 and Corollary 2

This file puts the pieces together.

* Theorems 12 and 16 make the reduction of our write-up correct on every input
  (`reductionCorrect`).
* A Turing machine computes the reduction in polynomial time
  (`shelfMap_polyTime`).
* The source problem is NP-hard: this is the team's reduction from SAT
  (`SATPacking.modifiedBinPackingUnary_NPHard`), given the Cook–Levin theorem.
* Both folding problems are in NP, and the perfect problem reduces to the
  threshold problem: these are the team's too.

The team's source problem is EXACT PACKING with the extra condition that every
size is even (`modifiedAccepts_iff`). So the map of the Karp reduction,
`shelfMap`, makes the team's check first, which also rejects an input with an odd
size, and on the inputs that pass the check it is the reduction of our write-up,
`shelfReduction`.

The final theorems have the hypothesis `hCL : SAT.CookLevin`, as in the team's
library: that SAT is NP-hard is not proved in Lean.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Computability Turing

/-- **Theorems 12 and 16 together.** The reduction of our write-up is correct on every
input: an input is a yes-instance of EXACT PACKING exactly when its string has a
perfect fold. -/
theorem reductionCorrect : ReductionCorrect :=
  reductionCorrect_of foldGivesPacking packingGivesFold

/-- The check that the machine makes before it writes the string, as a
proposition: every size is even, the numbers are positive and `∑ aᵢ = m · B`. -/
theorem sourceGuard_iff (I : Packing.Instance) :
    CubicPacking.sourceGuard I = true ↔ (∀ a ∈ I.sizes, Even a) ∧ Guard I := by
  rw [CubicPacking.sourceGuard_spec]
  unfold Guard
  tauto

/-- The map of the Karp reduction: check the input, normalise it, write the string
and the side of the cube. -/
def shelfMap (I : Packing.Instance) : PerfectInput :=
  if CubicPacking.sourceGuard I then (shelfWord (normalise I), side (normalise I)) else noInstance

/-- On an input that passes the check, the map is the reduction of our write-up. -/
theorem shelfMap_of_guard {I : Packing.Instance} (h : CubicPacking.sourceGuard I = true) :
    shelfMap I = shelfReduction I := by
  have hg : Guard I := ((sourceGuard_iff I).mp h).2
  simp [shelfMap, shelfReduction, h, hg]

/-- An input that fails the check is sent to the fixed no-instance. -/
theorem shelfMap_of_not_guard {I : Packing.Instance} (h : ¬ CubicPacking.sourceGuard I = true) :
    shelfMap I = noInstance := by
  simp [shelfMap, h]

/-- The map sends the yes-instances of the team's source problem (EXACT PACKING
with even sizes) to strings with a perfect fold, and every other input to a string
without one. -/
theorem shelfMap_correct (I : Packing.Instance) :
    Packing.ModifiedAccepts I ↔ PerfectFolds (shelfMap I) := by
  rw [modifiedAccepts_iff]
  by_cases h : CubicPacking.sourceGuard I = true
  · rw [shelfMap_of_guard h, ← reductionCorrect I]
    exact and_iff_right ((sourceGuard_iff I).mp h).1
  · rw [shelfMap_of_not_guard h]
    constructor
    · rintro ⟨he, ha⟩
      exact absurd ((sourceGuard_iff I).mpr ⟨he, guard_of_exactAccepts ha⟩) h
    · intro hf
      exact absurd hf noInstance_rejected

/-- What the machine computes is `shelfMap`: on an input that passes the check
every size is positive after the normalisation, so the machine's string
(`machineWord`) is the string `S`. -/
theorem machineMap_eq :
    (fun I : Packing.Instance =>
      if CubicPacking.sourceGuard I then (machineWord (normalise I), side (normalise I))
      else (([], 1) : PerfectInput)) = shelfMap := by
  funext I
  by_cases h : CubicPacking.sourceGuard I = true
  · have hg : Guard I := ((sourceGuard_iff I).mp h).2
    simp only [shelfMap, h, if_true]
    rw [machineWord_eq (normalised_normalise hg).size_pos]
  · simp only [shelfMap, h, if_false, noInstance, Bool.false_eq_true]

/-- **Proof of Theorem 1, "this takes polynomial time".** A Turing machine computes
the map in polynomial time, for sizes written in unary: it makes the check
(the team's machine), normalises the instance (`normaliseComputable`), and writes
the string and the side of the cube (`shelfPairComputable`). -/
theorem shelfMap_polyTime :
    Nonempty (TM2ComputableInPolyTime Packing.instanceEncoding perfectEncoding shelfMap) := by
  rw [← machineMap_eq]
  exact ⟨TM2Conditional.iteComputable CubicPacking.Guard.sourceGuardComputable
    (TM2CompositionPoly.compose normaliseComputable shelfPairComputable)
    (TM2Constants.constantComputable Packing.instanceEncoding perfectEncoding ([], 1))⟩

/-- The shelf map is a polynomial-time many-one reduction from the team's source
problem to PERFECT HP STRING-FOLD. -/
theorem shelfKarp :
    KarpReduces Packing.instanceEncoding perfectEncoding Packing.ModifiedAccepts PerfectFolds :=
  ⟨shelfMap, shelfMap_polyTime, shelfMap_correct⟩

/-- **Theorem 1, hardness.** PERFECT HP STRING-FOLD is NP-hard, given the
Cook–Levin theorem. -/
theorem perfectHPStringFold_NPHard (hCL : SAT.CookLevin) : PerfectHPStringFoldNPHard :=
  npHard_of_karpReduces (SATPacking.modifiedBinPackingUnary_NPHard hCL) shelfKarp

/-- **Theorem 1.** PERFECT HP STRING-FOLD is NP-complete, given the Cook–Levin
theorem. -/
theorem perfectHPStringFold_NPComplete (hCL : SAT.CookLevin) : PerfectHPStringFoldNPComplete :=
  ⟨perfectHPStringFold_inNP, perfectHPStringFold_NPHard hCL⟩

/-- **Corollary 2.** HP STRING-FOLD on the cubic lattice is NP-complete, given the
Cook–Levin theorem. -/
theorem hpStringFold_NPComplete (hCL : SAT.CookLevin) : HPStringFoldNPComplete :=
  ⟨hpStringFold_inNP, hpNPHard_of_perfectNPHard (perfectHPStringFold_NPHard hCL)⟩

end ProteinFolding.Shelf

import ProteinFolding.Cubic.MainTheorem
import ProteinFolding.Common.ComplexityComposition
import Shelf.Word

/-!
# What the shelf proof has to show

The problem statement is the team's, unchanged: `PerfectHPStringFold`,
`PerfectHPStringFoldNPHard`, `PerfectHPStringFoldNPComplete` and
`HPStringFoldNPComplete` from `ProteinFolding.Cubic`.

This file states the two directions of the reduction as propositions
(`def … : Prop`), in the style of that library, and shows that together they make
the reduction correct on every input (`reductionCorrect_of`). The two directions
are proved in `Shelf/Converse.lean` (Theorem 12) and `Shelf/Forward.lean`
(Theorem 16), and `Shelf/NPComplete.lean` draws the conclusion.

Numbers refer to `proof/paper/paper.tex`.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Computability Turing

/-- The predicate of PERFECT HP STRING-FOLD on raw inputs, as in the team's
`PerfectHPStringFoldNPHard`. -/
abbrev PerfectFolds (X : PerfectInput) : Prop :=
  PerfectHPStringFold X.1 X.2

/-- **Theorem 12** (a perfect fold gives a packing). If the string of a normalised
instance has a perfect fold, the instance has an exact packing. -/
def FoldGivesPacking : Prop :=
  ∀ J : Packing.Instance, Normalised J →
    PerfectHPStringFold (shelfWord J) (side J) → ∃ parts, Packing.Exact J parts

/-- **Theorem 16** (a packing gives a perfect fold). If a normalised instance has an
exact packing, its string has a perfect fold. -/
def PackingGivesFold : Prop :=
  ∀ J : Packing.Instance, Normalised J →
    (∃ parts, Packing.Exact J parts) → PerfectHPStringFold (shelfWord J) (side J)

/-- **Theorems 12 and 16 on raw inputs.** The reduction sends yes-instances to
yes-instances and no-instances to no-instances. -/
def ReductionCorrect : Prop :=
  ∀ I : Packing.Instance, ExactAccepts I ↔ PerfectFolds (shelfReduction I)

/-! ## How the two directions fit together -/

/-- The string that rejected inputs are sent to has no perfect fold: it has no
`H`, and a cube of side 1 needs one. -/
theorem noInstance_rejected : ¬ PerfectFolds noInstance := by
  rintro ⟨hcount, -⟩
  simp [noInstance, hydrophobicCount, hydrophobicIndices] at hcount

/-- Theorems 12 and 16 give the correctness of the reduction on every raw input.
The normalisation (`normalised_normalise`, `exists_exact_normalise_iff`) and the
rejected inputs (`noInstance_rejected`) are already proved. -/
theorem reductionCorrect_of (h12 : FoldGivesPacking) (h16 : PackingGivesFold) :
    ReductionCorrect := by
  intro I
  by_cases hg : Guard I
  · have hnorm := normalised_normalise hg
    have hiff := exists_exact_normalise_iff hg.1
    have hred : shelfReduction I = (shelfWord (normalise I), side (normalise I)) := by
      simp [shelfReduction, hg]
    rw [hred]
    constructor
    · rintro ⟨_, hp⟩
      exact h16 _ hnorm (hiff.mpr hp)
    · intro hf
      exact ⟨hg.1, hiff.mp (h12 _ hnorm hf)⟩
  · have hred : shelfReduction I = noInstance := by
      simp [shelfReduction, hg]
    rw [hred]
    constructor
    · intro h
      exact absurd (guard_of_exactAccepts h) hg
    · intro h
      exact absurd h noInstance_rejected

end ProteinFolding.Shelf

import ProteinFolding.Common.FoldConcatenation
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace ProteinFolding.Tetrahedral.ReductionTM2.PathOrientation

variable {V : Type} {G : SimpleGraph V} {L : ℕ}

def first (hL : 0 < L) : Fin L := ⟨0, hL⟩
def last (hL : 0 < L) : Fin L := ⟨L - 1, by omega⟩

theorem reverse_first (f : Fold G L) (hL : 0 < L) :
    f.reverse.pos (first hL) = f.pos (last hL) := rfl

theorem reverse_last (f : Fold G L) (hL : 0 < L) :
    f.reverse.pos (last hL) = f.pos (first hL) := by
  change f.pos (last hL).rev = f.pos (first hL)
  congr 1
  apply Fin.ext
  simp only [first, last, Fin.val_rev]
  omega

theorem endpoint_indices_ne (f : Fold G L) (hL : 2 ≤ L) (index : V → ℕ)
    (hinj : Function.Injective index) :
    index (f.pos (first (by omega))) ≠ index (f.pos (last (by omega))) := by
  intro he
  have hp := f.injective_pos (hinj he)
  have hv := congrArg Fin.val hp
  change 0 = L - 1 at hv
  omega

/-- Orient only the proof witness toward the larger endpoint index. The
actual machine independently discovers this same order by scanning starts. -/
def orient (f : Fold G L) (hL : 0 < L) (index : V → ℕ) : Fold G L :=
  if index (f.pos (first hL)) < index (f.pos (last hL)) then f else f.reverse

theorem ordered (f : Fold G L) (hL : 2 ≤ L) (index : V → ℕ) (hinj : Function.Injective index) :
    index ((orient f (by omega) index).pos (first (by omega))) <
      index ((orient f (by omega) index).pos (last (by omega))) := by
  by_cases h : index (f.pos (first (by omega))) < index (f.pos (last (by omega)))
  · simpa only [orient, if_pos h] using h
  · rw [orient, if_neg h, reverse_first, reverse_last]
    have hn := endpoint_indices_ne f hL index hinj
    omega

theorem sites (f : Fold G L) (hL : 0 < L) (index : V → ℕ) (w : V) :
    (∃ i, (orient f hL index).pos i = w) ↔ ∃ i, f.pos i = w := by
  unfold orient
  split
  · rfl
  · constructor
    · rintro ⟨i, hi⟩
      exact ⟨i.rev, hi⟩
    · rintro ⟨i, hi⟩
      refine ⟨i.rev, ?_⟩
      simpa only [Fold.reverse, Fin.rev_rev] using hi

section Degrees
variable [Fintype V] [DecidableRel G.Adj]

theorem first_degree_eq (f : Fold G L) (hL : 0 < L) (index : V → ℕ)
    (hf : G.degree (f.pos (first hL)) = 1) (hl : G.degree (f.pos (last hL)) = 1) :
    G.degree ((orient f hL index).pos (first hL)) = 1 := by
  by_cases h : index (f.pos (first hL)) < index (f.pos (last hL))
  · rw [orient, if_pos h]
    exact hf
  · rw [orient, if_neg h, reverse_first]
    exact hl

theorem last_degree_eq (f : Fold G L) (hL : 0 < L) (index : V → ℕ)
    (hf : G.degree (f.pos (first hL)) = 1) (hl : G.degree (f.pos (last hL)) = 1) :
    G.degree ((orient f hL index).pos (last hL)) = 1 := by
  by_cases h : index (f.pos (first hL)) < index (f.pos (last hL))
  · rw [orient, if_pos h]
    exact hl
  · rw [orient, if_neg h, reverse_last]
    exact hf

end Degrees

end ProteinFolding.Tetrahedral.ReductionTM2.PathOrientation

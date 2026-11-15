import ProteinFolding.Tetrahedral.ReductionTM2FoldNeighbours
import ProteinFolding.Tetrahedral.ReductionTM2WalkBounds

/-! Proof-only transfer from the existing finite component folds to the
computed natural-index walker. A fold is never an input to the machine. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2

open SimpleGraph

variable {V P : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def foldIndexPoint {L : ℕ} (f : Fold G L) (index : V → ℕ) (i : ℕ) : ℕ :=
  if hi : i < L then index (f.pos ⟨i, hi⟩) else 0

theorem indexedPath_of_fold {L N : ℕ} (hL : 2 ≤ L) (f : Fold G L)
    (hd : ∀ u, G.degree u ≤ 2)
    (hfirst : G.degree (f.pos ⟨0, by omega⟩) ≤ 1)
    (hlast : G.degree (f.pos ⟨L - 1, by omega⟩) ≤ 1)
    (index : V → ℕ) (hbound : ∀ u, index u < N) (hinj : Function.Injective index)
    (adj : P × (ℕ × ℕ) → Bool) (p : P)
    (hgraph : ∀ u k, k < N → (adj (p, (index u, k)) = true ↔ ∃ w, G.Adj u w ∧ index w = k)) :
    BoundedWalk.IndexedPath adj p N L (foldIndexPoint G f index) := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro i hi
    simpa only [foldIndexPoint, dif_pos hi] using hbound (f.pos ⟨i, hi⟩)
  · intro i hi j hj he
    simp only [foldIndexPoint, dif_pos hi, dif_pos hj] at he
    have hpos := f.injective_pos (hinj he)
    exact congrArg Fin.val hpos
  · intro i hi k hk
    rw [foldIndexPoint, dif_pos hi, hgraph _ k hk]
    constructor
    · rintro ⟨w, hw, he⟩
      rcases (fold_neighbours_iff G hL f hd hfirst hlast ⟨i, hi⟩ w).1 hw with
        ⟨j, hji, hjw⟩ | ⟨j, hij, hjw⟩
      · left
        change j.val + 1 = i at hji
        have hj : i - 1 = j.val := by omega
        refine ⟨by omega, ?_⟩
        rw [foldIndexPoint, dif_pos (by omega : i - 1 < L)]
        have hfin : (⟨i - 1, by omega⟩ : Fin L) = j := Fin.ext hj
        rw [hfin, hjw]
        exact he.symm
      · right
        change i + 1 = j.val at hij
        refine ⟨by have hj := j.isLt; omega, ?_⟩
        rw [foldIndexPoint, dif_pos (by have hj := j.isLt; omega : i + 1 < L)]
        have hfin : (⟨i + 1, by have hj := j.isLt; omega⟩ : Fin L) = j := Fin.ext hij
        rw [hfin, hjw]
        exact he.symm
    · rintro (⟨hip, he⟩ | ⟨hinext, he⟩)
      · let j : Fin L := ⟨i - 1, by omega⟩
        refine ⟨f.pos j, (f.consecutive j ⟨i, hi⟩ (by dsimp [j]; omega)).symm, ?_⟩
        simpa only [foldIndexPoint, dif_pos (by omega : i - 1 < L)] using he.symm
      · let j : Fin L := ⟨i + 1, hinext⟩
        refine ⟨f.pos j, f.consecutive ⟨i, hi⟩ j rfl, ?_⟩
        simpa only [foldIndexPoint, dif_pos hinext] using he.symm

end ProteinFolding.Tetrahedral.ReductionTM2

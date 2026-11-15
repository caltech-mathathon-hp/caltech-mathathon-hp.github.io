import ProteinFolding.Tetrahedral.ReductionTM2FoldNeighbours

namespace ProteinFolding.Tetrahedral.ReductionTM2

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem fold_leaf_index_end {L : ℕ} (f : Fold G L) (i : Fin L)
    (hdegree : G.degree (f.pos i) ≤ 1) : i.val = 0 ∨ i.val + 1 = L := by
  by_cases hi0 : i.val = 0
  · exact Or.inl hi0
  · by_cases hilast : i.val + 1 = L
    · exact Or.inr hilast
    · have hi := i.isLt
      let j : Fin L := ⟨i.val - 1, by omega⟩
      let k : Fin L := ⟨i.val + 1, by omega⟩
      have hj : G.Adj (f.pos i) (f.pos j) := (f.consecutive j i (by dsimp [j]; omega)).symm
      have hk : G.Adj (f.pos i) (f.pos k) := f.consecutive i k rfl
      have he := neighbour_of_degree_le_one G hdegree hj hk
      have hv := congrArg Fin.val (f.injective_pos he)
      dsimp [j, k] at hv
      omega

end ProteinFolding.Tetrahedral.ReductionTM2

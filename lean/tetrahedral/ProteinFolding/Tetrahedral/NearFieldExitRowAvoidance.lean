import ProteinFolding.Tetrahedral.NearFieldTetherRows
import ProteinFolding.Tetrahedral.NearFieldColumnPieces

/-! Both rows of an exit tether lie in the column-free margins b=j-1
and a=j-1. Thus every exit row avoids every canonical dangling column. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem exitRow_avoids_columns (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (exitRowCount p k)) : ¬ OnDanglingColumn p.side ((exitRowFold p k hk).pos i) := by
  have hr := p.separator_room k hk
  have ht := p.exit_column_triangle_room k
  have hj := p.tether_skin_bounds k hk
  unfold exitRowFold rowBAFold
  apply glue_property _ _ _ _ _ _ (fun q => ¬ OnDanglingColumn p.side q) ?_ ?_ i
  · intro r
    exact faceRowB_avoids_columns p.side (p.exitSkin k)
      (p.side - 3 - p.separatorIndex k + p.exitSkin k) (p.exitSkin k - 1)
      (p.separatorIndex k + 2) (exitRow_faceEquation p k hk)
      (by omega) (by omega) (by omega) r.val (by have h := r.isLt; omega)
  · intro r
    exact faceRowA_avoids_columns p.side (p.exitSkin k)
      (p.side - 3 - p.separatorIndex k + p.exitSkin k - (p.side - 2 - p.separatorIndex k))
      (p.exitSkin k - 1) (p.separatorIndex k + 2 + (p.side - 2 - p.separatorIndex k))
      (by have heq := exitRow_faceEquation p k hk; omega)
      (by omega) (by omega) (by omega) r.val (by have h := r.isLt; omega)

theorem exitRow_ne_column (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C : DanglingColumn p.side) (i : Fin (exitRowCount p k)) (n : ℕ) :
    (exitRowFold p k hk).pos i ≠ C.point n := by
  intro heq
  exact exitRow_avoids_columns p k hk i ⟨C, n, heq.symm⟩

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.NearFieldRightFinalColumn
import ProteinFolding.Tetrahedral.NearFieldTetherFamily

/-! The complete entry and exit tethers avoid the right filler's final
column at every height, including the actual two-row entry corner. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem entryRow_ne_rightFinalColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (entryRowCount p k)) (n : ℕ) :
    (entryRowFold p k hk).pos i ≠ (rightFinalColumn p).point n := by
  have hj := p.tether_skin_bounds k hk
  have ht := p.entry_column_triangle_room k hk
  have hm := p.side_ge
  unfold entryRowFold rowCBFold
  apply glue_property _ _ _ _ _ _ (fun x => x ≠ (rightFinalColumn p).point n) _ _ i
  · intro r
    exact entryRowC_ne_farColumn p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k) (3 * (k + 1) + p.entrySkin k)
      0 0 (p.side - 2) r.val n (entryRow_faceEquation p k hk) (by omega) (by omega)
  · intro r heq
    have hfree := faceRowB_avoids_columns p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k + (3 * (k + 1) + 1))
      (3 * (k + 1) + p.entrySkin k - (3 * (k + 1) + 1)) 1
      (by have h := entryRow_faceEquation p k hk; omega) (by omega) (by omega) (by omega)
      r.val (by have h := r.isLt; have hr := p.separator_room k hk; omega)
    exact hfree ⟨rightFinalColumn p, n, heq.symm⟩

theorem entryTetherFold_ne_rightFinalColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.entryTether k)) (n : ℕ) :
    (entryTetherFold p k hk).pos i ≠ (rightFinalColumn p).point n := by
  have hm := p.side_ge
  have hr := p.separator_room k hk
  apply entryTetherFold_property p k hk (fun x => x ≠ (rightFinalColumn p).point n) _ _ _ i
  · intro r
    exact borrowedPoint_ne_farColumn p.side (entryAnchorA p k) (3 * (k + 1)) 0 0 (p.side - 2)
      r.val n (entryAnchor_equation p k hk) (by omega) (entryAnchor_positive p k hk) (by omega)
  · exact fun r => entryRow_ne_rightFinalColumn p k hk r n
  · intro r
    exact faceColumns_ne_of_c_lt p.side (p.side - 2 - p.separatorIndex k) 0 (p.separatorIndex k)
      0 0 (p.side - 2) (by omega) (by omega) (by omega) r.rev.val n

theorem exitTetherFold_ne_rightFinalColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.exitTether k)) (n : ℕ) :
    (exitTetherFold p k hk).pos i ≠ (rightFinalColumn p).point n := by
  have hm := p.side_ge
  have hr := p.separator_room k hk
  have hf := p.rightFiller_ge
  have he := p.exit_column_triangle_room k
  apply exitTetherFold_property p k hk (fun x => x ≠ (rightFinalColumn p).point n) _ _ _ i
  · intro r
    exact faceColumns_ne_of_c_lt p.side (p.side - 3 - p.separatorIndex k) 0 (p.separatorIndex k + 1)
      0 0 (p.side - 2) (by omega) (by omega) (by omega) r.val n
  · intro r
    exact exitRow_ne_column p k hk (rightFinalColumn p) r n
  · intro r
    exact faceColumns_ne_of_c_lt p.side 0 (5 * p.exitSlot k + 3) (p.side - 5 - 5 * p.exitSlot k)
      0 0 (p.side - 2) (by omega) (by omega) (by omega) r.rev.val n

theorem tetherFold_ne_rightFinalColumn (p : ConstructionParameters) (t : TetherIndex p)
    (i : Fin (tetherCount p t)) (n : ℕ) :
    (tetherFold p t).pos i ≠ (rightFinalColumn p).point n := by
  rcases t with ⟨b, k⟩
  cases b
  · exact entryTetherFold_ne_rightFinalColumn p k.val (Nat.le_of_lt_succ k.isLt) i n
  · exact exitTetherFold_ne_rightFinalColumn p k.val (Nat.le_of_lt_succ k.isLt) i n

end ProteinFolding.Tetrahedral.NearField

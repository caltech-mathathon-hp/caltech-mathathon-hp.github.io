import ProteinFolding.Tetrahedral.NearFieldFrameTetherHalfspaces
import ProteinFolding.Tetrahedral.NearFieldDimerBulkClearance

/-! The ordinary A cap columns of the track run into Y < 0. They therefore
miss every frame P-link and all actual separator tethers at every height. -/

namespace ProteinFolding.Tetrahedral.NearField

def trackAColumn {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m) : DanglingColumn m where
  owner := octEdgeZigzag m trackEdgeFrame (2 * i)
  dir := 1
  owner_mem := by
    rcases octEdgeZigzag_mem hm trackEdgeFrame (show 2 * i < 2 * m - 1 by omega) with h | h <;> exact h.1.1
  seed_outside := by
    have h := octEdgeZigzag_even hm trackEdgeFrame i
    have hoct : octEdgeZigzag m trackEdgeFrame (2 * i) ∈ octahedron m := by
      rcases octEdgeZigzag_mem hm trackEdgeFrame (show 2 * i < 2 * m - 1 by omega) with h | h <;> exact h.1.1
    exact (step_not_mem_octahedron_A m h.1 hoct 1).mpr h.2.1

theorem trackAColumn_sy {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m) :
    (trackAColumn hm i hi).sy = -1 := by
  change (if InASublattice (octEdgeZigzag m trackEdgeFrame (2 * i)).val then bigFaceY 1 else -bigFaceY 1) = -1
  rw [if_pos (octEdgeZigzag_even hm trackEdgeFrame i).1]
  rfl

theorem trackAColumn_negativeY {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m) (n : ℕ) :
    bulkY m ((trackAColumn hm i hi).point n) ≤ -1 - (n : ℤ) := by
  have h := (trackAColumn hm i hi).point_signed_y n
  rw [trackAColumn_sy] at h
  omega

theorem FacePositive.ne_trackAColumn {m : ℕ} {s : Site} (hs : FacePositive m s)
    (hm : 1 ≤ m) (i : ℕ) (hi : i < m) (n : ℕ) : s ≠ (trackAColumn hm i hi).point n := by
  intro heq
  have hy := trackAColumn_negativeY hm i hi n
  rw [← heq] at hy
  have h := hs.2
  omega

theorem trackAColumn_ne_frameP {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m) (n f : ℕ)
    (kind : Fin 6) (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius m)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (trackAColumn hm i hi).point n ≠ nearFramePoint m f kind hf r := by
  intro heq
  have hn := trackAColumn_negativeY hm i hi n
  have hp := nearFrameP_positiveY m f kind hf hflo hfhi r hr0 hrlast
  rw [heq] at hn
  omega

theorem entryTetherFold_ne_trackAColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : ℕ) (hi : i < p.side) (n : ℕ) (r : Fin (p.entryTether k)) :
    (entryTetherFold p k hk).pos r ≠ (trackAColumn (m := p.side) (by have h := p.side_ge; omega) i hi).point n :=
  (entryTetherFold_positive p k hk r).ne_trackAColumn _ i hi n

theorem exitTetherFold_ne_trackAColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : ℕ) (hi : i < p.side) (n : ℕ) (r : Fin (p.exitTether k)) :
    (exitTetherFold p k hk).pos r ≠ (trackAColumn (m := p.side) (by have h := p.side_ge; omega) i hi).point n :=
  (exitTetherFold_positive p k hk r).ne_trackAColumn _ i hi n

theorem trackAColumn_ne_bulkColumn {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i < m)
    (C : DanglingColumn m) (hC : C.owner ∈ bulkInterior m) (n r : ℕ) :
    (trackAColumn hm i hi).point n ≠ C.point r := by
  apply Ne.symm
  exact bulkColumn_ne_edgeColumn C (trackAColumn hm i hi) hC
    (edgeZigzag_mem_deleted hm trackEdgeFrame (2 * i) (by omega)) r n

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.NearFieldBorrowedBulkClearance
import ProteinFolding.Tetrahedral.OctahedralEdgeUnion

/-! The selected borrowed-column owners are strictly between the adjoining
deleted edges, so no dimer PPP can mistake one for an H endpoint. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem aSecondRow_in_bulk (m t : ℕ) (ht : 1 ≤ t) (htm : t + 3 ≤ m) :
    aSecondRowSite m t ∈ bulkInterior m := by
  have hA : InASublattice (aSecondRowSite m t).val := aSecondRowCoordinates_inA m t
  have hinside : InOctahedron m (aSecondRowSite m t) := by
    apply (inOctahedron_iff_A m hA).mpr
    intro d
    fin_cases d <;> dsimp [aSecondRowSite, aSecondRowCoordinates, tetraCoordinate, octRadius]
    all_goals constructor <;> omega
  have hOct := (mem_octahedron m _).mpr hinside
  have hstrict : ∀ d, -octRadius m < tetraCoordinate m (aSecondRowSite m t).val d := by
    intro d
    fin_cases d <;> dsimp [aSecondRowSite, aSecondRowCoordinates, tetraCoordinate, octRadius] <;> omega
  refine Finset.mem_sdiff.mpr ⟨hOct, ?_⟩
  intro hdel
  obtain ⟨k, j, _, _, hj⟩ := (bulkOnDeletedEdge_A_iff m hA hOct).mp (Finset.mem_filter.mp hdel).2
  exact (ne_of_gt (hstrict j)) hj

theorem frameBorrowColumn_owner_in_bulk {m : ℕ} (hm : 1 ≤ m) (i : ℕ)
    (hi : i % 2 = 0) (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool)
    (hnear : mode = true ∨ 4 ≤ i) (hfar : mode = false ∨ (i : ℤ) + 4 ≤ octRadius m) :
    (frameBorrowColumn hm i hi hilo hihi mode).owner ∈ bulkInterior m := by
  change frameBorrowOwner hm i hi mode ∈ bulkInterior m
  rw [frameBorrowOwner_eq_aSecondRow hm i hi hilo mode]
  cases mode
  · simp only [Bool.false_eq_true, false_or] at hnear
    change aSecondRowSite m (i / 2 - 1) ∈ bulkInterior m
    apply aSecondRow_in_bulk m (i / 2 - 1)
    · omega
    · dsimp [octRadius] at hihi; omega
  · simp only [Bool.true_eq_false, false_or] at hfar
    change aSecondRowSite m (i / 2) ∈ bulkInterior m
    apply aSecondRow_in_bulk m (i / 2)
    · omega
    · dsimp [octRadius] at hfar; omega

end ProteinFolding.Tetrahedral.NearField

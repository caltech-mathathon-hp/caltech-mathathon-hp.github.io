import ProteinFolding.Tetrahedral.NearFieldBulkSecondRow
import ProteinFolding.Tetrahedral.NearFieldTetherFamily

/-! The c=1 entry row misses every bulk endpoint column: c=0 column
owners were deleted with the edges, and c=1 owners have degree two by N3.
All remaining row pieces lie in column-free margins. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem faceColumn_zero_c_owner_deleted (m a b : ℕ) (hs : a + b + 0 + 2 = m) :
    (faceDanglingColumn m a b 0 hs).owner ∈ bulkDeletedEdges m := by
  have hp := (faceDanglingColumn m a b 0 hs).owner_mem
  apply Finset.mem_filter.mpr
  refine ⟨hp, 2, 3, by decide, Or.inr ⟨⟨hp, faceSurfaceCoordinates_inB m 0 a b 0 hs, ?_⟩, ?_⟩⟩
  · change tetraCoordinate m (faceSurfaceSite m 0 a b 0 hs).val 3 = _
    rw [tetraCoordinate_faceSurface]
    rfl
  · change tetraCoordinate m (faceSurfaceSite m 0 a b 0 hs).val 2 = _
    rw [tetraCoordinate_faceSurface]
    dsimp [octRadius]
    omega

theorem entryRowC_ne_bulkEndColumn (m j a b r n : ℕ)
    (hm : 30 ≤ m) (hs : a + b + 1 + 2 = m + 2 * j) (hj : 1 ≤ j) (hr : r ≤ 2 * b)
    (C : DanglingColumn m) (howner : C.owner ∈ bulkInterior m)
    (hend : (bulkCoverNeighbours m C.owner).card = 1) :
    faceRowPoint 2 m j a b 1 hs r ≠ C.point n := by
  intro heq
  obtain ⟨a₀, b₀, c₀, hs₀, hC, hc⟩ := faceRowC_one_column_owners C hs hj hr heq.symm
  subst C
  rcases hc with rfl | rfl
  · exact (Finset.mem_sdiff.mp howner).2 (faceColumn_zero_c_owner_deleted m a₀ b₀ hs₀)
  · have hdegree := bulk_secondRow_degree m hm a₀ b₀ hs₀ howner
    exact (by decide : (2 : ℕ) ≠ 1) (hdegree.symm.trans hend)

theorem entryRow_ne_bulkEndColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C : DanglingColumn p.side) (howner : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1)
    (i : Fin (entryRowCount p k)) (n : ℕ) : (entryRowFold p k hk).pos i ≠ C.point n := by
  have hj := p.tether_skin_bounds k hk
  have ht := p.entry_column_triangle_room k hk
  unfold entryRowFold rowCBFold
  apply glue_property _ _ _ _ _ _ (fun q => q ≠ C.point n) ?_ ?_ i
  · intro r
    exact entryRowC_ne_bulkEndColumn p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k) (3 * (k + 1) + p.entrySkin k) r.val n
      (by have h := p.side_ge; omega) (entryRow_faceEquation p k hk) (by omega)
      (by have h := r.isLt; omega) C howner hend
  · intro r heq
    have hfree := faceRowB_avoids_columns p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k + (3 * (k + 1) + 1))
      (3 * (k + 1) + p.entrySkin k - (3 * (k + 1) + 1)) 1
      (by have h := entryRow_faceEquation p k hk; omega) (by omega) (by omega) (by omega)
      r.val (by have h := r.isLt; have hr := p.separator_room k hk; omega)
    exact hfree ⟨C, n, heq.symm⟩

end ProteinFolding.Tetrahedral.NearField

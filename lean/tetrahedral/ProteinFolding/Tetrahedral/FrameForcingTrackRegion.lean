import ProteinFolding.Tetrahedral.FrameForcingTrackHeights
import ProteinFolding.Tetrahedral.BulkMerges
import Mathlib.Tactic.ClearExcept

/-! Generic O7: the two strict height inequalities force an edge site onto
the interior of the third side of the shared small face. -/

namespace ProteinFolding.Tetrahedral

theorem frame_region_edge_indices (F : OctEdgeFrame) (f : Fin 4 → ℤ) (R δ : ℤ)
    (hR : 4 ≤ R) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hbound : ∀ d, -R - δ ≤ f d ∧ f d ≤ R - δ)
    (hsum : f F.k + f F.j + f F.a + f F.b = 0)
    (hH : 6 ≤ f F.a + f F.b) (hK : f F.a + f F.j ≤ -6)
    (k j : Fin 4) (hhigh : f k = R - δ) (hlow : f j = -R - δ) :
    k = F.b ∧ j = F.j := by
  have bk := hbound F.k
  have bj := hbound F.j
  have ba := hbound F.a
  have bb := hbound F.b
  constructor
  · rcases F.index_cases k with h | h | h | h
    · rw [h] at hhigh
      rcases F.index_cases j with h | h | h | h <;> rw [h] at hlow <;> omega
    · rw [h] at hhigh
      omega
    · rw [h] at hhigh
      omega
    · exact h
  · rcases F.index_cases j with h | h | h | h
    · rw [h] at hlow
      rcases F.index_cases k with h | h | h | h <;> rw [h] at hhigh <;> omega
    · exact h
    · rw [h] at hlow
      omega
    · rw [h] at hlow
      omega

theorem frame_deleted_edge_track_region (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (p : Site)
    (hedge : bulkOnDeletedEdge m p) (hH : 6 ≤ frameH2 m F p) (hK : frameK2 m F p ≤ -6) :
    ∃ r, 3 ≤ r ∧ r ≤ 2 * m - 5 ∧ p = octEdgeZigzag m F.smallOtherSide r := by
  obtain ⟨k, j, _, hEdge⟩ := hedge
  have hm1 : 1 ≤ m := by omega
  have hsum := tetraCoordinate_sum_frame m F p.val
  have hR : 4 ≤ octRadius m := by dsimp [octRadius]; omega
  have hindices : k = F.b ∧ j = F.j := by
    rcases hEdge with hEdge | hEdge
    · have hbound := (inOctahedron_iff_A m hEdge.1.2.1).mp ((mem_octahedron m p).mp hEdge.1.1)
      exact frame_region_edge_indices F (tetraCoordinate m p.val) (octRadius m) 0 hR (by decide) (by decide)
        (by simpa only [sub_zero] using hbound) hsum hH hK k j
        (by simpa only [sub_zero] using hEdge.1.2.2) (by simpa only [sub_zero] using hEdge.2)
    · have hbound := (inOctahedron_iff_B m hEdge.1.2.1).mp ((mem_octahedron m p).mp hEdge.1.1)
      have hbound' (d : Fin 4) : -octRadius m - 1 ≤ tetraCoordinate m p.val d ∧
          tetraCoordinate m p.val d ≤ octRadius m - 1 := by
        have h := hbound d
        dsimp [octRadius]
        omega
      exact frame_region_edge_indices F (tetraCoordinate m p.val) (octRadius m) 1 hR (by decide) (by decide)
        hbound' hsum hH hK k j (by have h := hEdge.2; dsimp [octRadius]; omega)
        (by have h := hEdge.1.2.2; dsimp [octRadius]; omega)
  rw [hindices.1, hindices.2] at hEdge
  obtain ⟨r, _, heq⟩ := (octEdgeSite_iff_param hm1 F.smallOtherSide p).mp hEdge
  have hdata := track_edge_height_data m hm1 F r
  rw [heq] at hH hK
  rw [hdata.1] at hH
  rw [hdata.2] at hK
  refine ⟨r, by omega, ?_, heq⟩
  dsimp [octRadius] at hK
  omega

end ProteinFolding.Tetrahedral

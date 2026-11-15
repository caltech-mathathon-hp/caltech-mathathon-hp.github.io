import ProteinFolding.Tetrahedral.FrameForcingSeparatorWindow
import ProteinFolding.Tetrahedral.FrameForcingTrackRegion

/-! Two occupied HH pairs at a separator seal each intervening track band
against both HH bonds and exterior P3 links. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

def frameTrackBand (m : ℕ) (F : OctEdgeFrame) (lo hi : ℕ) : Finset Site :=
  (Finset.Ico lo hi).image (frameTrackPoint m F)

theorem frameTrackBand_card (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (lo hi : ℕ) :
    (frameTrackBand m F lo hi).card = hi - lo := by
  rw [frameTrackBand, Finset.card_image_of_injective _ (frameTrackPoint_injective m hm F), Nat.card_Ico]

theorem frameTrackBand_closed (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (lo hi : ℕ)
    (hlo : 5 ≤ lo) (hhi : hi + 6 ≤ 2 * m) (V : Finset Site)
    (hV : V ⊆ bulkDeletedEdges m)
    (hguard : ∀ s ∈ Finset.Ico (lo - 2) lo ∪ Finset.Ico hi (hi + 2), frameTrackPoint m F s ∉ V) :
    ∀ x ∈ frameTrackBand m F lo hi, ∀ y ∈ V,
      (tetrahedralLattice.Adj x y ∨ OctTriangularNeighbours m x y) →
        y ∈ frameTrackBand m F lo hi := by
  intro x hx y hy hlink
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hrlo, hrhi⟩ := Finset.mem_Ico.mp hr
  have hr0 : r ≠ 0 := by omega
  have hH : -4 ≤ frameH2 m F y - frameH2 m F (frameTrackPoint m F r) ∧
      frameH2 m F y - frameH2 m F (frameTrackPoint m F r) ≤ 4 := by
    rcases hlink with h | h
    · have hb := frameH2_adj_bounds m F h
      constructor <;> omega
    · exact frameH2_triangular_bounds m F h
  have hK : -4 ≤ frameK2 m F y - frameK2 m F (frameTrackPoint m F r) ∧
      frameK2 m F y - frameK2 m F (frameTrackPoint m F r) ≤ 4 := by
    rcases hlink with h | h
    · have hb := frameK2_adj_bounds m F h
      constructor <;> omega
    · exact frameK2_triangular_bounds m F h
  rw [frameTrackPoint_H2 m (by omega) F r] at hH
  rw [frameTrackPoint_K2 m (by omega) F r hr0] at hK
  have hyH : 6 ≤ frameH2 m F y := by omega
  have hyK : frameK2 m F y ≤ -6 := by dsimp only [octRadius] at hK; omega
  obtain ⟨s, hslo, _, hys⟩ := frame_deleted_edge_track_region m hm F y (Finset.mem_filter.mp (hV hy)).2 hyH hyK
  have hys' : y = frameTrackPoint m F s := by
    rw [frameTrackPoint, if_neg (by omega : s ≠ 0)]
    exact hys
  rw [hys', frameTrackPoint_H2 m (by omega) F s] at hH
  have hsnear : r ≤ s + 2 ∧ s ≤ r + 2 := by omega
  have hsband : lo ≤ s ∧ s < hi := by
    by_contra hnot
    have hsGuard : s ∈ Finset.Ico (lo - 2) lo ∪ Finset.Ico hi (hi + 2) := by
      by_cases hsl : lo ≤ s
      · apply Finset.mem_union_right
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · apply Finset.mem_union_left
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    exact hguard s hsGuard (hys' ▸ hy)
  exact Finset.mem_image.mpr ⟨s, Finset.mem_Ico.mpr hsband, hys'.symm⟩

end ProteinFolding.Tetrahedral

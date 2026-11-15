import ProteinFolding.Tetrahedral.FrameForcingSlotGeometry
import ProteinFolding.Tetrahedral.BulkMerges

/-! A consecutive interior edge block is isolated after its two boundary
neighbours are occupied by the frame. -/

namespace ProteinFolding.Tetrahedral

def edgeBlock (m : ℕ) (F : OctEdgeFrame) (a n : ℕ) : Finset Site :=
  (Finset.range n).image (fun t => octEdgeZigzag m F (a + t))

theorem edgeBlock_card (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ) :
    (edgeBlock m F a n).card = n := by
  rw [edgeBlock, Finset.card_image_of_injective]
  · exact Finset.card_range n
  · intro i j heq
    have h := octEdgeZigzag_injective hm F heq
    omega

theorem edgeBlock_mem_edges (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ)
    (hbound : a + n ≤ 2 * m - 1) : edgeBlock m F a n ⊆ bulkDeletedEdges m := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  have ht' := Finset.mem_range.mp ht
  have hedge := octEdgeZigzag_mem hm F (by omega : a + t < 2 * m - 1)
  exact Finset.mem_filter.mpr ⟨(octEdgeSite_surface m hedge).1, F.k, F.j, F.kj, hedge⟩

theorem edgeBlock_isolated (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (a n : ℕ)
    (hlo : 2 ≤ a) (hhi : a + n + 1 ≤ 2 * m - 2) (V : Finset Site)
    (hV : V ⊆ bulkDeletedEdges m)
    (hleft : octEdgeZigzag m F (a - 1) ∉ V)
    (hright : octEdgeZigzag m F (a + n) ∉ V) :
    ∀ x ∈ edgeBlock m F a n, ∀ y ∈ V, tetrahedralLattice.Adj x y → y ∈ edgeBlock m F a n := by
  intro x hx y hy hadj
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  have ht' := Finset.mem_range.mp ht
  have hyEdge := Finset.mem_filter.mp (hV hy)
  obtain ⟨k, j, _, hyOn⟩ := hyEdge.2
  have hySurface := octEdgeSite_surface m hyOn
  obtain ⟨s, hs, heq, hadjIndex⟩ := inner_edge_surface_neighbour_index m hm F (a + t)
    (by omega) (by omega) y hySurface hadj
  by_cases hsin : a ≤ s ∧ s < a + n
  · apply Finset.mem_image.mpr
    refine ⟨s - a, Finset.mem_range.mpr (by omega), ?_⟩
    have hsum : a + (s - a) = s := by omega
    rw [hsum]
    exact heq.symm
  · have hboundary : s = a - 1 ∨ s = a + n := by omega
    rcases hboundary with h | h
    · have hbad : octEdgeZigzag m F (a - 1) ∈ V := by rw [← h, ← heq]; exact hy
      exact (hleft hbad).elim
    · have hbad : octEdgeZigzag m F (a + n) ∈ V := by rw [← h, ← heq]; exact hy
      exact (hright hbad).elim

end ProteinFolding.Tetrahedral

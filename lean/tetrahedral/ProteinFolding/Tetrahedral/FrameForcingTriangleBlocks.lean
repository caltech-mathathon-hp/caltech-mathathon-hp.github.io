import ProteinFolding.Tetrahedral.FrameForcingGapFamily
import ProteinFolding.Tetrahedral.FrameForcingTriangleIsolation

/-! Four occupied frame guards isolate an interior block under exterior P3
links as well as ordinary bonds. -/

namespace ProteinFolding.Tetrahedral

theorem edgeBlock_triangular_isolated (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (a n : ℕ)
    (hlo : 4 ≤ a) (hhi : a + n + 3 ≤ 2 * m - 2) (V : Finset Site)
    (hV : ∀ y ∈ V, bulkOnDeletedEdge m y)
    (hguard : ∀ r, r = a - 2 ∨ r = a - 1 ∨ r = a + n ∨ r = a + n + 1 →
      octEdgeZigzag m F r ∉ V) :
    ∀ x ∈ edgeBlock m F a n, ∀ y ∈ V,
      OctTriangularNeighbours m x y → y ∈ edgeBlock m F a n := by
  intro x hx y hy htri
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  have ht' := Finset.mem_range.mp ht
  obtain ⟨s, _, heq, hstep⟩ := far_edge_triangular_neighbour_index m hm F (a + t)
    (by omega) (by omega) y htri (hV y hy)
  by_cases hin : a ≤ s ∧ s < a + n
  · apply Finset.mem_image.mpr
    refine ⟨s - a, Finset.mem_range.mpr (by omega), ?_⟩
    have hsum : a + (s - a) = s := by omega
    rw [hsum]
    exact heq.symm
  · have hs : s = a - 2 ∨ s = a - 1 ∨ s = a + n ∨ s = a + n + 1 := by omega
    exact (hguard s hs (heq ▸ hy)).elim

theorem ForcedFrameFamily.guarded_gap_nodes {m H g₁ g₂}
    (F : ForcedFrameFamily m H g₁ g₂) (pre post : List ℕ) (k a n : ℕ)
    (heq : g₁ = pre ++ [0, k, 0] ++ post)
    (hprefix : (pre.map frameGapAdvance).sum + 2 = a)
    (hk : frameGapAdvance k = n + 1) :
    ∀ r, r = a - 2 ∨ r = a - 1 ∨ r = a + n ∨ r = a + n + 1 →
      octEdgeZigzag m F.first r ∈ H := by
  have hj : pre.length + 2 < g₁.length := by
    rw [heq, List.length_append, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  have hzero₁ : g₁[pre.length]'(by omega) = 0 := by
    have heq' : g₁ = pre ++ 0 :: (k :: 0 :: post) := by
      simpa only [List.append_assoc, List.cons_append] using heq
    exact List.getElem_of_append heq' rfl
  have hgap : g₁[pre.length + 1]'(by omega) = k := by
    have heq' : g₁ = (pre ++ [0]) ++ k :: (0 :: post) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using heq
    simpa only [List.length_append, List.length_singleton] using List.getElem_of_append heq' rfl
  have hzero₂ : g₁[pre.length + 2]'hj = 0 := by
    have heq' : g₁ = (pre ++ [0, k]) ++ 0 :: post := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using heq
    simpa only [List.length_append, List.length_cons, List.length_nil] using List.getElem_of_append heq' rfl
  have hpref : frameAdvanceAt g₁ pre.length + 2 = a := by
    unfold frameAdvanceAt
    rw [heq, List.append_assoc, List.take_left]
    exact hprefix
  have hnext₁ := frameAdvanceAt_next g₁ pre.length (by omega)
  have hnext₂ := frameAdvanceAt_next g₁ (pre.length + 1) (by omega)
  have hnext₃ := frameAdvanceAt_next g₁ (pre.length + 2) hj
  rw [hzero₁] at hnext₁
  rw [hgap, hk] at hnext₂
  rw [hzero₂] at hnext₃
  change frameAdvanceAt g₁ (pre.length + 1) = frameAdvanceAt g₁ pre.length + 1 at hnext₁
  change frameAdvanceAt g₁ (pre.length + 2) = frameAdvanceAt g₁ (pre.length + 1) + (n + 1) at hnext₂
  change frameAdvanceAt g₁ (pre.length + 3) = frameAdvanceAt g₁ (pre.length + 2) + 1 at hnext₃
  intro r hr
  rcases hr with hr | hr | hr | hr
  · have hind : r = frameAdvanceAt g₁ pre.length := by omega
    rw [hind]
    exact F.nodes₁ _ (by omega)
  · have hind : r = frameAdvanceAt g₁ (pre.length + 1) := by omega
    rw [hind]
    exact F.nodes₁ _ (by omega)
  · have hind : r = frameAdvanceAt g₁ (pre.length + 2) := by omega
    rw [hind]
    exact F.nodes₁ _ (by omega)
  · have hind : r = frameAdvanceAt g₁ (pre.length + 3) := by omega
    rw [hind]
    exact F.nodes₁ _ (by omega)

theorem ForcedFrameFamily.guarded_gap_triangular_isolated {m H g₁ g₂}
    (F : ForcedFrameFamily m H g₁ g₂) (hm : 3 ≤ m) (pre post : List ℕ) (k a n : ℕ)
    (heq : g₁ = pre ++ [0, k, 0] ++ post)
    (hprefix : (pre.map frameGapAdvance).sum + 2 = a)
    (hk : frameGapAdvance k = n + 1) (hlo : 4 ≤ a) (hhi : a + n + 3 ≤ 2 * m - 2) :
    ∀ x ∈ edgeBlock m F.first a n, ∀ y ∈ bulkDeletedEdges m \ (H ∪ octVertices m),
      OctTriangularNeighbours m x y → y ∈ edgeBlock m F.first a n := by
  apply edgeBlock_triangular_isolated m hm F.first a n hlo hhi
  · intro y hy
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hy).1).2
  · intro r hr hmem
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_union_left _
      (F.guarded_gap_nodes pre post k a n heq hprefix hk r hr))

end ProteinFolding.Tetrahedral

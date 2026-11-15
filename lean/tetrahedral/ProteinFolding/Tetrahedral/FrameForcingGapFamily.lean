import ProteinFolding.Tetrahedral.FrameForcingAmbient
import ProteinFolding.Tetrahedral.FrameForcingExitIndices
import ProteinFolding.Tetrahedral.FrameForcingSlotBlocks

/-! A derived description of the actual frame support, with no assumed
frame-rigidity predicate. Interior gaps are isolated ordinary-edge components. -/

namespace ProteinFolding.Tetrahedral

structure ForcedFrameFamily (m : ℕ) (H : Finset Site) (g₁ g₂ : List ℕ) where
  first : OctEdgeFrame
  second : OctEdgeFrame
  distinct : first.k ≠ second.k
  allowed₁ : ∀ k ∈ g₁, FrameGapAllowed k
  allowed₂ : ∀ k ∈ g₂, FrameGapAllowed k
  budget₁ : (g₁.map frameGapAdvance).sum = 2 * m - 2
  budget₂ : (g₂.map frameGapAdvance).sum = 2 * m - 2
  nodes₁ : ∀ j ≤ g₁.length, octEdgeZigzag m first (frameAdvanceAt g₁ j) ∈ H
  nodes₂ : ∀ j ≤ g₂.length, octEdgeZigzag m second (frameAdvanceAt g₂ j) ∈ H
  support_cases : ∀ x ∈ H,
    (∃ j ≤ g₁.length, x = octEdgeZigzag m first (frameAdvanceAt g₁ j)) ∨
      (∃ j ≤ g₂.length, x = octEdgeZigzag m second (frameAdvanceAt g₂ j))

def ForcedFrameFamily.swap {m H g₁ g₂} (F : ForcedFrameFamily m H g₁ g₂) :
    ForcedFrameFamily m H g₂ g₁ where
  first := F.second
  second := F.first
  distinct := Ne.symm F.distinct
  allowed₁ := F.allowed₂
  allowed₂ := F.allowed₁
  budget₁ := F.budget₂
  budget₂ := F.budget₁
  nodes₁ := F.nodes₂
  nodes₂ := F.nodes₁
  support_cases x hx := (F.support_cases x hx).symm

theorem ForcedFrameFamily.gap_disjoint_support {m H g₁ g₂}
    (F : ForcedFrameFamily m H g₁ g₂) (hm : 3 ≤ m) (j : ℕ) (hj : j < g₁.length)
    (a n : ℕ) (hbefore : frameAdvanceAt g₁ j + 1 = a)
    (hafter : frameAdvanceAt g₁ (j + 1) = a + n)
    (hlo : 2 ≤ a) (hhi : a + n + 1 ≤ 2 * m - 2) :
    Disjoint (edgeBlock m F.first a n) H := by
  apply Finset.disjoint_left.mpr
  intro x hx hH
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  have ht' := Finset.mem_range.mp ht
  rcases F.support_cases _ hH with ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩
  · have heqIndex := octEdgeZigzag_injective (by omega : 1 ≤ m) F.first heq
    exact frameAdvanceAt_avoids_gap g₁ F.allowed₁ j hj (a + t)
      (by omega) (by omega) q hq heqIndex.symm
  · have hbound := sum_map_take_le frameGapAdvance g₂ q
    rw [F.budget₂] at hbound
    change frameAdvanceAt g₂ q ≤ 2 * m - 2 at hbound
    have hedge := octEdgeZigzag_mem (by omega : 1 ≤ m) F.second (by omega : frameAdvanceAt g₂ q < 2 * m - 1)
    rw [← heq] at hedge
    have hid := inner_edge_unique_faces m hm F.first (a + t) (by omega) (by omega) hedge
    exact F.distinct hid.1.symm

theorem interior_edgeBlock_disjoint_vertices (m : ℕ) (hm : 3 ≤ m)
    (F : OctEdgeFrame) (a n : ℕ) (hlo : 2 ≤ a) (hhi : a + n + 1 ≤ 2 * m - 2) :
    Disjoint (edgeBlock m F a n) (octVertices m) := by
  apply Finset.disjoint_left.mpr
  intro x hx hv
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  have ht' := Finset.mem_range.mp ht
  rcases octEdgeZigzag_vertex_endpoints m (by omega) F (a + t) hv with heq | heq
  · have heq' : octEdgeZigzag m F (a + t) = octEdgeZigzag m F 0 := heq
    have hindex := octEdgeZigzag_injective (by omega : 1 ≤ m) F heq'
    omega
  · have hindex := octEdgeZigzag_injective (by omega : 1 ≤ m) F heq
    omega

theorem ForcedFrameFamily.gap_block {m H g₁ g₂}
    (F : ForcedFrameFamily m H g₁ g₂) (hm : 3 ≤ m) (j : ℕ) (hj : j < g₁.length)
    (a n : ℕ) (hbefore : frameAdvanceAt g₁ j + 1 = a)
    (hafter : frameAdvanceAt g₁ (j + 1) = a + n)
    (hlo : 2 ≤ a) (hhi : a + n + 1 ≤ 2 * m - 2) :
    edgeBlock m F.first a n ⊆ bulkDeletedEdges m \ (H ∪ octVertices m) ∧
      (∀ x ∈ edgeBlock m F.first a n, ∀ y ∈ bulkDeletedEdges m \ (H ∪ octVertices m),
        tetrahedralLattice.Adj x y → y ∈ edgeBlock m F.first a n) := by
  have hW := subset_sdiff_union_of_disjoint _ _ _ _
    (edgeBlock_mem_edges m (by omega) F.first a n (by omega))
    (F.gap_disjoint_support hm j hj a n hbefore hafter hlo hhi)
    (interior_edgeBlock_disjoint_vertices m hm F.first a n hlo hhi)
  refine ⟨hW, ?_⟩
  apply edgeBlock_isolated m hm F.first a n hlo hhi _ Finset.sdiff_subset
  · intro hmem
    have hH := F.nodes₁ j (by omega)
    have hind : a - 1 = frameAdvanceAt g₁ j := by omega
    rw [hind] at hmem
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_union_left _ hH)
  · intro hmem
    have hH := F.nodes₁ (j + 1) (by omega)
    rw [hafter] at hH
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_union_left _ hH)

namespace ConstructionParameters

theorem frameWord_forced_family (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord) :
    Nonempty (ForcedFrameFamily p.side (hSupport p.frameWord P.toFold) p.frameGaps1 p.frameGaps2) := by
  obtain ⟨F₁, F₂, _, _, _, hf₁, hf₂, hdistinct, _⟩ := p.frame_word_forced_incidence P
  refine ⟨{
    first := F₁
    second := F₂
    distinct := hdistinct
    allowed₁ := p.frameGaps1_allowed
    allowed₂ := p.frameGaps2_allowed
    budget₁ := p.frameGaps1_budget
    budget₂ := p.frameGaps2_budget
    nodes₁ := ?_
    nodes₂ := ?_
    support_cases := ?_ }⟩
  · intro j hj
    unfold frameAdvanceAt
    rw [← hf₁ j hj]
    exact P.site_mem_Hsupport _ (p.frameWord_gap1_H j hj)
  · intro j hj
    unfold frameAdvanceAt
    rw [← hf₂ j hj]
    exact P.site_mem_Hsupport _ (p.frameWord_gap2_H j hj)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := (mem_hSupport p.frameWord P.toFold x).mp hx
    have hi' := List.getElem?_eq_some_iff.mpr ⟨i.isLt, hi⟩
    rcases p.frame_word_H_cases i.val hi' with ⟨j, hj, heq⟩ | ⟨j, hj, heq⟩
    · exact Or.inl ⟨j, hj, by simpa only [OctWordPath.toFold, heq] using hf₁ j hj⟩
    · exact Or.inr ⟨j, hj, by simpa only [OctWordPath.toFold, heq] using hf₂ j hj⟩

end ConstructionParameters

end ProteinFolding.Tetrahedral

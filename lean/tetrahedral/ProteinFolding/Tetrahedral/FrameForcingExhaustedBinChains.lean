import ProteinFolding.Tetrahedral.FrameForcingBinRegions
import ProteinFolding.Tetrahedral.FrameForcingCatalogueGeometry
import ProteinFolding.Tetrahedral.FrameForcingBandChains
import ProteinFolding.Tetrahedral.FrameForcingAmbient

/-! Exhaustion of the size-two chains makes the separator guards closed
for every other actual catalogue chain, so every chain meeting a bin stays
whole inside it. -/

namespace ProteinFolding.Tetrahedral.DimerCatalogue

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem bin_chain_of_double_exhaustion {α : Type} {S : Sequence}
    (c : DimerCatalogue α S) (f : Fold tetrahedralLattice S.length)
    (p : ConstructionParameters) (hsupport : hSupport S f = octahedron p.side)
    (F : OctEdgeFrame) (starts : Fin (p.bins + 1) → ℕ)
    (hwindow : ∀ k, |(starts k : ℤ) - (p.separatorIndex k.val : ℤ)| ≤ (p.separatorRadius : ℤ))
    (hexhaust : ((@Finset.univ c.Index c.finiteIndex).filter (fun i => c.q i = 2)).biUnion (c.chainSites f) =
      Finset.univ.biUnion (fun k => frameTrackBand p.side F (2 * starts k) (2 * starts k + 4)))
    (k : Fin p.bins) (t : c.Index)
    (hmeet : (c.chainSites f t ∩ p.binTrackRegion F starts k).Nonempty) :
    c.q t ≠ 2 ∧ c.chainSites f t ⊆ p.binTrackRegion F starts k := by
  classical
  letI := c.finiteIndex
  let Q2 := (Finset.univ.filter (fun i => c.q i = 2)).biUnion (c.chainSites f)
  change Q2 = _ at hexhaust
  have hdisjoint : Disjoint (p.binTrackRegion F starts k) Q2 := by
    rw [hexhaust]
    apply Finset.disjoint_left.mpr
    intro x hx hq
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hq
    exact Finset.disjoint_left.mp (p.binTrackRegion_disjoint_separator F starts hwindow k l) hx hl
  have ht : c.q t ≠ 2 := by
    intro ht
    obtain ⟨x, hx⟩ := hmeet
    obtain ⟨hxC, hxW⟩ := Finset.mem_inter.mp hx
    exact Finset.disjoint_left.mp hdisjoint hxW (Finset.mem_biUnion.mpr
      ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, hxC⟩)
  let V := bulkDeletedEdges p.side \ Q2
  have hV : V ⊆ bulkDeletedEdges p.side := Finset.sdiff_subset
  have hsub : c.chainSites f t ⊆ V := by
    intro x hx
    apply Finset.mem_sdiff.mpr
    refine ⟨foldDimerPairs_subset_edges S f p.side hsupport (c.chainSites_subset f t hx), ?_⟩
    intro hq
    obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.mp hq
    have hqu : c.q u = 2 := (Finset.mem_filter.mp hu).2
    have htu : t ≠ u := by intro he; subst u; exact ht hqu
    exact Finset.disjoint_left.mp (c.chainSites_disjoint f t u htu) hx hxu
  have hguard : ∀ s ∈
      Finset.Ico (2 * starts (p.binLeftIndex k) + 4 - 2) (2 * starts (p.binLeftIndex k) + 4) ∪
        Finset.Ico (2 * starts (p.binRightIndex k)) (2 * starts (p.binRightIndex k) + 2),
      frameTrackPoint p.side F s ∉ V := by
    intro s hs hmem
    have hnot := (Finset.mem_sdiff.mp hmem).2
    apply hnot
    rw [hexhaust]
    rcases Finset.mem_union.mp hs with hs | hs
    · apply Finset.mem_biUnion.mpr
      refine ⟨p.binLeftIndex k, Finset.mem_univ _, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨s, Finset.mem_Ico.mpr ?_, rfl⟩
      have hb := Finset.mem_Ico.mp hs
      constructor <;> omega
    · apply Finset.mem_biUnion.mpr
      refine ⟨p.binRightIndex k, Finset.mem_univ _, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨s, Finset.mem_Ico.mpr ?_, rfl⟩
      have hb := Finset.mem_Ico.mp hs
      constructor <;> omega
  have hm := p.side_ge
  have hmarg := p.binTrackRegion_margins F starts hwindow k
  obtain ⟨x, hx⟩ := hmeet
  obtain ⟨hxC, hxW⟩ := Finset.mem_inter.mp hx
  obtain ⟨⟨i, b⟩, _, rfl⟩ := Finset.mem_image.mp hxC
  refine ⟨ht, ?_⟩
  exact factorDimerPairs_band_all S f p.side (by omega) hsupport (c.pre t) (c.post t) (c.q t) (c.factor t)
    F _ _ hmarg.1 hmarg.2.1 V hV hsub hguard ⟨i, b, hxW⟩

end ProteinFolding.Tetrahedral.DimerCatalogue

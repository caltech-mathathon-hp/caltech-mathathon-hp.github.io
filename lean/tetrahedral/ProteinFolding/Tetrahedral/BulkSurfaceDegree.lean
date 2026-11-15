import ProteinFolding.Tetrahedral.BulkBoundaryEnds

/-! Unpatched surface sites always retain an inward foliation partner. -/

namespace ProteinFolding.Tetrahedral

theorem octVertices_subset_bulkDeleted {m : ℕ} (hm : 1 ≤ m) :
    octVertices m ⊆ bulkDeletedEdges m := by
  intro p hp
  obtain ⟨⟨a, s⟩, _, rfl⟩ := Finset.mem_image.mp hp
  have hOct := octVertexSite_mem_octahedron hm a s
  have hA := octVertexCoordinates_inA m a s
  apply Finset.mem_filter.mpr
  refine ⟨hOct, ?_⟩
  fin_cases a <;> cases s
  all_goals first
    | (refine ⟨0, 1, by decide, Or.inl ⟨⟨hOct, hA, ?_⟩, ?_⟩⟩ <;>
        dsimp [tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre, octRadius] <;> omega)
    | (refine ⟨0, 2, by decide, Or.inl ⟨⟨hOct, hA, ?_⟩, ?_⟩⟩ <;>
        dsimp [tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre, octRadius] <;> omega)
    | (refine ⟨1, 0, by decide, Or.inl ⟨⟨hOct, hA, ?_⟩, ?_⟩⟩ <;>
        dsimp [tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre, octRadius] <;> omega)
    | (refine ⟨2, 0, by decide, Or.inl ⟨⟨hOct, hA, ?_⟩, ?_⟩⟩ <;>
        dsimp [tetraCoordinate, octVertexSite, octVertexCoordinates, octCentre, octRadius] <;> omega)

theorem bulkInterior_not_vertex {m : ℕ} (hm : 1 ≤ m) {p : Site} (hp : p ∈ bulkInterior m) :
    p ∉ octVertices m := by
  intro hv
  exact (Finset.mem_sdiff.mp hp).2 (octVertices_subset_bulkDeleted hm hv)

theorem bulkBaseNeighbours_surface_eq_inside (m : ℕ) (p : Site)
    (hp : p ∈ bulkInterior m) (hs : OctSurfaceSite m p) :
    bulkBaseNeighbours m p = (bulkRungNeighbours m p).filter (fun q => q ∈ octahedron m) := by
  ext q
  simp only [bulkBaseNeighbours, Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨hrung, hq⟩
    exact ⟨hrung, (Finset.mem_sdiff.mp hq).1⟩
  · rintro ⟨hrung, hq⟩
    refine ⟨hrung, Finset.mem_sdiff.mpr ⟨hq, ?_⟩⟩
    intro hdel
    obtain ⟨k, j, _, hedge⟩ := (Finset.mem_filter.mp hdel).2
    have hqSurface := octEdgeSite_surface m hedge
    exact bulkInterior_no_surface_bond m hp hs hqSurface
      ((bulkRungGraph_adj_iff m p q).mpr hrung).1

theorem bulkBaseNeighbours_surface_positive {m : ℕ} (hm : 1 ≤ m) (p : Site)
    (hp : p ∈ bulkInterior m) (hs : OctSurfaceSite m p) :
    1 ≤ (bulkBaseNeighbours m p).card := by
  have hDang := nonvertex_dangling_le_one m (Finset.mem_sdiff.mp hp).1 (bulkInterior_not_vertex hm hp)
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := bulkRungNeighbours m p) (p := fun q => q ∈ octahedron m)
  rw [← bulkBaseNeighbours_surface_eq_inside m p hp hs, bulkRungNeighbours_card] at hpart
  have hsub : (bulkRungNeighbours m p).filter (fun q => q ∉ octahedron m) ⊆
      externalNeighbours (octahedron m) p := by
    intro q hq
    have hf := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨(mem_neighbours p q).mpr
      ((bulkRungGraph_adj_iff m p q).mpr hf.1).1, hf.2⟩
  have hout := Finset.card_le_card hsub
  rw [← octDanglingDirections_card_eq_external] at hout
  omega

theorem bulkCover_surface_positive_of_not_support {m : ℕ} (hm : 1 ≤ m) (p : Site)
    (hp : p ∈ bulkInterior m) (hs : OctSurfaceSite m p) (hn : p ∉ bulkPatchSupport m) :
    1 ≤ (bulkCoverNeighbours m p).card := by
  rw [bulkCoverNeighbours_eq_merged_of_not_support m p hp hn]
  have hBase := bulkBaseNeighbours_surface_positive hm p hp hs
  have hSub : bulkBaseNeighbours m p ⊆ bulkMergedNeighbours m p := Finset.subset_union_left
  exact hBase.trans (Finset.card_le_card hSub)

end ProteinFolding.Tetrahedral

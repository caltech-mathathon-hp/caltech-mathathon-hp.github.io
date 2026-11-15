import ProteinFolding.Tetrahedral.BulkPatchSupport

/-! Nonsurface vertices away from damaged ends already have full foliation degree.
Two surface endpoints can never make a two-site bulk run, by O3. -/

namespace ProteinFolding.Tetrahedral

theorem bulkInterior_no_surface_bond (m : ℕ) {p q : Site}
    (hp : p ∈ bulkInterior m) (hps : OctSurfaceSite m p) (hqs : OctSurfaceSite m q) :
    ¬tetrahedralLattice.Adj p q := by
  intro hpq
  have hpParts := Finset.mem_sdiff.mp hp
  apply hpParts.2
  apply Finset.mem_filter.mpr
  refine ⟨hpParts.1, ?_⟩
  rcases p.property with hpA | hpB
  · obtain ⟨k, j, hkj, hpEdge, _⟩ := bonded_surface_sites_on_edge m hpA hps hqs hpq
    exact ⟨k, j, hkj, Or.inl hpEdge⟩
  · have hqA : InASublattice q.val :=
      (adj_not_same_sublattice hpq.symm).mpr ((inB_iff_not_inA p).mp hpB)
    obtain ⟨k, j, hkj, _, hpEdge⟩ := bonded_surface_sites_on_edge m hqA hqs hps hpq.symm
    exact ⟨k, j, hkj, Or.inr hpEdge⟩

theorem bulkCover_no_surface_bond (m : ℕ) {p q : Site}
    (h : (bulkCoverGraph m).Adj p q) (hps : OctSurfaceSite m p) (hqs : OctSurfaceSite m q) : False :=
  bulkInterior_no_surface_bond m h.1 hps hqs (bulkCoverBond_adj m h)

theorem nonsurface_neighbour_inside (m : ℕ) {p q : Site} (hp : p ∈ octahedron m)
    (hn : ¬OctSurfaceSite m p) (h : tetrahedralLattice.Adj p q) : q ∈ octahedron m := by
  by_contra hq
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp h
  apply hn
  refine ⟨hp, Finset.card_pos.mpr ⟨d, ?_⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩

theorem bulkBaseNeighbours_full_of_nondamaged (m : ℕ) (p : Site)
    (hp : p ∈ bulkInterior m) (hn : ¬OctSurfaceSite m p) (hd : p ∉ bulkDamaged m) :
    bulkBaseNeighbours m p = bulkRungNeighbours m p := by
  apply Finset.inter_eq_left.mpr
  intro q hq
  have hrung := (bulkRungGraph_adj_iff m p q).mpr hq
  apply Finset.mem_sdiff.mpr
  refine ⟨nonsurface_neighbour_inside m (Finset.mem_sdiff.mp hp).1 hn hrung.1, ?_⟩
  intro hdel
  apply hd
  exact Finset.mem_filter.mpr ⟨hp, q, Finset.mem_inter.mpr ⟨hq, hdel⟩⟩

theorem bulkIncidentMerges_empty_of_nondamaged (m : ℕ) (p : Site)
    (hn : ¬OctSurfaceSite m p) (hd : p ∉ bulkDamaged m) : bulkIncidentMerges m p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  rcases (Finset.mem_filter.mp hq).2 with h | h
  · exact hd h.1
  · exact hn (bulkMerge_target_surface m h)

theorem bulkMergedNeighbours_full_of_nondamaged (m : ℕ) (p : Site)
    (hp : p ∈ bulkInterior m) (hn : ¬OctSurfaceSite m p) (hd : p ∉ bulkDamaged m) :
    (bulkMergedNeighbours m p).card = 2 := by
  unfold bulkMergedNeighbours
  rw [bulkIncidentMerges_empty_of_nondamaged m p hn hd, Finset.union_empty,
    bulkBaseNeighbours_full_of_nondamaged m p hp hn hd, bulkRungNeighbours_card]

theorem bulkCover_nondamaged_nonsurface_degree (m : ℕ) (p : Site)
    (hp : p ∈ bulkInterior m) (hn : ¬OctSurfaceSite m p) (hd : p ∉ bulkDamaged m)
    (hs : p ∉ bulkPatchSupport m) : (bulkCoverNeighbours m p).card = 2 := by
  rw [bulkCoverNeighbours_eq_merged_of_not_support m p hp hs]
  exact bulkMergedNeighbours_full_of_nondamaged m p hp hn hd

theorem bulkCover_no_leaf_pair_of_nonsurface_degree (m : ℕ)
    (hfull : ∀ p ∈ bulkInterior m, ¬OctSurfaceSite m p → 2 ≤ (bulkCoverNeighbours m p).card)
    {p q : Site} (h : (bulkCoverGraph m).Adj p q)
    (hp : (bulkCoverNeighbours m p).card = 1) (hq : (bulkCoverNeighbours m q).card = 1) : False := by
  have hps : OctSurfaceSite m p := by
    by_contra hn
    have hb := hfull p h.1 hn
    omega
  have hqs : OctSurfaceSite m q := by
    by_contra hn
    have hb := hfull q h.2.1 hn
    omega
  exact bulkCover_no_surface_bond m h hps hqs

end ProteinFolding.Tetrahedral

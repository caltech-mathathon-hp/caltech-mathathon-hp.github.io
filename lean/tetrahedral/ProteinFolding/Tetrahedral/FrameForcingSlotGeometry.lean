import ProteinFolding.Tetrahedral.FrameForcingCaps

/-! Away from vertices and B-corners an edge site belongs to just one edge.
Thus a bonded surface neighbour remains on that same zigzag. -/

namespace ProteinFolding.Tetrahedral

theorem inner_edge_unique_faces (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hrlo : 2 ≤ r) (hrhi : r + 2 ≤ 2 * m - 2) {k j : Fin 4}
    (hedge : OctEdgeSite m k j (octEdgeZigzag m F r)) : k = F.k ∧ j = F.j := by
  have hm1 : 1 ≤ m := by omega
  have hmod := Nat.mod_lt r (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div r 2
  by_cases heven : r % 2 = 0
  · have hr : r = 2 * (r / 2) := by omega
    rw [hr] at hedge
    obtain ⟨hpA, hk, hj, ha, hb⟩ := octEdgeZigzag_even hm1 F (r / 2)
    rcases hedge with hedge | hedge
    · have hforeignK := hedge.1.2.2
      have hforeignJ := hedge.2
      constructor
      · rcases F.index_cases k with h | h | h | h
        · exact h
        all_goals rw [h] at hforeignK
        all_goals dsimp [octRadius] at hforeignK hk hj ha hb
        all_goals omega
      · rcases F.index_cases j with h | h | h | h
        · rw [h] at hforeignJ
          dsimp [octRadius] at hforeignJ hk
          omega
        · exact h
        · rw [h] at hforeignJ
          dsimp [octRadius] at hforeignJ ha
          omega
        · rw [h] at hforeignJ
          dsimp [octRadius] at hforeignJ hb
          omega
    · exact (sublattices_disjoint _ hpA hedge.1.2.1).elim
  · have hr : r = 2 * (r / 2) + 1 := by omega
    rw [hr] at hedge
    obtain ⟨hpB, hk, hj, ha, hb⟩ := octEdgeZigzag_odd hm1 F (r / 2)
    rcases hedge with hedge | hedge
    · exact (sublattices_disjoint _ hedge.1.2.1 hpB).elim
    · have hforeignK := hedge.2
      have hforeignJ := hedge.1.2.2
      constructor
      · rcases F.index_cases k with h | h | h | h
        · exact h
        all_goals rw [h] at hforeignK
        all_goals dsimp [octRadius] at hforeignK hk hj ha hb
        all_goals omega
      · rcases F.index_cases j with h | h | h | h
        · rw [h] at hforeignJ
          dsimp [octRadius] at hforeignJ hk
          omega
        · exact h
        · rw [h] at hforeignJ
          dsimp [octRadius] at hforeignJ ha
          omega
        · rw [h] at hforeignJ
          dsimp [octRadius] at hforeignJ hb
          omega

theorem inner_edge_surface_neighbour (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hrlo : 2 ≤ r) (hrhi : r + 2 ≤ 2 * m - 2) (q : Site)
    (hq : OctSurfaceSite m q) (hadj : tetrahedralLattice.Adj (octEdgeZigzag m F r) q) :
    OctEdgeSite m F.k F.j q := by
  have hm1 : 1 ≤ m := by omega
  have hp := octEdgeSite_surface m (octEdgeZigzag_mem hm1 F (by omega : r < 2 * m - 1))
  rcases (octEdgeZigzag m F r).property with hpA | hpB
  · obtain ⟨k, j, _, hleft, hright⟩ := bonded_surface_sites_on_edge m hpA hp hq hadj
    have hid := inner_edge_unique_faces m hm F r hrlo hrhi (Or.inl hleft)
    rw [hid.1, hid.2] at hright
    exact Or.inr hright
  · have hqA : InASublattice q.val := by
      rcases adj_sublattices hadj with h | h
      · exact (sublattices_disjoint _ h.1 hpB).elim
      · exact h.2
    obtain ⟨k, j, _, hleft, hright⟩ := bonded_surface_sites_on_edge m hqA hq hp hadj.symm
    have hid := inner_edge_unique_faces m hm F r hrlo hrhi (Or.inr hright)
    rw [hid.1, hid.2] at hleft
    exact Or.inl hleft

theorem inner_edge_surface_neighbour_index (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hrlo : 2 ≤ r) (hrhi : r + 2 ≤ 2 * m - 2) (q : Site)
    (hq : OctSurfaceSite m q) (hadj : tetrahedralLattice.Adj (octEdgeZigzag m F r) q) :
    ∃ s < 2 * m - 1, q = octEdgeZigzag m F s ∧ (r + 1 = s ∨ s + 1 = r) := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨s, hs, heq⟩ := (octEdgeSite_iff_param hm1 F q).mp
    (inner_edge_surface_neighbour m hm F r hrlo hrhi q hq hadj)
  refine ⟨s, hs, heq, ?_⟩
  rw [heq] at hadj
  exact (octEdgeZigzag_adj_iff hm1 F r s).mp hadj

end ProteinFolding.Tetrahedral

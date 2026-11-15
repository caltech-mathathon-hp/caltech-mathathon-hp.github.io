import ProteinFolding.Tetrahedral.FrameForcingSlotGeometry
import ProteinFolding.Tetrahedral.OctahedralTriangleSides
import ProteinFolding.Tetrahedral.BulkMerges

/-! A P3 link from an interior edge site to another edge site stays on
that edge and changes its zigzag index by exactly two. -/

namespace ProteinFolding.Tetrahedral

theorem triangular_neighbours_same_sublattice {m : ℕ} {p q : Site}
    (h : OctTriangularNeighbours m p q) :
    (InASublattice p.val ∧ InASublattice q.val) ∨ (InBSublattice p.val ∧ InBSublattice q.val) := by
  rcases p.property with hp | hp
  · obtain ⟨i, l, _, rfl⟩ := triangular_neighbours_A_step hp h
    exact Or.inl ⟨hp, step_in_A (step_in_B hp l) i⟩
  · obtain ⟨i, l, _, rfl⟩ := triangular_neighbours_B_step hp h
    exact Or.inr ⟨hp, step_in_B (step_in_A hp l) i⟩

theorem far_edge_triangular_neighbour_faces (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (r : ℕ) (hrlo : 4 ≤ r) (hrhi : r + 4 ≤ 2 * m - 2) (q : Site)
    (htri : OctTriangularNeighbours m (octEdgeZigzag m F r) q)
    {k j : Fin 4} (hq : OctEdgeSite m k j q) : k = F.k ∧ j = F.j := by
  have hm1 : 1 ≤ m := by omega
  have hmod := Nat.mod_lt r (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div r 2
  have hsame := triangular_neighbours_same_sublattice htri
  have hchangeK := triangular_neighbours_coordinate_bounds htri k
  have hchangeJ := triangular_neighbours_coordinate_bounds htri j
  by_cases heven : r % 2 = 0
  · have hr : r = 2 * (r / 2) := by omega
    rw [hr] at hsame hchangeK hchangeJ
    obtain ⟨hpA, hk, hj, ha, hb⟩ := octEdgeZigzag_even hm1 F (r / 2)
    have hqA : InASublattice q.val := by
      rcases hsame with h | h
      · exact h.2
      · exact (sublattices_disjoint _ hpA h.1).elim
    rcases hq with hq | hq
    · have hforeignK := hq.1.2.2
      have hforeignJ := hq.2
      constructor
      · rcases F.index_cases k with h | h | h | h
        · exact h
        all_goals rw [h] at hforeignK hchangeK
        all_goals dsimp [octRadius] at hforeignK hchangeK hk hj ha hb
        all_goals omega
      · rcases F.index_cases j with h | h | h | h
        · rw [h] at hforeignJ hchangeJ
          dsimp [octRadius] at hforeignJ hchangeJ hk
          omega
        · exact h
        · rw [h] at hforeignJ hchangeJ
          dsimp [octRadius] at hforeignJ hchangeJ ha
          omega
        · rw [h] at hforeignJ hchangeJ
          dsimp [octRadius] at hforeignJ hchangeJ hb
          omega
    · exact (sublattices_disjoint _ hqA hq.1.2.1).elim
  · have hr : r = 2 * (r / 2) + 1 := by omega
    rw [hr] at hsame hchangeK hchangeJ
    obtain ⟨hpB, hk, hj, ha, hb⟩ := octEdgeZigzag_odd hm1 F (r / 2)
    have hqB : InBSublattice q.val := by
      rcases hsame with h | h
      · exact (sublattices_disjoint _ h.1 hpB).elim
      · exact h.2
    rcases hq with hq | hq
    · exact (sublattices_disjoint _ hq.1.2.1 hqB).elim
    · have hforeignK := hq.2
      have hforeignJ := hq.1.2.2
      constructor
      · rcases F.index_cases k with h | h | h | h
        · exact h
        all_goals rw [h] at hforeignK hchangeK
        all_goals dsimp [octRadius] at hforeignK hchangeK hk hj ha hb
        all_goals omega
      · rcases F.index_cases j with h | h | h | h
        · rw [h] at hforeignJ hchangeJ
          dsimp [octRadius] at hforeignJ hchangeJ hk
          omega
        · exact h
        · rw [h] at hforeignJ hchangeJ
          dsimp [octRadius] at hforeignJ hchangeJ ha
          omega
        · rw [h] at hforeignJ hchangeJ
          dsimp [octRadius] at hforeignJ hchangeJ hb
          omega

theorem same_edge_triangular_indices (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame)
    (r s : ℕ) (hr : r < 2 * m - 1) (hs : s < 2 * m - 1)
    (htri : OctTriangularNeighbours m (octEdgeZigzag m F r) (octEdgeZigzag m F s)) :
    r + 2 = s ∨ s + 2 = r := by
  have hrmod := Nat.mod_lt r (by decide : 0 < 2)
  have hsmod := Nat.mod_lt s (by decide : 0 < 2)
  have hrdiv := Nat.mod_add_div r 2
  have hsdiv := Nat.mod_add_div s 2
  have hsame := triangular_neighbours_same_sublattice htri
  by_cases hre : r % 2 = 0 <;> by_cases hse : s % 2 = 0
  · have hr' : r = 2 * (r / 2) := by omega
    have hs' : s = 2 * (s / 2) := by omega
    rw [hr', hs'] at htri
    have h := (big_face_same_side_neighbours hm F (by omega : r / 2 < m) (by omega : s / 2 < m)).mp htri
    omega
  · have hr' : r = 2 * (r / 2) := by omega
    have hs' : s = 2 * (s / 2) + 1 := by omega
    rw [hr', hs'] at hsame
    rcases hsame with h | h
    · exact (sublattices_disjoint _ h.2 (octEdgeZigzag_odd hm F (s / 2)).1).elim
    · exact (sublattices_disjoint _ (octEdgeZigzag_even hm F (r / 2)).1 h.1).elim
  · have hr' : r = 2 * (r / 2) + 1 := by omega
    have hs' : s = 2 * (s / 2) := by omega
    rw [hr', hs'] at hsame
    rcases hsame with h | h
    · exact (sublattices_disjoint _ h.1 (octEdgeZigzag_odd hm F (r / 2)).1).elim
    · exact (sublattices_disjoint _ (octEdgeZigzag_even hm F (s / 2)).1 h.2).elim
  · have hr' : r = 2 * (r / 2) + 1 := by omega
    have hs' : s = 2 * (s / 2) + 1 := by omega
    rw [hr', hs'] at htri
    have h := (small_face_same_side_neighbours hm F (by omega : r / 2 < m - 1)
      (by omega : s / 2 < m - 1)).mp htri
    omega

theorem far_edge_triangular_neighbour_index (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (r : ℕ) (hrlo : 4 ≤ r) (hrhi : r + 4 ≤ 2 * m - 2) (q : Site)
    (htri : OctTriangularNeighbours m (octEdgeZigzag m F r) q)
    (hq : bulkOnDeletedEdge m q) :
    ∃ s < 2 * m - 1, q = octEdgeZigzag m F s ∧ (r + 2 = s ∨ s + 2 = r) := by
  obtain ⟨k, j, _, hedge⟩ := hq
  have hid := far_edge_triangular_neighbour_faces m hm F r hrlo hrhi q htri hedge
  rw [hid.1, hid.2] at hedge
  obtain ⟨s, hs, heq⟩ := (octEdgeSite_iff_param (by omega : 1 ≤ m) F q).mp hedge
  refine ⟨s, hs, heq, ?_⟩
  rw [heq] at htri
  exact same_edge_triangular_indices m (by omega) F r s (by omega) hs htri

end ProteinFolding.Tetrahedral

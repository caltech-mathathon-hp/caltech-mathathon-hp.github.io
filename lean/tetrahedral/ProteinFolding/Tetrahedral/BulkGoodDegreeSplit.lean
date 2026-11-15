import ProteinFolding.Tetrahedral.BulkDamagedParametrization
import ProteinFolding.Tetrahedral.BulkFarDamagedDegree
import ProteinFolding.Tetrahedral.BulkNearDamagedDegreeSplit
import ProteinFolding.Tetrahedral.BulkPatchMinimum

/-! Uniform local cover invariants for every required construction size. -/

namespace ProteinFolding.Tetrahedral

theorem bulkDamaged_degree_split (m : ℕ) (hm : 27 ≤ m) (p : Site) (hd : p ∈ bulkDamaged m) :
    (bulkCoverNeighbours m p).card = 2 := by
  have hOne : 1 ≤ m := by omega
  obtain ⟨F, t, d, heven | hodd⟩ := bulkDamaged_candidate_exists hOne p hd
  · obtain ⟨htValid, rfl⟩ := heven
    by_cases hfar : 10 ≤ t ∧ t + 11 ≤ m
    · exact bulkFarEdge_damaged_degree m F t false d hOne hfar.1 hfar.2 hd
    · by_cases hnear : t ≤ 9
      · exact bulkNearEdge_damaged_degree_split m F t false d hm hnear hOne hd
      · have hreverse : m - 1 - t ≤ 9 := by omega
        have heq := bulkEdgeCandidate_reverse_even hOne F t htValid d
        rw [heq] at hd ⊢
        exact bulkNearEdge_damaged_degree_split m (bulkReverseEdgeFrame F) (m - 1 - t) false d hm hreverse hOne hd
  · obtain ⟨htValid, rfl⟩ := hodd
    by_cases hfar : 10 ≤ t ∧ t + 11 ≤ m
    · exact bulkFarEdge_damaged_degree m F t true d hOne hfar.1 hfar.2 hd
    · by_cases hnear : t ≤ 9
      · exact bulkNearEdge_damaged_degree_split m F t true d hm hnear hOne hd
      · have hreverse : m - 2 - t ≤ 9 := by omega
        have heq := bulkEdgeCandidate_reverse_odd hOne F t htValid d
        rw [heq] at hd ⊢
        exact bulkNearEdge_damaged_degree_split m (bulkReverseEdgeFrame F) (m - 2 - t) true d hm hreverse hOne hd

theorem bulkCover_minimum_degree_split (m : ℕ) (hm : 27 ≤ m) (p : Site) (hp : p ∈ bulkInterior m) :
    1 ≤ (bulkCoverNeighbours m p).card := by
  by_cases hd : p ∈ bulkDamaged m
  · have heq := bulkDamaged_degree_split m hm p hd
    omega
  · exact (bulkCover_good_degree_of_nondamaged m (by omega) p hp hd).1

theorem bulkCover_nonsurface_degree_split (m : ℕ) (hm : 27 ≤ m) (p : Site)
    (hp : p ∈ bulkInterior m) (hn : ¬OctSurfaceSite m p) : (bulkCoverNeighbours m p).card = 2 := by
  by_cases hd : p ∈ bulkDamaged m
  · exact bulkDamaged_degree_split m hm p hd
  · exact bulkCover_nondamaged_nonsurface_degree_all m (by omega) p hp hn hd

theorem bulkCover_degree_one_surface_split (m : ℕ) (hm : 27 ≤ m) (p : Site)
    (hp : p ∈ bulkInterior m) (hdegree : (bulkCoverNeighbours m p).card = 1) : OctSurfaceSite m p := by
  by_contra hn
  have heq := bulkCover_nonsurface_degree_split m hm p hp hn
  omega

theorem bulkCover_no_leaf_pair_split (m : ℕ) (hm : 27 ≤ m) {p q : Site}
    (h : (bulkCoverGraph m).Adj p q)
    (hp : (bulkCoverNeighbours m p).card = 1) (hq : (bulkCoverNeighbours m q).card = 1) : False :=
  bulkCover_no_surface_bond m h
    (bulkCover_degree_one_surface_split m hm p h.1 hp)
    (bulkCover_degree_one_surface_split m hm q h.2.1 hq)

end ProteinFolding.Tetrahedral

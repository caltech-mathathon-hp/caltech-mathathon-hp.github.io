import ProteinFolding.Tetrahedral.BulkCoverConstruction

/-! The simultaneous construction reads only finite local claim sets. -/

namespace ProteinFolding.Tetrahedral

theorem bulkClaimants_eq_neighbour_filter (m : ℕ) (w : Site) :
    bulkClaimants m w = (neighbours w).filter
      (fun d => d ∈ bulkDamaged m ∧ bulkPotentialTarget m d w) := by
  ext d
  simp only [bulkClaimants, Finset.mem_filter, mem_neighbours]
  constructor
  · rintro ⟨hd, ht⟩
    exact ⟨ht.2.1.1.symm, hd, ht⟩
  · rintro ⟨_, hd, ht⟩
    exact ⟨hd, ht⟩

theorem bulkClaimants_card_le_four (m : ℕ) (w : Site) : (bulkClaimants m w).card ≤ 4 := by
  rw [bulkClaimants_eq_neighbour_filter]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by rw [card_neighbours])

theorem bulkDamaged_has_deleted_neighbour (m : ℕ) {d : Site} (hd : d ∈ bulkDamaged m) :
    ∃ e ∈ bulkDeletedEdges m, tetrahedralLattice.Adj d e := by
  obtain ⟨e, he⟩ := (Finset.mem_filter.mp hd).2
  have h := Finset.mem_inter.mp he
  exact ⟨e, h.2, ((bulkRungGraph_adj_iff m d e).mpr h.1).1⟩

def BulkWithinTwoDeleted (m : ℕ) (p : Site) : Prop :=
  ∃ e ∈ bulkDeletedEdges m, tetrahedralLattice.Adj p e ∨
    ∃ d : Site, tetrahedralLattice.Adj p d ∧ tetrahedralLattice.Adj d e

theorem bulkMerge_near_deleted (m : ℕ) {d w : Site} (h : bulkMerge m d w) :
    BulkWithinTwoDeleted m d ∧ BulkWithinTwoDeleted m w := by
  obtain ⟨e, he, hde⟩ := bulkDamaged_has_deleted_neighbour m h.1
  exact ⟨⟨e, he, Or.inl hde⟩, ⟨e, he, Or.inr ⟨d, (bulkMerge_adj m h).symm, hde⟩⟩⟩

/-- Every non-foliation joint is a frozen patch bond, or has both endpoints
within two lattice bonds of a deleted edge. -/
theorem bulkCover_joint_locality (m : ℕ) {p q : Site} (h : (bulkCoverGraph m).Adj p q)
    (hnot : ¬(bulkRungGraph m).Adj p q) :
    bulkPatchAdded m p q ∨ (BulkWithinTwoDeleted m p ∧ BulkWithinTwoDeleted m q) := by
  rcases h.2.2 with hpatch | ⟨hmerged, _⟩
  · exact Or.inl hpatch
  · right
    rcases hmerged with h | h | h
    · exact (hnot h).elim
    · exact bulkMerge_near_deleted m h
    · exact (bulkMerge_near_deleted m h).symm

theorem bulkMergedBond_far_iff_rung (m : ℕ) {p q : Site}
    (hfar : ¬BulkWithinTwoDeleted m p) :
    bulkMergedBond m p q ↔ (bulkRungGraph m).Adj p q := by
  constructor
  · intro h
    rcases h with h | h | h
    · exact h
    · exact (hfar (bulkMerge_near_deleted m h).1).elim
    · exact (hfar (bulkMerge_near_deleted m h).2).elim
  · exact Or.inl

end ProteinFolding.Tetrahedral

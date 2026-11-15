import ProteinFolding.Tetrahedral.BulkPatchReferenceDegree

/-! The actual canonical cover has maximum degree two at every size m>=15. -/

namespace ProteinFolding.Tetrahedral

theorem bulkPatch_degree_le_two (m : ℕ) (hm : 15 ≤ m) (v : Fin 6)
    (r : {r : Coordinates // r ∈ bulkPatchOffsets v}) :
    (bulkCoverNeighbours m (bulkPatchOffsetSite m v r)).card ≤ 2 := by
  have hcard := bulkReanchor_coverNeighbours_card m 15 v 8 (bulkPatchOffsetSite m v r)
    (by omega) (by decide) (bulkPatchOffsetSite_in_box m v r)
  rw [bulkReanchor_patchOffsetSite] at hcard
  have hc := bulkPatch_reference_degree v r
  have hc' : (bulkCoverNeighbours 15 (bulkPatchOffsetSite 15 v r)).card ≤ 2 := by
    rw [bulkCoverNeighbours_fast_card]
    exact hc
  omega

/-- This is an unconditional invariant of the literal merge-and-patch graph,
not a hypothesis on an abstract candidate cover. -/
theorem bulkCoverNeighbours_card_le_two (m : ℕ) (hm : 15 ≤ m) (p : Site) :
    (bulkCoverNeighbours m p).card ≤ 2 := by
  by_cases hp : p ∈ bulkInterior m
  · by_cases hs : p ∈ bulkPatchSupport m
    · obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hs
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
      exact bulkPatch_degree_le_two m hm v r
    · exact bulkCoverNeighbours_card_le_two_of_not_support m p hp hs
  · have hempty : bulkCoverNeighbours m p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact hp (bulkCoverGraph_support m ((mem_bulkCoverNeighbours m p q).mp hq)).1
    rw [hempty]
    decide

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkLocality

/-! Simultaneous rule merges preserve the maximum degree two uniformly in m. -/

namespace ProteinFolding.Tetrahedral

theorem bulkDamaged_not_surface (m : ℕ) {d : Site} (hd : d ∈ bulkDamaged m) :
    ¬OctSurfaceSite m d := by
  intro hsurface
  have hdI := (Finset.mem_filter.mp hd).1
  have hdparts := Finset.mem_sdiff.mp hdI
  obtain ⟨e, he, hde⟩ := bulkDamaged_has_deleted_neighbour m hd
  obtain ⟨k, j, _, heEdge⟩ := (Finset.mem_filter.mp he).2
  have heSurface := octEdgeSite_surface m heEdge
  apply hdparts.2
  apply Finset.mem_filter.mpr
  refine ⟨hdparts.1, ?_⟩
  rcases d.property with hdA | hdB
  · obtain ⟨k, j, hkj, hdEdge, _⟩ := bonded_surface_sites_on_edge m hdA hsurface heSurface hde
    exact ⟨k, j, hkj, Or.inl hdEdge⟩
  · have heA : InASublattice e.val :=
      (adj_not_same_sublattice hde.symm).mpr ((inB_iff_not_inA d).mp hdB)
    obtain ⟨k, j, hkj, _, hdEdge⟩ := bonded_surface_sites_on_edge m heA heSurface hsurface hde.symm
    exact ⟨k, j, hkj, Or.inr hdEdge⟩

theorem bulkMerge_target_surface (m : ℕ) {d w : Site} (h : bulkMerge m d w) :
    OctSurfaceSite m w := by
  have hwI := (bulkMerge_mem m h).2
  exact ⟨(Finset.mem_sdiff.mp hwI).1, h.2.1.2.2.2.2⟩

theorem bulkMerge_not_source_and_target (m : ℕ) {d p w : Site}
    (hin : bulkMerge m d p) (hout : bulkMerge m p w) : False :=
  bulkDamaged_not_surface m hout.1 (bulkMerge_target_surface m hin)

def bulkIncidentMerges (m : ℕ) (p : Site) : Finset Site :=
  (bulkInterior m).filter (fun q => bulkMerge m p q ∨ bulkMerge m q p)

theorem bulkIncidentMerges_card_le_one (m : ℕ) (p : Site) :
    (bulkIncidentMerges m p).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q hq r hr
  have hq' := (Finset.mem_filter.mp hq).2
  have hr' := (Finset.mem_filter.mp hr).2
  rcases hq' with hq' | hq' <;> rcases hr' with hr' | hr'
  · exact bulkMerge_target_unique m hq' hr'
  · exact (bulkMerge_not_source_and_target m hr' hq').elim
  · exact (bulkMerge_not_source_and_target m hq' hr').elim
  · exact bulkMerge_claimant_unique m hq' hr'

theorem bulkIncidentMerges_base_degree (m : ℕ) (p : Site)
    (hne : (bulkIncidentMerges m p).Nonempty) : (bulkBaseNeighbours m p).card ≤ 1 := by
  obtain ⟨q, hq⟩ := hne
  rcases (Finset.mem_filter.mp hq).2 with h | h
  · exact bulk_damaged_base_degree m h.1
  · exact h.2.1.2.2.2.1

def bulkMergedNeighbours (m : ℕ) (p : Site) : Finset Site :=
  bulkBaseNeighbours m p ∪ bulkIncidentMerges m p

theorem bulkMergedNeighbours_card_le_two (m : ℕ) (p : Site) :
    (bulkMergedNeighbours m p).card ≤ 2 := by
  by_cases hne : (bulkIncidentMerges m p).Nonempty
  · have hbase := bulkIncidentMerges_base_degree m p hne
    have hnew := bulkIncidentMerges_card_le_one m p
    have hcard := Finset.card_union_le (bulkBaseNeighbours m p) (bulkIncidentMerges m p)
    change (bulkMergedNeighbours m p).card ≤ _ at hcard
    omega
  · have hempty : bulkIncidentMerges m p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    unfold bulkMergedNeighbours
    rw [hempty, Finset.union_empty]
    have hsub : bulkBaseNeighbours m p ⊆ bulkRungNeighbours m p := Finset.inter_subset_left
    have hcard := Finset.card_le_card hsub
    rwa [bulkRungNeighbours_card] at hcard

theorem mem_bulkMergedNeighbours (m : ℕ) (p q : Site) :
    q ∈ bulkMergedNeighbours m p ↔ q ∈ bulkInterior m ∧ bulkMergedBond m p q := by
  simp only [bulkMergedNeighbours, Finset.mem_union, bulkBaseNeighbours, Finset.mem_inter,
    bulkIncidentMerges, Finset.mem_filter, ← bulkRungGraph_adj_iff, bulkMergedBond]
  constructor
  · rintro (⟨hrung, hq⟩ | ⟨hq, hmerge⟩)
    · exact ⟨hq, Or.inl hrung⟩
    · exact ⟨hq, Or.inr hmerge⟩
  · rintro ⟨hq, hrung | hmerge⟩
    · exact Or.inl ⟨hrung, hq⟩
    · exact Or.inr ⟨hq, hmerge⟩

end ProteinFolding.Tetrahedral

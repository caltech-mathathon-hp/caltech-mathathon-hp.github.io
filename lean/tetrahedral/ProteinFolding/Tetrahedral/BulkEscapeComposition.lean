import ProteinFolding.Tetrahedral.BulkEscapeTypes
import ProteinFolding.Tetrahedral.BulkXPositiveEscape
import ProteinFolding.Tetrahedral.BulkXNegativeEscape
import ProteinFolding.Tetrahedral.BulkLongXEndpointSigns
import ProteinFolding.Tetrahedral.BulkLongXRow
import ProteinFolding.Tetrahedral.BulkGoodDegreeSplit
import ProteinFolding.Tetrahedral.FiniteCycleCriterion

/-! Every actual bulk component escapes from each rung segment to a leaf
or a strictly larger exact potential. The finite canonical graph is acyclic. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkSegment_cover_reachable (m : ℕ) {p q : BulkVertex m}
    (h : (bulkSegmentGraph m).Reachable p q) : (bulkFiniteGraph m).Reachable p q := by
  obtain ⟨w⟩ := h
  let f : bulkSegmentGraph m →g bulkFiniteGraph m := ⟨id, by intro a b h; exact h.1⟩
  exact ⟨w.map f⟩

theorem bulkEscapes_of_segment_reachable (m : ℕ) {p q : BulkVertex m}
    (h : (bulkSegmentGraph m).Reachable p q) (hq : BulkEscapes m q) : BulkEscapes m p := by
  obtain ⟨r, hqr, hcase⟩ := hq
  refine ⟨r, (bulkSegment_cover_reachable m h).trans hqr, ?_⟩
  rcases hcase with hleaf | hgt
  · exact Or.inl hleaf
  · right
    rwa [bulkSegmentPotential_eq m h]

theorem bulkX_two_ends_escape (m : ℕ) (hm : 50 ≤ m) {p q r s : BulkVertex m}
    (w : (bulkSegmentGraph m).Walk p q) (hw : w.IsPath)
    (hspan : ∀ v, (bulkSegmentGraph m).Reachable p v → v ∈ w.support)
    (hp : BulkXJointData m p r) (hq : BulkXJointData m q s) : BulkEscapes m p := by
  have hpin := bulkHasInwardNeighbour_finite m p hp.inward
  have hqin := bulkHasInwardNeighbour_finite m q hq.inward
  have hline : (bulkSegmentGraph m).Reachable p q := ⟨w⟩
  obtain ⟨b, hpb, hbend, hhat⟩ := bulkSegment_inward_spanning_bend_xhat m w hw hspan hpin hqin
  have hBend := bulk_bend_unique_of_reachable m (bulkBendPoint_is_bend m p.val) hbend
    ((bulkBendPoint_reachable m p.val).symm.trans (bulkSegment_reachable_rung m hpb))
  have hpHat : bulkSegmentXhat m p = 2 * (bulkBendPoint m p.val).val 0 := by rw [hBend]; exact hhat
  rcases bulkAlpha_signed m p.val with hα | hα
  · have hop := bulkYSign_opposite_of_coordinates m p.val q.val
      (bulkSegment_inward_negative_endpoint_signs m w hw hspan hpin hqin hα)
    exact bulkXNegative_escape_at_one_end m p q r s hline hα hop hp.negative hq.negative
      hp.axes.2 hq.axes.2 hp.adj hq.adj hp.merge hq.merge hp.signs hq.signs hpHat
      (bulkNegative_neighbour_shape m hm p r hp.x_bound hp.alpha_bound hp.adj)
      (bulkNegative_neighbour_shape m hm q s hq.x_bound hq.alpha_bound hq.adj)
  · have hop := bulkZSign_opposite_of_coordinates p.val q.val
      (bulkSegment_inward_positive_endpoint_signs m w hw hspan hpin hqin hα)
    have hnr : ¬BulkRowSegment m p := by
      apply bulkSegment_not_row_of_slab_alpha m p 5
      · intro v hv
        exact bulkSegment_x_bound_of_site m 3 hv hp.x_bound
      · have hbound := abs_le.mp hp.alpha_bound
        omega
    obtain ⟨v, hpv, hgt⟩ := bulkXPositive_escape_at_one_end m p q r s hline hα hnr hop
      hp.positive hq.positive hp.adj hq.adj
    exact ⟨v, hpv, Or.inr hgt⟩

theorem bulkEveryVertex_escapes_of_joint_cases (m : ℕ) (hm : 50 ≤ m)
    (hcases : ∀ p q : BulkVertex m, (bulkFiniteGraph m).Adj p q →
      ¬(bulkRungGraph m).Adj p.val q.val → BulkEscapes m p ∨ BulkXJointData m p q)
    (p : BulkVertex m) : BulkEscapes m p := by
  obtain ⟨a, b, w, hw, hspan, haDeg, hbDeg⟩ := bulkSegment_spanning_path m p
  have hpa := (hspan a).mp w.start_mem_support
  have hpb := (hspan b).mp w.end_mem_support
  by_cases haLeaf : (bulkFiniteGraph m).degree a ≤ 1
  · exact ⟨a, bulkSegment_cover_reachable m hpa, Or.inl haLeaf⟩
  by_cases hbLeaf : (bulkFiniteGraph m).degree b ≤ 1
  · exact ⟨b, bulkSegment_cover_reachable m hpb, Or.inl hbLeaf⟩
  obtain ⟨r, har, hnr⟩ := bulkSegment_endpoint_joint m a (by omega) haDeg
  obtain ⟨s, hbs, hns⟩ := bulkSegment_endpoint_joint m b (by omega) hbDeg
  rcases hcases a r har hnr with haEscape | haX
  · exact bulkEscapes_of_segment_reachable m hpa haEscape
  rcases hcases b s hbs hns with hbEscape | hbX
  · exact bulkEscapes_of_segment_reachable m hpb hbEscape
  have hspanA : ∀ v, (bulkSegmentGraph m).Reachable a v → v ∈ w.support :=
    fun v hav => (hspan v).mpr (hpa.trans hav)
  exact bulkEscapes_of_segment_reachable m hpa (bulkX_two_ends_escape m hm w hw hspanA haX hbX)

theorem bulkFiniteGraph_acyclic_of_joint_cases (m : ℕ) (hm : 50 ≤ m)
    (hcases : ∀ p q : BulkVertex m, (bulkFiniteGraph m).Adj p q →
      ¬(bulkRungGraph m).Adj p.val q.val → BulkEscapes m p ∨ BulkXJointData m p q) :
    (bulkFiniteGraph m).IsAcyclic := by
  have hdegree : ∀ p : BulkVertex m, (bulkFiniteGraph m).degree p ≤ 2 := by
    intro p
    rw [bulkFinite_degree]
    exact bulkCoverNeighbours_card_le_two m (by omega) p.val
  exact finite_degree_two_acyclic_of_escape (bulkFiniteGraph m) hdegree (bulkSegmentPotential m)
    (bulkEveryVertex_escapes_of_joint_cases m hm hcases)

end ProteinFolding.Tetrahedral

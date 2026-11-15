import ProteinFolding.Tetrahedral.BulkNegativeJointGeometry
import ProteinFolding.Tetrahedral.BulkXInwardNearUniform
import ProteinFolding.Tetrahedral.BulkLongXInwardPath
import ProteinFolding.Tetrahedral.BulkSegmentEnds
import ProteinFolding.Tetrahedral.BulkDamagedParametrization

/-! A moderately negative-alpha component in the X slab either reaches
a true cover leaf or has the full bend Xhat. This covers neighbouring
components without assuming that their second joint is far. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkNegative_moderate_not_patch (m : ℕ) (hm : 50 ≤ m) (p : Site)
    (hx : |p.val 0| ≤ 6) (hα : bulkAlpha m p < 0) (hbound : |bulkAlpha m p| ≤ octRadius m - 35) :
    p ∉ bulkPatchSupport m := by
  intro hp
  obtain ⟨v, _, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
  exact bulkNegative_moderate_not_vertex_box m hm _ hx hα hbound v
    (bulkVertexBox_mono m v (by decide : 8 ≤ 9) (bulkPatchOffsetSite_in_box m v r))

theorem bulkNegative_candidate_joint_inward (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m)
    (hvalid : match odd with | false => t < m | true => t + 2 ≤ m)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) (p : Site)
    (hp : p = bulkEdgeCandidate m F t odd d hOne ∨ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) p)
    (hx : |p.val 0| ≤ 6) (hα : bulkAlpha m p < 0) (hbound : |bulkAlpha m p| ≤ octRadius m - 35) :
    BulkHasInwardNeighbour m p := by
  have hpAdj : p = bulkEdgeCandidate m F t odd d hOne ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hOne) p :=
    hp.imp id (bulkMerge_adj m)
  have hX := bulkNegative_moderate_joint_frame_X m hm F t odd d hOne p hpAdj hx hα hbound
  have ht := bulkX_joint_moderate_index_lower m hm F t odd d hOne hX hd p hp hbound
  have hXrev : BulkXEdgeFrame (bulkReverseEdgeFrame F) := by
    simpa only [BulkXEdgeFrame, bulkReverseEdgeFrame] using hX
  have hrev : 8 ≤ if odd then m - 2 - t else m - 1 - t := by
    cases odd
    · change t < m at hvalid
      change 8 ≤ m - 1 - t
      have heq := bulkEdgeCandidate_reverse_even hOne F t hvalid d
      rw [heq] at hd hp
      exact bulkX_joint_moderate_index_lower m hm (bulkReverseEdgeFrame F) _ false d hOne hXrev hd p hp hbound
    · change t + 2 ≤ m at hvalid
      change 8 ≤ m - 2 - t
      have heq := bulkEdgeCandidate_reverse_odd hOne F t hvalid d
      rw [heq] at hd hp
      exact bulkX_joint_moderate_index_lower m hm (bulkReverseEdgeFrame F) _ true d hOne hXrev hd p hp hbound
  exact bulkX_joint_inward_outside_seven m hm F t odd d hOne ht hrev hX hd p hp

theorem bulkNegative_merge_endpoint_inward (m : ℕ) (hm : 50 ≤ m) (source target p : Site)
    (hmerge : bulkMerge m source target) (hp : p = source ∨ p = target)
    (hx : |p.val 0| ≤ 6) (hα : bulkAlpha m p < 0) (hbound : |bulkAlpha m p| ≤ octRadius m - 35) :
    BulkHasInwardNeighbour m p := by
  have hOne : 1 ≤ m := by omega
  obtain ⟨F, t, d, heven | hodd⟩ := bulkDamaged_candidate_exists hOne source hmerge.1
  · obtain ⟨hvalid, heq⟩ := heven
    rw [heq] at hmerge hp
    have hend : p = bulkEdgeCandidate m F t false d hOne ∨ bulkMerge m (bulkEdgeCandidate m F t false d hOne) p := by
      rcases hp with hp | rfl
      · exact Or.inl hp
      · exact Or.inr hmerge
    exact bulkNegative_candidate_joint_inward m hm F t false d hOne hvalid hmerge.1 p hend hx hα hbound
  · obtain ⟨hvalid, heq⟩ := hodd
    rw [heq] at hmerge hp
    have hend : p = bulkEdgeCandidate m F t true d hOne ∨ bulkMerge m (bulkEdgeCandidate m F t true d hOne) p := by
      rcases hp with hp | rfl
      · exact Or.inl hp
      · exact Or.inr hmerge
    exact bulkNegative_candidate_joint_inward m hm F t true d hOne hvalid hmerge.1 p hend hx hα hbound

theorem bulkNegative_actual_joint_inward (m : ℕ) (hm : 50 ≤ m) (p q : BulkVertex m)
    (h : (bulkFiniteGraph m).Adj p q) (hnr : ¬(bulkRungGraph m).Adj p.val q.val)
    (hx : |p.val.val 0| ≤ 6) (hα : bulkAlpha m p.val < 0) (hbound : |bulkAlpha m p.val| ≤ octRadius m - 35) :
    ∃ r : BulkVertex m, (bulkSegmentGraph m).Adj p r ∧ bulkRho m r.val < bulkRho m p.val := by
  apply bulkHasInwardNeighbour_finite m p
  rcases bulkCover_nonrung_joint_cases m h hnr with hpatch | hmerge | hmerge
  · exact (bulkNegative_moderate_not_patch m hm p.val hx hα hbound (bulkPatchSupport_added m hpatch).1).elim
  · exact bulkNegative_merge_endpoint_inward m hm p.val q.val p.val hmerge (Or.inl rfl) hx hα hbound
  · exact bulkNegative_merge_endpoint_inward m hm q.val p.val p.val hmerge (Or.inr rfl) hx hα hbound

theorem bulkSegmentXhat_eq_of_reachable (m : ℕ) {p q : BulkVertex m}
    (h : (bulkSegmentGraph m).Reachable p q) : bulkSegmentXhat m p = bulkSegmentXhat m q := by
  unfold bulkSegmentXhat bulkSegmentXValues
  simp only [bulkSegmentSites_eq_of_reachable m h]

theorem bulkNegative_component_leaf_or_bend (m : ℕ) (hm : 50 ≤ m) (p : BulkVertex m)
    (hx : |p.val.val 0| ≤ 4) (hα : bulkAlpha m p.val < 0) (hbound : |bulkAlpha m p.val| ≤ octRadius m - 35) :
    (∃ q : BulkVertex m, (bulkFiniteGraph m).Reachable p q ∧ (bulkFiniteGraph m).degree q ≤ 1) ∨
      bulkSegmentXhat m p = 2 * (bulkBendPoint m p.val).val 0 := by
  obtain ⟨a, b, w, hw, hspan, haDeg, hbDeg⟩ := bulkSegment_spanning_path m p
  have hpa := (hspan a).mp w.start_mem_support
  have hpb := (hspan b).mp w.end_mem_support
  have coverReach {q : BulkVertex m} (hpq : (bulkSegmentGraph m).Reachable p q) :
      (bulkFiniteGraph m).Reachable p q := by
    obtain ⟨v⟩ := hpq
    let f : bulkSegmentGraph m →g bulkFiniteGraph m := ⟨id, by intro r s h; exact h.1⟩
    exact ⟨v.map f⟩
  by_cases haLeaf : (bulkFiniteGraph m).degree a ≤ 1
  · exact Or.inl ⟨a, coverReach hpa, haLeaf⟩
  by_cases hbLeaf : (bulkFiniteGraph m).degree b ≤ 1
  · exact Or.inl ⟨b, coverReach hpb, hbLeaf⟩
  have endpointInward (q : BulkVertex m) (hpq : (bulkSegmentGraph m).Reachable p q)
      (hqDeg : (bulkSegmentGraph m).degree q ≤ 1) (hqNotLeaf : ¬(bulkFiniteGraph m).degree q ≤ 1) :
      ∃ r : BulkVertex m, (bulkSegmentGraph m).Adj q r ∧ bulkRho m r.val < bulkRho m q.val := by
    obtain ⟨r, hqr, hnr⟩ := bulkSegment_endpoint_joint m q (by omega) hqDeg
    have hqα := bulkSegment_alpha m hpq
    exact bulkNegative_actual_joint_inward m hm q r hqr hnr
      (bulkSegment_x_bound_of_site m 4 hpq hx) (by omega) (by rwa [hqα])
  have haIn := endpointInward a hpa haDeg haLeaf
  have hbIn := endpointInward b hpb hbDeg hbLeaf
  have hspanA : ∀ r, (bulkSegmentGraph m).Reachable a r → r ∈ w.support :=
    fun r har => (hspan r).mpr (hpa.trans har)
  obtain ⟨c, hac, hcbend, hXhat⟩ := bulkSegment_inward_spanning_bend_xhat m w hw hspanA haIn hbIn
  have hpc := hpa.trans hac
  have hBend := bulk_bend_unique_of_reachable m (bulkBendPoint_is_bend m p.val) hcbend
    ((bulkBendPoint_reachable m p.val).symm.trans (bulkSegment_reachable_rung m hpc))
  right
  rw [bulkSegmentXhat_eq_of_reachable m hpa, hXhat, hBend]

end ProteinFolding.Tetrahedral

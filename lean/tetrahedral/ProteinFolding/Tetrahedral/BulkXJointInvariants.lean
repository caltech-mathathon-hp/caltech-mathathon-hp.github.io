import ProteinFolding.Tetrahedral.BulkXJointInvariantTransfer

/-! Uniform X-joint invariants for both ends of an actual merge. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkXJoint_uniform_invariants (m : ℕ) (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4)
    (hm : 1 ≤ m) (ht : 10 ≤ t) (htm : t + 11 ≤ m) (hX : BulkXEdgeFrame F) (w : Site)
    (hmerge : bulkMerge m (bulkEdgeCandidate m F t odd d hm) w) :
    BulkXPositiveJointInvariant m (bulkEdgeCandidate m F t odd d hm) w ∧
      BulkXNegativeJointInvariant m (bulkEdgeCandidate m F t odd d hm) ∧
      BulkXPositiveJointInvariant m w (bulkEdgeCandidate m F t odd d hm) ∧
      BulkXNegativeJointInvariant m w := by
  obtain ⟨e, rfl⟩ := (adj_iff_exists_step _ w).mp (bulkMerge_adj m hmerge)
  have hsource := bulkEdgeCandidate_in_box m F t odd d hm
  have htarget := bulk_adjacent_in_edge_box m F t 2 hsource (step_adj _ e)
  have hsource3 := bulkEdgeBox_mono m F t (show 2 ≤ 3 by decide) hsource
  have hM := (bulkEdgeReanchor_merge_iff m 21 t 10 F 3 _ _
    (by omega) (by omega) (by decide) (by decide) hsource3 htarget).mpr hmerge
  rw [bulkEdgeReanchor_step, bulkEdgeReanchor_candidate m 21 t 10 F odd d hm (by decide)] at hM
  have href := bulkXJoint_reference_invariants F odd d e hX ((bulkMerge_fast_iff 21 _ _).mp hM)
  have hc := bulkEdgeReanchor_candidate m 21 t 10 F odd d hm (by decide)
  have hw : bulkEdgeReanchor m 21 t 10 F (step (bulkEdgeCandidate m F t odd d hm) e) =
      step (bulkEdgeCandidate 21 F 10 odd d (by decide)) e := by rw [bulkEdgeReanchor_step, hc]
  have hrefMapped :
      BulkXPositiveJointInvariant 21 (bulkEdgeReanchor m 21 t 10 F (bulkEdgeCandidate m F t odd d hm))
        (bulkEdgeReanchor m 21 t 10 F (step (bulkEdgeCandidate m F t odd d hm) e)) ∧
      BulkXNegativeJointInvariant 21 (bulkEdgeReanchor m 21 t 10 F (bulkEdgeCandidate m F t odd d hm)) ∧
      BulkXPositiveJointInvariant 21 (bulkEdgeReanchor m 21 t 10 F (step (bulkEdgeCandidate m F t odd d hm) e))
        (bulkEdgeReanchor m 21 t 10 F (bulkEdgeCandidate m F t odd d hm)) ∧
      BulkXNegativeJointInvariant 21 (bulkEdgeReanchor m 21 t 10 F (step (bulkEdgeCandidate m F t odd d hm) e)) := by
    simpa only [hc, hw] using href
  have hpIff := bulkXJoint_invariants_edge_iff m 21 t 10 F 3 _ _
    (by omega) (by omega) (by decide) (by decide) hX hsource3 htarget
  have hwIff := bulkXJoint_invariants_edge_iff m 21 t 10 F 3 _ _
    (by omega) (by omega) (by decide) (by decide) hX htarget hsource3
  exact ⟨hpIff.1.mp hrefMapped.1, hpIff.2.mp hrefMapped.2.1,
    hwIff.1.mp hrefMapped.2.2.1, hwIff.2.mp hrefMapped.2.2.2⟩

theorem bulkXPositiveBend_eq_bend (m : ℕ) (p : Site) (hp : 0 < bulkAlpha m p) :
    bulkXPositiveBend m p = (bulkBendPoint m p).val 0 :=
  (bulkBendPoint_x_positive m p hp).symm

theorem bulkXNegativeBend_eq_bend (m : ℕ) (p : Site) (hp : bulkAlpha m p < 0) :
    bulkXNegativeBend m p = (bulkBendPoint m p).val 0 :=
  (bulkBendPoint_x_negative m p hp).symm

end ProteinFolding.Tetrahedral

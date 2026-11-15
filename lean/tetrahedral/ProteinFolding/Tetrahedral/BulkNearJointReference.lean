import ProteinFolding.Tetrahedral.BulkNearJointCheck0
import ProteinFolding.Tetrahedral.BulkNearJointCheck1
import ProteinFolding.Tetrahedral.BulkNearJointCheck2
import ProteinFolding.Tetrahedral.BulkNearJointCheck3

/-! Every actual non-rung cover neighbour of a near damaged candidate belongs
to a listed core component, including the merge-target case. -/

namespace ProteinFolding.Tetrahedral

theorem bulkNearJoint_reference (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d e : Fin 4)
    (hd : bulkFastDamaged 50 (bulkEdgeCandidate 50 F t.val odd d (by decide)))
    (hrho : bulkRho 50 (bulkEdgeCandidate 50 F t.val odd d (by decide)) =
      bulkRho 50 (step (bulkEdgeCandidate 50 F t.val odd d (by decide)) e))
    (hbond : bulkFastCoverBond 50 (bulkEdgeCandidate 50 F t.val odd d (by decide))
      (step (bulkEdgeCandidate 50 F t.val odd d (by decide)) e)) :
    step (bulkEdgeCandidate 50 F t.val odd d (by decide)) e ∈
        bulkNearSegmentSupport (bulkNearSegmentJointIndex F t odd d e) ∧
      bulkNearSegmentVertex (bulkNearSegmentJointIndex F t odd d e) = bulkEdgeStartIndex F ∧
      bulkNearSegmentCore (bulkNearSegmentJointIndex F t odd d e) = true := by
  have hcheck : BulkNearJointPositionCheck F t odd d e := by
    have h : ∀ k : Fin 4, F.k = k → BulkNearJointPositionCheck F t odd d e := by
      intro k
      fin_cases k
      · intro hk; exact bulkNearJoint_position_reference_0 F hk t odd d e
      · intro hk; exact bulkNearJoint_position_reference_1 F hk t odd d e
      · intro hk; exact bulkNearJoint_position_reference_2 F hk t odd d e
      · intro hk; exact bulkNearJoint_position_reference_3 F hk t odd d e
    exact h _ rfl
  obtain ⟨hmatch, hv, hc⟩ := hcheck hd hrho hbond
  refine ⟨?_, hv, hc⟩
  exact List.mem_toFinset.mpr (bulkSiteListPositionMatch_mem _ _ _ hmatch)

end ProteinFolding.Tetrahedral

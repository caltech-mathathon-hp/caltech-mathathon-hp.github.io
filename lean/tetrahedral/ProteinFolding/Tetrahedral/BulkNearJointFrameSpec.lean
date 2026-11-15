import ProteinFolding.Tetrahedral.BulkNearJointPositionSpec

/-! Check the damaged-candidate guard once before the four possible joint
directions. This is logically the same actual coordinate certificate. -/

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 2000000

def BulkNearJointRowCheck (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d : Fin 4) : Prop :=
  bulkFastDamaged 50 (bulkEdgeCandidate 50 F t.val odd d (by decide)) →
    ∀ e : Fin 4,
      bulkRho 50 (bulkEdgeCandidate 50 F t.val odd d (by decide)) =
        bulkRho 50 (step (bulkEdgeCandidate 50 F t.val odd d (by decide)) e) →
      bulkFastCoverBond 50 (bulkEdgeCandidate 50 F t.val odd d (by decide))
        (step (bulkEdgeCandidate 50 F t.val odd d (by decide)) e) →
      bulkSiteListPositionMatch (bulkNearSegmentPoints (bulkNearSegmentJointIndex F t odd d e))
          (bulkNearJointPosition F t odd d e) (step (bulkEdgeCandidate 50 F t.val odd d (by decide)) e) = true ∧
        bulkNearSegmentVertex (bulkNearSegmentJointIndex F t odd d e) = bulkEdgeStartIndex F ∧
        bulkNearSegmentCore (bulkNearSegmentJointIndex F t odd d e) = true

instance (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d : Fin 4) :
    Decidable (BulkNearJointRowCheck F t odd d) := by
  unfold BulkNearJointRowCheck
  infer_instance

theorem bulkNearJointRowCheck_sound (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d : Fin 4)
    (h : BulkNearJointRowCheck F t odd d) (e : Fin 4) : BulkNearJointPositionCheck F t odd d e := by
  intro hd hrho hbond
  exact h hd e hrho hbond

end ProteinFolding.Tetrahedral

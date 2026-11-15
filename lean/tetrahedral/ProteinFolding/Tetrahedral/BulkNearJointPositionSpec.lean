import ProteinFolding.Tetrahedral.BulkNearJointPositions
import ProteinFolding.Tetrahedral.BulkNearCandidatePositionSpec

/-! Direct-coordinate certificates for the actual targets of near joints.
The public statement still asserts membership in the complete component. -/

namespace ProteinFolding.Tetrahedral

def BulkNearJointPositionCheck (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d e : Fin 4) : Prop :=
  bulkFastDamaged 50 (bulkEdgeCandidate 50 F t.val odd d (by decide)) →
    bulkRho 50 (bulkEdgeCandidate 50 F t.val odd d (by decide)) =
      bulkRho 50 (step (bulkEdgeCandidate 50 F t.val odd d (by decide)) e) →
    bulkFastCoverBond 50 (bulkEdgeCandidate 50 F t.val odd d (by decide))
      (step (bulkEdgeCandidate 50 F t.val odd d (by decide)) e) →
    bulkSiteListPositionMatch (bulkNearSegmentPoints (bulkNearSegmentJointIndex F t odd d e))
        (bulkNearJointPosition F t odd d e) (step (bulkEdgeCandidate 50 F t.val odd d (by decide)) e) = true ∧
      bulkNearSegmentVertex (bulkNearSegmentJointIndex F t odd d e) = bulkEdgeStartIndex F ∧
      bulkNearSegmentCore (bulkNearSegmentJointIndex F t odd d e) = true

instance (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d e : Fin 4) :
    Decidable (BulkNearJointPositionCheck F t odd d e) := by
  unfold BulkNearJointPositionCheck
  infer_instance

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkNearCandidatePositionSpec

namespace ProteinFolding.Tetrahedral

local instance bulkNearCandidate3FrameFintype : Fintype OctEdgeFrame := bulkNearReferenceFrameFintype

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem bulkNearCandidate_position_reference_3 (F : OctEdgeFrame) (hk : F.k = 3) :
    ∀ (t : Fin 10) (odd : Bool) (d : Fin 4), BulkNearCandidatePositionCheck F t odd d := by
  revert F
  decide +kernel

theorem bulkNearCandidate_reference_3 (F : OctEdgeFrame) (hk : F.k = 3) :
    ∀ (t : Fin 10) (odd : Bool) (d : Fin 4), BulkNearCandidateReferenceCheck F t odd d := by
  intro t odd d
  exact bulkNearCandidatePositionCheck_sound F t odd d
    (bulkNearCandidate_position_reference_3 F hk t odd d)

end ProteinFolding.Tetrahedral

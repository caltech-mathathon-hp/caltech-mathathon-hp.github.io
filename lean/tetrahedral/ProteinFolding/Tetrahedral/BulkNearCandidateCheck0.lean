import ProteinFolding.Tetrahedral.BulkNearReferenceSpec

namespace ProteinFolding.Tetrahedral

local instance bulkNearCandidate0FrameFintype : Fintype OctEdgeFrame := bulkNearReferenceFrameFintype

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem bulkNearCandidate_reference_0 (F : OctEdgeFrame) (hk : F.k = 0) :
    ∀ (t : Fin 10) (odd : Bool) (d : Fin 4), BulkNearCandidateReferenceCheck F t odd d := by
  revert F
  decide

end ProteinFolding.Tetrahedral

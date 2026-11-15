import ProteinFolding.Tetrahedral.BulkFarEdgeReference

/-! Fixed near-edge anchor 7; split from the single all-anchor certificate. -/

namespace ProteinFolding.Tetrahedral

local instance bulkNearEdgeFrameFintype7 : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bulkNearEdge_reference_damaged_degree_7 (F : OctEdgeFrame) (odd : Bool) (d : Fin 4) :
    bulkFastDamaged 50 (bulkEdgeCandidate 50 F 7 odd d (by decide)) →
      2 ≤ (bulkFastCoverDirections 50 (bulkEdgeCandidate 50 F 7 odd d (by decide))).card := by
  revert F odd d
  decide

end ProteinFolding.Tetrahedral


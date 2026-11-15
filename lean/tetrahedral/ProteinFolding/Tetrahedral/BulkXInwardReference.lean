import ProteinFolding.Tetrahedral.BulkInwardNeighbour
import ProteinFolding.Tetrahedral.BulkJointPlanes

/-! Finite local inward-neighbour certificates for X-joint sources,
targets, and the one target transition index10. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

local instance bulkXInwardReferenceFrameFintype : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

theorem bulkXInward_reference_source (F : OctEdgeFrame) (odd : Bool) (d : Fin 4) :
    BulkXEdgeFrame F → bulkFastDamaged 21 (bulkEdgeCandidate 21 F 10 odd d (by decide)) →
      BulkFastHasInwardNeighbour 21 (bulkEdgeCandidate 21 F 10 odd d (by decide)) := by
  revert F odd d
  decide

theorem bulkXInward_reference_target (F : OctEdgeFrame) (odd : Bool) (d e : Fin 4) :
    BulkXEdgeFrame F → bulkFastMerge 23 (bulkEdgeCandidate 23 F 11 odd d (by decide))
      (step (bulkEdgeCandidate 23 F 11 odd d (by decide)) e) →
      BulkFastHasInwardNeighbour 23 (step (bulkEdgeCandidate 23 F 11 odd d (by decide)) e) := by
  revert F odd d e
  decide

theorem bulkXInward_reference_target_ten (F : OctEdgeFrame) (odd : Bool) (d e : Fin 4) :
    BulkXEdgeFrame F → bulkFastMerge 50 (bulkEdgeCandidate 50 F 10 odd d (by decide))
      (step (bulkEdgeCandidate 50 F 10 odd d (by decide)) e) →
      BulkFastHasInwardNeighbour 50 (step (bulkEdgeCandidate 50 F 10 odd d (by decide)) e) := by
  revert F odd d e
  decide

end ProteinFolding.Tetrahedral

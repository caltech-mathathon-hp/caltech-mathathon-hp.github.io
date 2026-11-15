import ProteinFolding.Tetrahedral.BulkXInwardUniform
import ProteinFolding.Tetrahedral.BulkSegmentCoordinateTransfer

/-! The two additional inward indices8,9 and the alpha bound excluding
indices0..7 from moderately negative neighbouring segments. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

local instance bulkXInwardNearReferenceFrameFintype : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

theorem bulkXInward_near_reference_source (F : OctEdgeFrame) (j : Fin 2) (odd : Bool) (d : Fin 4) :
    BulkXEdgeFrame F → bulkFastDamaged 50 (bulkEdgeCandidate 50 F (j.val + 8) odd d (by decide)) →
      BulkFastHasInwardNeighbour 50 (bulkEdgeCandidate 50 F (j.val + 8) odd d (by decide)) := by
  revert F j odd d
  decide

theorem bulkXInward_near_reference_target (F : OctEdgeFrame) (j : Fin 2) (odd : Bool) (d e : Fin 4) :
    BulkXEdgeFrame F → bulkFastMerge 50 (bulkEdgeCandidate 50 F (j.val + 8) odd d (by decide))
      (step (bulkEdgeCandidate 50 F (j.val + 8) odd d (by decide)) e) →
      BulkFastHasInwardNeighbour 50 (step (bulkEdgeCandidate 50 F (j.val + 8) odd d (by decide)) e) := by
  revert F j odd d e
  decide

theorem bulkXNear_reference_alpha_lower (F : OctEdgeFrame) (j : Fin 8) (odd : Bool) (d : Fin 4) :
    BulkXEdgeFrame F → bulkFastDamaged 50 (bulkEdgeCandidate 50 F j.val odd d (by decide)) →
      octRadius 50 - 31 ≤ |bulkAlpha 50 (bulkEdgeCandidate 50 F j.val odd d (by decide))| := by
  revert F j odd d
  decide

theorem bulkXEdgeStart_middle (F : OctEdgeFrame) : BulkXEdgeFrame F →
    1 ≤ (bulkEdgeStartIndex F).val ∧ (bulkEdgeStartIndex F).val ≤ 4 := by
  revert F
  decide

end ProteinFolding.Tetrahedral

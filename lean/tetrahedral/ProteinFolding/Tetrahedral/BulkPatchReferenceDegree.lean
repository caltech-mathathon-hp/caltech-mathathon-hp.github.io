import ProteinFolding.Tetrahedral.BulkPatchSupport

/-! The single reference size used by the unbounded vertex-transfer proof. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem bulkPatch_reference_degree (v : Fin 6) :
    ∀ r : {r : Coordinates // r ∈ bulkPatchOffsets v},
      (bulkFastCoverDirections 15 (bulkPatchOffsetSite 15 v r)).card ≤ 2 := by
  fin_cases v <;> decide

end ProteinFolding.Tetrahedral

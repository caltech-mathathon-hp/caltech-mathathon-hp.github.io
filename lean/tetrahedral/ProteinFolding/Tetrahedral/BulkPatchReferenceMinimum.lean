import ProteinFolding.Tetrahedral.BulkPatchSupport

/-! The finite m15 certificate for minimum degree and legitimate patched ends. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem bulkPatch_reference_minimum (v : Fin 6) :
    ∀ r : {r : Coordinates // r ∈ bulkPatchOffsets v},
      let p := bulkPatchOffsetSite 15 v r
      bulkFastInterior 15 p →
        (if 0 < (bulkFastDanglingDirections 15 p).card then 1 else 2) ≤
          (bulkFastCoverDirections 15 p).card := by
  fin_cases v <;> decide

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.NearFieldBulkARowCoordinates
import ProteinFolding.Tetrahedral.BulkFastLocal

/-! Kernel checks of the actual A-second-row reference points. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem aSecondRow_far_reference_degree : (bulkFastCoverDirections 21 (aSecondRowSite 21 10)).card = 2 := by
  decide

theorem aSecondRow_left_reference_degree (t : Fin 10) :
    bulkFastInterior 50 (aSecondRowSite 50 t.val) →
      (bulkFastCoverDirections 50 (aSecondRowSite 50 t.val)).card = 2 := by
  fin_cases t <;> decide

theorem aSecondRow_right_reference_degree (r : Fin 10) :
    bulkFastInterior 50 (aSecondRowSite 50 (49 - r.val)) →
      (bulkFastCoverDirections 50 (aSecondRowSite 50 (49 - r.val))).card = 2 := by
  fin_cases r <;> decide

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.NearFieldBulkXRows
import ProteinFolding.Tetrahedral.BulkFastLocal

/-! Local reference certificates for X-plane normal 0, with both edge
orientations and both sublattices retained. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem xRow_far_reference_0 (reverse small : Bool) :
    bulkFastInterior 23 (xRowSite 23 (by decide) 0 reverse small 11) →
      (bulkFastCoverDirections 23 (xRowSite 23 (by decide) 0 reverse small 11)).card = 2 := by
  cases reverse <;> cases small <;> decide

theorem xRow_left_reference_0 (reverse small : Bool) (t : Fin 11) :
    bulkFastInterior 50 (xRowSite 50 (by decide) 0 reverse small t.val) →
      (bulkFastCoverDirections 50 (xRowSite 50 (by decide) 0 reverse small t.val)).card = 2 := by
  fin_cases t <;> cases reverse <;> cases small <;> decide

theorem xRow_right_reference_0 (reverse small : Bool) (r : Fin 11) :
    bulkFastInterior 50 (xRowSite 50 (by decide) 0 reverse small (49 - r.val)) →
      (bulkFastCoverDirections 50 (xRowSite 50 (by decide) 0 reverse small (49 - r.val))).card = 2 := by
  fin_cases r <;> cases reverse <;> cases small <;> decide

end ProteinFolding.Tetrahedral.NearField


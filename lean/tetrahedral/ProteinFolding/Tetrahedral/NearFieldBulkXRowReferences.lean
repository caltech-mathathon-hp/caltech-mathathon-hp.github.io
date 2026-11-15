import ProteinFolding.Tetrahedral.NearFieldBulkXRowReference0
import ProteinFolding.Tetrahedral.NearFieldBulkXRowReference1
import ProteinFolding.Tetrahedral.NearFieldBulkXRowReference2
import ProteinFolding.Tetrahedral.NearFieldBulkXRowReference3

/-! All four normal directions and both edge orientations of the reference
second rows. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem xRow_far_reference (k : Fin 4) (reverse small : Bool) :
    bulkFastInterior 23 (xRowSite 23 (by decide) k reverse small 11) →
      (bulkFastCoverDirections 23 (xRowSite 23 (by decide) k reverse small 11)).card = 2 := by
  fin_cases k
  · exact xRow_far_reference_0 reverse small
  · exact xRow_far_reference_1 reverse small
  · exact xRow_far_reference_2 reverse small
  · exact xRow_far_reference_3 reverse small

theorem xRow_left_reference (k : Fin 4) (reverse small : Bool) (t : Fin 11) :
    bulkFastInterior 50 (xRowSite 50 (by decide) k reverse small t.val) →
      (bulkFastCoverDirections 50 (xRowSite 50 (by decide) k reverse small t.val)).card = 2 := by
  fin_cases k
  · exact xRow_left_reference_0 reverse small t
  · exact xRow_left_reference_1 reverse small t
  · exact xRow_left_reference_2 reverse small t
  · exact xRow_left_reference_3 reverse small t

theorem xRow_right_reference (k : Fin 4) (reverse small : Bool) (r : Fin 11) :
    bulkFastInterior 50 (xRowSite 50 (by decide) k reverse small (49 - r.val)) →
      (bulkFastCoverDirections 50 (xRowSite 50 (by decide) k reverse small (49 - r.val))).card = 2 := by
  fin_cases k
  · exact xRow_right_reference_0 reverse small r
  · exact xRow_right_reference_1 reverse small r
  · exact xRow_right_reference_2 reverse small r
  · exact xRow_right_reference_3 reverse small r

end ProteinFolding.Tetrahedral.NearField

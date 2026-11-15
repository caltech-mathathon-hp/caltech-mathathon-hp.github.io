import ProteinFolding.Tetrahedral.BulkBendSigns
import ProteinFolding.Tetrahedral.BulkLineX
import ProteinFolding.Tetrahedral.ColumnsArmFacts

/-! Recovering the X-coordinate of a line's bend from any site on an arm. -/

namespace ProteinFolding.Tetrahedral

theorem bulkBendPoint_x_recovery (m : ℕ) (p : Site) :
    (bulkBendPoint m p).val 0 = p.val 0 -
      (siteCharge p - siteCharge (bulkBendPoint m p)) * (bulkYSign m p * bulkZSign p) := by
  have h := bulkArmPoint_x_charge (bulkYSign m p) (bulkZSign p)
    (bulkYSign_unit m p) (bulkZSign_unit p) (bulkBendPoint m p) (bulkBendDistance m p)
  rw [bulkBendPoint_outward] at h
  omega

theorem bulkBendPoint_x_positive (m : ℕ) (p : Site) (hp : 0 < bulkAlpha m p) :
    (bulkBendPoint m p).val 0 = p.val 0 -
      (siteCharge p - 1) * (bulkYSign m p * bulkZSign p) := by
  rw [bulkBendPoint_x_recovery, siteCharge_B (bulkBendPoint_inB_of_positive m p hp)]

theorem bulkBendPoint_x_negative (m : ℕ) (p : Site) (hp : bulkAlpha m p < 0) :
    (bulkBendPoint m p).val 0 = p.val 0 - siteCharge p * (bulkYSign m p * bulkZSign p) := by
  rw [bulkBendPoint_x_recovery, siteCharge_A (bulkBendPoint_inA_of_negative m p hp), sub_zero]

end ProteinFolding.Tetrahedral

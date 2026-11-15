import ProteinFolding.Tetrahedral.BulkLineCoordinates
import ProteinFolding.Tetrahedral.BulkFoliationParity

/-! The sign of alpha determines the bend plane and its sublattice. -/

namespace ProteinFolding.Tetrahedral

theorem bulkBendPoint_alpha (m : ℕ) (p : Site) : bulkAlpha m (bulkBendPoint m p) = bulkAlpha m p :=
  (bulkInwardPoint_rho_alpha m p (bulkBendDistance m p) (le_refl _)).2

theorem bulkBendPoint_Z_zero_of_positive (m : ℕ) (p : Site) (hp : 0 < bulkAlpha m p) :
    bulkZ (bulkBendPoint m p) = 0 := by
  rcases bulkBendPoint_is_bend m p with hy | hz
  · have ha := bulkBendPoint_alpha m p
    unfold bulkAlpha at ha
    unfold bulkAlpha at hp
    rw [hy, abs_zero] at ha
    have hznonneg := abs_nonneg (bulkZ (bulkBendPoint m p))
    omega
  · exact hz

theorem bulkBendPoint_Y_zero_of_negative (m : ℕ) (p : Site) (hp : bulkAlpha m p < 0) :
    bulkY m (bulkBendPoint m p) = 0 := by
  rcases bulkBendPoint_is_bend m p with hy | hz
  · exact hy
  · have ha := bulkBendPoint_alpha m p
    unfold bulkAlpha at ha
    unfold bulkAlpha at hp
    rw [hz, abs_zero] at ha
    have hynonneg := abs_nonneg (bulkY m (bulkBendPoint m p))
    omega

theorem bulkBendPoint_inB_of_positive (m : ℕ) (p : Site) (hp : 0 < bulkAlpha m p) :
    InBSublattice (bulkBendPoint m p).val :=
  bulkZ_zero_inB _ (bulkBendPoint_Z_zero_of_positive m p hp)

theorem bulkBendPoint_inA_of_negative (m : ℕ) (p : Site) (hp : bulkAlpha m p < 0) :
    InASublattice (bulkBendPoint m p).val :=
  bulkY_zero_inA m _ (bulkBendPoint_Y_zero_of_negative m p hp)

end ProteinFolding.Tetrahedral

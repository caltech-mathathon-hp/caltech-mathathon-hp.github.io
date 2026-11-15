import ProteinFolding.Tetrahedral.BulkFoliation

/-! The bent foliation has odd, nonzero alpha on every lattice site. -/

namespace ProteinFolding.Tetrahedral

theorem bulk_abs_mod_two (x : ℤ) : |x| % 2 = x % 2 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    omega

theorem bulkAlpha_mod_two (m : ℕ) (p : Site) : bulkAlpha m p % 2 = 1 := by
  have hy : |bulkY m p| % 2 = bulkY m p % 2 := bulk_abs_mod_two _
  have hz : |bulkZ p| % 2 = bulkZ p % 2 := bulk_abs_mod_two _
  rcases p.property with hp | hp
  · have hypar := hp.1 1
    have hzpar := hp.1 2
    dsimp [bulkAlpha, bulkY, bulkZ, octRadius] at *
    omega
  · have hypar := hp.1 1
    have hzpar := hp.1 2
    dsimp [bulkAlpha, bulkY, bulkZ, octRadius] at *
    omega

theorem bulkAlpha_ne_zero (m : ℕ) (p : Site) : bulkAlpha m p ≠ 0 := by
  have h := bulkAlpha_mod_two m p
  omega

theorem bulkAlpha_signed (m : ℕ) (p : Site) : bulkAlpha m p < 0 ∨ 0 < bulkAlpha m p := by
  have h := bulkAlpha_ne_zero m p
  omega

theorem bulkY_zero_inA (m : ℕ) (p : Site) (h : bulkY m p = 0) : InASublattice p.val := by
  rcases p.property with hp | hp
  · exact hp
  · have hpar := hp.1 1
    dsimp [bulkY, octRadius] at h
    omega

theorem bulkZ_zero_inB (p : Site) (h : bulkZ p = 0) : InBSublattice p.val := by
  rcases p.property with hp | hp
  · have hpar := hp.1 2
    dsimp [bulkZ] at h
    omega
  · exact hp

end ProteinFolding.Tetrahedral

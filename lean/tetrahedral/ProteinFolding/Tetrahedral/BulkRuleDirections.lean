import ProteinFolding.Tetrahedral.BulkMerges
import ProteinFolding.Tetrahedral.BulkFoliationParity

/-! Signed alpha and X changes of actual rule merges. -/

namespace ProteinFolding.Tetrahedral

theorem bulkRuleNeighbour_alpha_normal (m : ℕ) {p q : Site}
    (h : bulkRuleNeighbour m p q) (hnz : bulkZ p ≠ 0) :
    bulkAlpha m q = bulkAlpha m p + 2 * bulkSign (bulkY m p) * bulkSign (bulkZ p) := by
  rcases h.2 with ⟨hy0, hz0, hdy, hdz⟩ | ⟨hz0, _, _, _⟩
  · have hsy := bulkSign_unit_of_ne (bulkY m p) hy0
    have hsz := bulkSign_unit_of_ne (bulkZ p) hz0
    have hyabs := abs_add_signed_unit (bulkSign (bulkY m p)) (bulkY m p)
      (bulkSign (bulkZ p)) hsy (bulkSign_mul_pos _ hy0) hsz
    have hzabs := abs_add_signed_unit (bulkSign (bulkZ p)) (bulkZ p)
      (-bulkSign (bulkY m p)) hsz (bulkSign_mul_pos _ hz0) (by rcases hsy with h | h <;> omega)
    have hY : bulkY m q = bulkY m p + bulkSign (bulkZ p) := by omega
    have hZ : bulkZ q = bulkZ p + -bulkSign (bulkY m p) := by omega
    unfold bulkAlpha
    rw [hY, hZ, hyabs, hzabs]
    ring
  · exact (hnz hz0).elim

theorem bulkRuleNeighbour_alpha_zero (m : ℕ) {p q : Site}
    (h : bulkRuleNeighbour m p q) (hz : bulkZ p = 0) :
    bulkAlpha m q = bulkAlpha m p - 2 := by
  rcases h.2 with ⟨_, hz0, _, _⟩ | ⟨hz0, hy0, hdy, hdz⟩
  · exact (hz0 hz).elim
  · have hsy := bulkSign_unit_of_ne (bulkY m p) hy0
    have hyabs := abs_add_signed_unit (bulkSign (bulkY m p)) (bulkY m p)
      (-bulkSign (bulkY m p)) hsy (bulkSign_mul_pos _ hy0) (by rcases hsy with h | h <;> omega)
    have hunit : bulkSign (bulkY m p) * bulkSign (bulkY m p) = 1 := by
      rcases hsy with h | h <;> rw [h] <;> norm_num
    have hY : bulkY m q = bulkY m p + -bulkSign (bulkY m p) := by omega
    have hZ : bulkZ q = 1 := by omega
    have hYabs : |bulkY m q| = |bulkY m p| - 1 := by
      rw [hY, hyabs]
      rw [mul_neg, hunit]
      omega
    have hZabs : |bulkZ q| = 1 := by rw [hZ]; norm_num
    unfold bulkAlpha
    rw [hYabs, hZabs, hz, abs_zero]
    omega

theorem bondVector_x_eq_yz (d : Fin 4) : bondVector d 0 = bondVector d 1 * bondVector d 2 := by
  revert d
  decide

theorem adj_x_from_yz {p q : Site} (h : tetrahedralLattice.Adj p q) :
    q.val 0 - p.val 0 = if InASublattice p.val then
      (q.val 1 - p.val 1) * (q.val 2 - p.val 2)
      else -(q.val 1 - p.val 1) * (q.val 2 - p.val 2) := by
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp h
  have hd := bondVector_x_eq_yz d
  by_cases hpA : InASublattice p.val
  · simp only [if_pos hpA]
    rw [step_val_of_A p hpA d]
    convert hd using 1 <;> ring
  · have hpB := (inB_iff_not_inA p).mpr hpA
    simp only [if_neg hpA]
    rw [step_val_of_B p hpB d]
    convert congrArg Neg.neg hd using 1 <;> ring

theorem bulkRuleNeighbour_x_normal (m : ℕ) {p q : Site}
    (h : bulkRuleNeighbour m p q) (hnz : bulkZ p ≠ 0) :
    q.val 0 - p.val 0 = if InASublattice p.val then
      -(bulkSign (bulkY m p) * bulkSign (bulkZ p))
      else bulkSign (bulkY m p) * bulkSign (bulkZ p) := by
  have hstep := adj_x_from_yz h.1
  rcases h.2 with ⟨_, _, hdy, hdz⟩ | ⟨hz0, _, _, _⟩
  · have hY : q.val 1 - p.val 1 = bulkSign (bulkZ p) := by dsimp only [bulkY] at hdy ⊢; omega
    have hZ : q.val 2 - p.val 2 = -bulkSign (bulkY m p) := by dsimp only [bulkZ] at hdz ⊢; omega
    rw [hY, hZ] at hstep
    by_cases hpA : InASublattice p.val
    · simp only [if_pos hpA] at hstep ⊢
      calc
        q.val 0 - p.val 0 = bulkSign (bulkZ p) * -bulkSign (bulkY m p) := hstep
        _ = -(bulkSign (bulkY m p) * bulkSign (bulkZ p)) := by ring
    · simp only [if_neg hpA] at hstep ⊢
      calc
        q.val 0 - p.val 0 = -bulkSign (bulkZ p) * -bulkSign (bulkY m p) := hstep
        _ = bulkSign (bulkY m p) * bulkSign (bulkZ p) := by ring
  · exact (hnz hz0).elim

theorem bulkRuleNeighbour_x_zero (m : ℕ) {p q : Site}
    (h : bulkRuleNeighbour m p q) (hz : bulkZ p = 0) :
    q.val 0 - p.val 0 = bulkSign (bulkY m p) := by
  have hstep := adj_x_from_yz h.1
  have hpB := bulkZ_zero_inB p hz
  rw [if_neg ((inB_iff_not_inA p).mp hpB)] at hstep
  rcases h.2 with ⟨_, hz0, _, _⟩ | ⟨_, _, hdy, hdz⟩
  · exact (hz0 hz).elim
  · have hY : q.val 1 - p.val 1 = -bulkSign (bulkY m p) := by dsimp only [bulkY] at hdy ⊢; omega
    have hZ : q.val 2 - p.val 2 = 1 := by dsimp only [bulkZ] at hdz ⊢; omega
    rw [hY, hZ] at hstep
    simpa only [neg_neg, mul_one] using hstep

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkBendX
import ProteinFolding.Tetrahedral.BulkRuleDirections

/-! At a merge in one quadrant, the exact change of bend-X depends only
on the source sublattice and the quadrant signs. -/

namespace ProteinFolding.Tetrahedral

theorem bulkSign_eq_YSign_of_ne (m : ℕ) (p : Site) (h : bulkY m p ≠ 0) :
    bulkSign (bulkY m p) = bulkYSign m p := by
  unfold bulkSign bulkYSign
  split_ifs <;> omega

theorem bulkSign_eq_ZSign_of_ne (p : Site) (h : bulkZ p ≠ 0) :
    bulkSign (bulkZ p) = bulkZSign p := by
  unfold bulkSign bulkZSign
  split_ifs <;> omega

theorem bulkRuleNeighbour_bendX_negative (m : ℕ) {p q : Site}
    (h : bulkRuleNeighbour m p q) (hnz : bulkZ p ≠ 0)
    (hp : bulkAlpha m p < 0) (hq : bulkAlpha m q < 0)
    (hY : bulkYSign m q = bulkYSign m p) (hZ : bulkZSign q = bulkZSign p) :
    (bulkBendPoint m q).val 0 - (bulkBendPoint m p).val 0 =
      if InASublattice p.val then -2 * (bulkYSign m p * bulkZSign p)
      else 2 * (bulkYSign m p * bulkZSign p) := by
  have hny : bulkY m p ≠ 0 := by
    rcases h.2 with hnormal | hzero
    · exact hnormal.1
    · exact (hnz hzero.1).elim
  have hx := bulkRuleNeighbour_x_normal m h hnz
  rw [bulkSign_eq_YSign_of_ne m p hny, bulkSign_eq_ZSign_of_ne p hnz] at hx
  have hxp := bulkBendPoint_x_negative m p hp
  have hxq := bulkBendPoint_x_negative m q hq
  rw [hY, hZ] at hxq
  rcases adj_sublattices h.1 with ⟨hpA, hqB⟩ | ⟨hpB, hqA⟩
  · rw [if_pos hpA] at hx ⊢
    rw [siteCharge_A hpA] at hxp
    rw [siteCharge_B hqB] at hxq
    simp only [zero_mul, sub_zero, one_mul] at hxp hxq
    omega
  · have hpnot := (inB_iff_not_inA p).mp hpB
    rw [if_neg hpnot] at hx ⊢
    rw [siteCharge_B hpB] at hxp
    rw [siteCharge_A hqA] at hxq
    simp only [zero_mul, sub_zero, one_mul] at hxp hxq
    omega

theorem bulkRuleNeighbour_bendX_positive (m : ℕ) {p q : Site}
    (h : bulkRuleNeighbour m p q) (hnz : bulkZ p ≠ 0)
    (hp : 0 < bulkAlpha m p) (hq : 0 < bulkAlpha m q)
    (hY : bulkYSign m q = bulkYSign m p) (hZ : bulkZSign q = bulkZSign p) :
    (bulkBendPoint m q).val 0 - (bulkBendPoint m p).val 0 =
      if InASublattice p.val then -2 * (bulkYSign m p * bulkZSign p)
      else 2 * (bulkYSign m p * bulkZSign p) := by
  have hny : bulkY m p ≠ 0 := by
    rcases h.2 with hnormal | hzero
    · exact hnormal.1
    · exact (hnz hzero.1).elim
  have hx := bulkRuleNeighbour_x_normal m h hnz
  rw [bulkSign_eq_YSign_of_ne m p hny, bulkSign_eq_ZSign_of_ne p hnz] at hx
  have hxp := bulkBendPoint_x_positive m p hp
  have hxq := bulkBendPoint_x_positive m q hq
  rw [hY, hZ] at hxq
  rcases adj_sublattices h.1 with ⟨hpA, hqB⟩ | ⟨hpB, hqA⟩
  · rw [if_pos hpA] at hx ⊢
    rw [siteCharge_A hpA] at hxp
    rw [siteCharge_B hqB] at hxq
    simp only [zero_sub, sub_self, zero_mul, sub_zero, neg_mul, one_mul] at hxp hxq
    omega
  · have hpnot := (inB_iff_not_inA p).mp hpB
    rw [if_neg hpnot] at hx ⊢
    rw [siteCharge_B hpB] at hxp
    rw [siteCharge_A hqA] at hxq
    simp only [zero_sub, sub_self, zero_mul, sub_zero, neg_mul, one_mul] at hxp hxq
    omega

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkSegmentLocalBounds
import ProteinFolding.Tetrahedral.BulkBendX

/-! The transverse coordinate parametrises a nonzero-alpha rung line
injectively. This bounds short class-Z segments without enumerating paths. -/

namespace ProteinFolding.Tetrahedral

theorem int_eq_of_abs_eq_sign (a b : ℤ) (habs : |a| = |b|)
    (hsign : (if 0 ≤ a then (1 : ℤ) else -1) = if 0 ≤ b then 1 else -1) : a = b := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · rw [abs_of_nonneg ha, abs_of_nonneg hb] at habs
    exact habs
  · simp only [if_pos ha, if_neg hb] at hsign
    omega
  · simp only [if_neg ha, if_pos hb] at hsign
    omega
  · rw [abs_of_neg (by omega : a < 0), abs_of_neg (by omega : b < 0)] at habs
    omega

theorem siteCharge_eq_coordinate_mod (p : Site) (k : Fin 3) :
    siteCharge p = p.val k % 2 := by
  rcases p.property with hp | hp
  · rw [siteCharge_A hp, hp.1 k]
  · rw [siteCharge_B hp, hp.1 k]

theorem bulkYSign_eq_of_rungWalk_positive (m : ℕ) {p q : Site}
    (w : (bulkRungGraph m).Walk p q) (hp : 0 < bulkAlpha m p) :
    bulkYSign m q = bulkYSign m p := by
  induction w with
  | nil => rfl
  | @cons p r q hadj w ih =>
    have hα := (bulkRungGraph_adj_rho_alpha m hadj).2
    have hr : 0 < bulkAlpha m r := by omega
    have hp0 : bulkY m p ≠ 0 := by
      have h := abs_nonneg (bulkZ p)
      unfold bulkAlpha at hp
      intro heq
      rw [heq, abs_zero] at hp
      omega
    have hr0 : bulkY m r ≠ 0 := by
      have h := abs_nonneg (bulkZ r)
      unfold bulkAlpha at hr
      intro heq
      rw [heq, abs_zero] at hr
      omega
    have hd := bulk_adj_deltas m hadj.1
    have hs : bulkYSign m r = bulkYSign m p := by
      unfold bulkYSign
      split_ifs <;> omega
    exact (ih hr).trans hs

theorem bulkZSign_eq_of_rungWalk_negative (m : ℕ) {p q : Site}
    (w : (bulkRungGraph m).Walk p q) (hp : bulkAlpha m p < 0) :
    bulkZSign q = bulkZSign p := by
  induction w with
  | nil => rfl
  | @cons p r q hadj w ih =>
    have hα := (bulkRungGraph_adj_rho_alpha m hadj).2
    have hr : bulkAlpha m r < 0 := by omega
    have hp0 : bulkZ p ≠ 0 := by
      have h := abs_nonneg (bulkY m p)
      unfold bulkAlpha at hp
      intro heq
      rw [heq, abs_zero] at hp
      omega
    have hr0 : bulkZ r ≠ 0 := by
      have h := abs_nonneg (bulkY m r)
      unfold bulkAlpha at hr
      intro heq
      rw [heq, abs_zero] at hr
      omega
    have hd := bulk_adj_deltas m hadj.1
    have hs : bulkZSign r = bulkZSign p := by
      unfold bulkZSign
      split_ifs <;> omega
    exact (ih hr).trans hs

theorem bulkRung_positive_Z_injective (m : ℕ) {p q : Site}
    (h : (bulkRungGraph m).Reachable p q) (hp : 0 < bulkAlpha m p)
    (hz : bulkZ q = bulkZ p) : q = p := by
  obtain ⟨w⟩ := h
  have hα := bulkWalk_alpha m w
  have hys := bulkYSign_eq_of_rungWalk_positive m w hp
  have hYabs : |bulkY m q| = |bulkY m p| := by
    unfold bulkAlpha at hα
    rw [hz] at hα
    omega
  have hy : bulkY m q = bulkY m p := by
    exact int_eq_of_abs_eq_sign _ _ hYabs hys
  have hycoord : q.val 1 = p.val 1 := by dsimp only [bulkY] at hy; omega
  have hzcoord : q.val 2 = p.val 2 := by dsimp only [bulkZ] at hz; omega
  have hzs : bulkZSign q = bulkZSign p := by unfold bulkZSign; rw [hz]
  have hc : siteCharge q = siteCharge p := by
    rw [siteCharge_eq_coordinate_mod q 2, siteCharge_eq_coordinate_mod p 2]
    exact congrArg (fun z : ℤ => z % 2) hzcoord
  have hB := bulkBendPoint_eq_of_rungReachable m (show (bulkRungGraph m).Reachable p q from ⟨w⟩)
  have hxp := bulkBendPoint_x_positive m p hp
  have hxq := bulkBendPoint_x_positive m q (by omega)
  rw [← hB, hc, hys, hzs] at hxq
  have hx : q.val 0 = p.val 0 := by omega
  apply Subtype.ext
  funext k
  fin_cases k
  · exact hx
  · exact hycoord
  · exact hzcoord

theorem bulkRung_negative_Y_injective (m : ℕ) {p q : Site}
    (h : (bulkRungGraph m).Reachable p q) (hp : bulkAlpha m p < 0)
    (hy : bulkY m q = bulkY m p) : q = p := by
  obtain ⟨w⟩ := h
  have hα := bulkWalk_alpha m w
  have hzs := bulkZSign_eq_of_rungWalk_negative m w hp
  have hZabs : |bulkZ q| = |bulkZ p| := by
    unfold bulkAlpha at hα
    rw [hy] at hα
    omega
  have hz : bulkZ q = bulkZ p := by
    exact int_eq_of_abs_eq_sign _ _ hZabs hzs
  have hzcoord : q.val 2 = p.val 2 := by dsimp only [bulkZ] at hz; omega
  have hys : bulkYSign m q = bulkYSign m p := by unfold bulkYSign; rw [hy]
  have hycoord : q.val 1 = p.val 1 := by dsimp only [bulkY] at hy; omega
  have hc : siteCharge q = siteCharge p := by
    rw [siteCharge_eq_coordinate_mod q 1, siteCharge_eq_coordinate_mod p 1, hycoord]
  have hB := bulkBendPoint_eq_of_rungReachable m (show (bulkRungGraph m).Reachable p q from ⟨w⟩)
  have hxp := bulkBendPoint_x_negative m p hp
  have hxq := bulkBendPoint_x_negative m q (by omega)
  rw [← hB, hc, hys, hzs] at hxq
  have hx : q.val 0 = p.val 0 := by omega
  apply Subtype.ext
  funext k
  fin_cases k
  · exact hx
  · exact hycoord
  · exact hzcoord

end ProteinFolding.Tetrahedral

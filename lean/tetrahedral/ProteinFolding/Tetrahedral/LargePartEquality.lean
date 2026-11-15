import ProteinFolding.Tetrahedral.BackwardInduction

/-! The final-part restriction in the equality case of Lemma 5.1. -/

namespace ProteinFolding.Tetrahedral

/-- A final part larger than floor(sqrt(a)) gives strict inequality in the
two-candidate estimate, including the borderline quotient j = sqrt(a). -/
theorem largePart_two_point_strict (a t l : ℕ) (ha : 0 < a)
    (ht : Nat.sqrt a < t) (hta : t ≤ a) (hl : Nat.sqrt a < l) :
    min a (t * l) + Nat.sqrt a * (a / t) +
      largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / t) (a % t) <
      a + Nat.sqrt a * l + (l - nextSquareDistance a) := by
  let s := Nat.sqrt a
  let j := a / t
  let q := a % t
  let u := nextSquareDistance a
  have hs : 0 < s := Nat.sqrt_pos.mpr ha
  have hj : j ≤ s := backward_quotient_le_sqrt a t ht
  have hmin := min_le_left a (t * l)
  have hpen : largePartPenalty s u j q ≤ s + (j + 1 - u) := min_le_right _ _
  change min a (t * l) + s * j + largePartPenalty s u j q < a + s * l + (l - u)
  by_cases hjs : j < s
  · have hprod := Nat.mul_lt_mul_of_pos_left (show j + 1 < l by omega) hs
    rw [Nat.mul_succ] at hprod
    have he : j + 1 - u ≤ l - u := by omega
    omega
  · have hjeq : j = s := by omega
    have hdecomp : a = s * t + q := by
      have h := Nat.div_add_mod' a t
      change j * t + q = a at h
      rw [hjeq] at h
      omega
    have hsquare : a < (s + 1) ^ 2 := by
      simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' a
    have hmul := Nat.mul_le_mul_left s (show s + 1 ≤ t by omega)
    have hq : q ≤ s := by nlinarith only [hdecomp, hsquare, hmul]
    have hstrict : largePartPenalty s u s q < s + (s + 1 - u) := by
      have hfirst : largePartPenalty s u s q ≤ q + (s - u) := min_le_left _ _
      by_cases hqs : q < s
      · omega
      · have hqeq : q = s := by omega
        have hdist := add_nextSquareDistance a
        change a + u = (s + 1) ^ 2 at hdist
        have hu : u = 1 := by nlinarith only [hdecomp, hsquare, hmul, hqeq, hdist]
        rw [hu] at hfirst ⊢
        omega
    have hprod := Nat.mul_le_mul_left s (show s + 1 ≤ l by omega)
    rw [Nat.mul_succ] at hprod
    have he : s + 1 - u ≤ l - u := by omega
    rw [hjeq]
    omega

/-- The final part in an equality case of the large-part inequality is at
most floor(sqrt(a)), once its upper bound has been established. -/
theorem large_part_equality_length (hback : BackwardRootBound)
    (a t l : ℕ) (ha : 0 < a) (ht : Nat.sqrt a < t) (hta : t ≤ a)
    (heq : rootSum (a - t) + (a - t) + min a (t * l) = rootSum (a + l)) :
    l ≤ Nat.sqrt a := by
  by_contra hnot
  have hstrict := largePart_two_point_strict a t l ha ht hta (by omega)
  have hleft := hback a t ha ht hta
  have hright := rootWindow_enhanced_lower a l
  have hmono := rootSum_mono (Nat.le_add_right a l)
  unfold rootWindow at hright
  omega

end ProteinFolding.Tetrahedral

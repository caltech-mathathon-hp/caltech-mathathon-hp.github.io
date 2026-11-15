import ProteinFolding.Tetrahedral.BackwardBase

/-! The initial backward-root estimate at t = floor(sqrt(a)) + 1.
The proof separates the remainder below, at, and above the square root. -/

namespace ProteinFolding.Tetrahedral

set_option maxHeartbeats 2000000 in
theorem backward_initial_parametric (s r : ℕ) (hs : 0 < s) (hr : r ≤ 2 * s)
    (hsize : s + 1 ≤ s ^ 2 + r) :
    rootSum (s ^ 2 + r - (s + 1)) + (s ^ 2 + r - (s + 1)) + (s ^ 2 + r) ≤
      rootSum (s ^ 2 + r) + s * ((s ^ 2 + r) / (s + 1)) +
        largePartPenalty s ((s + 1) ^ 2 - (s ^ 2 + r))
          ((s ^ 2 + r) / (s + 1)) ((s ^ 2 + r) % (s + 1)) := by
  cases s with
  | zero => omega
  | succ n =>
    let a := (n + 1) ^ 2 + r
    let u := (n + 2) ^ 2 - a
    have ha : a = (n + 1) ^ 2 + r := rfl
    change r ≤ 2 * (n + 1) at hr
    change n + 2 ≤ a at hsize
    change rootSum (a - (n + 2)) + (a - (n + 2)) + a ≤ rootSum a +
      (n + 1) * (a / (n + 2)) + largePartPenalty (n + 1) u (a / (n + 2)) (a % (n + 2))
    have hule : a ≤ (n + 2) ^ 2 := by nlinarith only [ha, hr]
    have huadd : u + a = (n + 2) ^ 2 := Nat.sub_add_cancel hule
    have hu : u + r = 2 * n + 3 := by nlinarith only [ha, huadd]
    have hsub := Nat.sub_add_cancel hsize
    have hmono := rootSum_mono (Nat.sub_le a (n + 2))
    have hdelta := Nat.sub_add_cancel hmono
    by_cases hsmall : r ≤ n
    · have hdiv : a / (n + 2) = n :=
        Nat.div_eq_of_lt_le (by nlinarith only [ha]) (by nlinarith only [ha, hsmall])
      have hm := Nat.mod_add_div a (n + 2)
      rw [hdiv] at hm
      have hmod : a % (n + 2) = r + 1 := by nlinarith only [hm, ha]
      have hpen : largePartPenalty (n + 1) u n (r + 1) = r + 1 := by
        unfold largePartPenalty
        rw [show n - u = 0 by omega, show n + 1 - u = 0 by omega]
        simp only [Nat.add_zero]
        exact Nat.min_eq_left (by omega)
      have hw : rootWindow (a - (n + 2)) a + 1 = a :=
        rootWindow_base_low (n + 1) r (by omega) (by omega) hsize
      unfold rootWindow at hw
      rw [hdiv, hmod, hpen]
      nlinarith only [ha, hsub, hdelta, hw]
    · let q := r - (n + 1)
      have hq : r = n + 1 + q := by dsimp [q]; omega
      have hqbound : q ≤ n + 1 := by omega
      have huq : u + q = n + 2 := by omega
      have hlarge : n + 1 ≤ r := by omega
      have hdiv : a / (n + 2) = n + 1 :=
        Nat.div_eq_of_lt_le (by nlinarith only [ha, hlarge]) (by nlinarith only [ha, hr])
      have hm := Nat.mod_add_div a (n + 2)
      rw [hdiv] at hm
      have hmod : a % (n + 2) = q := by nlinarith only [hm, ha, hq]
      rw [hdiv, hmod]
      by_cases hzero : q = 0
      · have hrEq : r = n + 1 := by omega
        have hpen : largePartPenalty (n + 1) u (n + 1) q = 0 := by
          unfold largePartPenalty
          rw [hzero, show n + 1 - u = 0 by omega, show n + 1 + 1 - u = 0 by omega]
          simp
        have hw : rootWindow (a - (n + 2)) a + 1 = a :=
          rootWindow_base_low (n + 1) r (by omega) (by omega) hsize
        unfold rootWindow at hw
        rw [hpen]
        nlinarith only [ha, hsub, hdelta, hw, hrEq]
      · have hqpos : 0 < q := by omega
        have hpen : largePartPenalty (n + 1) u (n + 1) q = q + (q - 1) := by
          unfold largePartPenalty
          rw [show n + 1 - u = q - 1 by omega, show n + 1 + 1 - u = q by omega]
          exact Nat.min_eq_left (by omega)
        have hw : rootWindow (a - (n + 2)) a = (n + 1) * (n + 2) :=
          rootWindow_base_high (n + 1) r (by omega) hr
        unfold rootWindow at hw
        have hqsub : q - 1 + 1 = q := by omega
        rw [hpen]
        nlinarith only [ha, hsub, hdelta, hw, hq, hqsub]

/-- Lemma 5.1(iii), including the quotient/remainder and penalty computation. -/
theorem backward_initial (a : ℕ) (ha : 0 < a) (hsize : Nat.sqrt a + 1 ≤ a) :
    rootSum (a - (Nat.sqrt a + 1)) + (a - (Nat.sqrt a + 1)) + a ≤
      rootSum a + Nat.sqrt a * (a / (Nat.sqrt a + 1)) +
        largePartPenalty (Nat.sqrt a) (nextSquareDistance a)
          (a / (Nat.sqrt a + 1)) (a % (Nat.sqrt a + 1)) := by
  let s := Nat.sqrt a
  let r := a - s ^ 2
  have hs : 0 < s := Nat.sqrt_pos.mpr ha
  have hlo : s ^ 2 ≤ a := Nat.sqrt_le' a
  have hhi : a < (s + 1) ^ 2 := by simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' a
  have hparts : a = s ^ 2 + r := by dsimp [r]; omega
  have hr : r ≤ 2 * s := by nlinarith only [hhi, hparts]
  have h := backward_initial_parametric s r hs hr (by omega)
  rw [← hparts] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- The low-remainder initial case has at least one unit of slack. -/
theorem backward_initial_small_parametric (s r : ℕ) (hs : 0 < s) (hr : r < s)
    (hsize : s + 1 ≤ s ^ 2 + r) :
    rootSum (s ^ 2 + r - (s + 1)) + (s ^ 2 + r - (s + 1)) + (s ^ 2 + r) + 1 ≤
      rootSum (s ^ 2 + r) + s * ((s ^ 2 + r) / (s + 1)) +
        largePartPenalty s ((s + 1) ^ 2 - (s ^ 2 + r))
          ((s ^ 2 + r) / (s + 1)) ((s ^ 2 + r) % (s + 1)) := by
  cases s with
  | zero => omega
  | succ n =>
    let a := (n + 1) ^ 2 + r
    let u := (n + 2) ^ 2 - a
    have ha : a = (n + 1) ^ 2 + r := rfl
    change r < n + 1 at hr
    change n + 2 ≤ a at hsize
    change rootSum (a - (n + 2)) + (a - (n + 2)) + a + 1 ≤ rootSum a +
      (n + 1) * (a / (n + 2)) + largePartPenalty (n + 1) u (a / (n + 2)) (a % (n + 2))
    have hule : a ≤ (n + 2) ^ 2 := by nlinarith only [ha, hr]
    have huadd : u + a = (n + 2) ^ 2 := Nat.sub_add_cancel hule
    have hu : u + r = 2 * n + 3 := by nlinarith only [ha, huadd]
    have hsub := Nat.sub_add_cancel hsize
    have hmono := rootSum_mono (Nat.sub_le a (n + 2))
    have hdelta := Nat.sub_add_cancel hmono
    have hdiv : a / (n + 2) = n :=
      Nat.div_eq_of_lt_le (by nlinarith only [ha]) (by nlinarith only [ha, hr])
    have hm := Nat.mod_add_div a (n + 2)
    rw [hdiv] at hm
    have hmod : a % (n + 2) = r + 1 := by nlinarith only [hm, ha]
    have hpen : largePartPenalty (n + 1) u n (r + 1) = r + 1 := by
      unfold largePartPenalty
      rw [show n - u = 0 by omega, show n + 1 - u = 0 by omega]
      simp only [Nat.add_zero]
      exact Nat.min_eq_left (by omega)
    have hw : rootWindow (a - (n + 2)) a + 1 = a :=
      rootWindow_base_low (n + 1) r (by omega) (by omega) hsize
    unfold rootWindow at hw
    rw [hdiv, hmod, hpen]
    nlinarith only [ha, hsub, hdelta, hw]

theorem backward_initial_strict (a : ℕ) (ha : 0 < a) (hsize : Nat.sqrt a + 1 ≤ a)
    (hsmall : a - Nat.sqrt a ^ 2 < Nat.sqrt a) :
    rootSum (a - (Nat.sqrt a + 1)) + (a - (Nat.sqrt a + 1)) + a <
      rootSum a + Nat.sqrt a * (a / (Nat.sqrt a + 1)) +
        largePartPenalty (Nat.sqrt a) (nextSquareDistance a)
          (a / (Nat.sqrt a + 1)) (a % (Nat.sqrt a + 1)) := by
  let s := Nat.sqrt a
  let r := a - s ^ 2
  have hs : 0 < s := Nat.sqrt_pos.mpr ha
  have hlo : s ^ 2 ≤ a := Nat.sqrt_le' a
  have hparts : a = s ^ 2 + r := by dsimp [r]; omega
  have h := backward_initial_small_parametric s r hs hsmall (by omega)
  rw [← hparts] at h
  exact lt_of_lt_of_le (Nat.lt_succ_self _) h

end ProteinFolding.Tetrahedral

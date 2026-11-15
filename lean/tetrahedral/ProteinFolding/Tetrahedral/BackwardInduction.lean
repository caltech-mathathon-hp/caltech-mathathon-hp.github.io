import ProteinFolding.Tetrahedral.LargePart

/-! The induction in t for the backward-window bound, Lemma 5.1(iv). -/

namespace ProteinFolding.Tetrahedral

theorem backward_quotient_le_sqrt (a t : ℕ) (ht : Nat.sqrt a < t) :
    a / t ≤ Nat.sqrt a := by
  have htpos : 0 < t := by omega
  have hsquare := Nat.lt_succ_sqrt' a
  simp only [Nat.succ_eq_add_one] at hsquare
  have hmul := Nat.mul_le_mul_left (Nat.sqrt a + 1) (show Nat.sqrt a + 1 ≤ t by omega)
  have hlt : a < (Nat.sqrt a + 1) * t := by nlinarith
  have hdiv := (Nat.div_lt_iff_lt_mul htpos).mpr hlt
  omega

theorem backward_quotient_changes_by_at_most_one (a t : ℕ) (ht : Nat.sqrt a < t) :
    a / (t + 1) = a / t ∨ a / (t + 1) + 1 = a / t := by
  have htpos : 0 < t := by omega
  have hjle := backward_quotient_le_sqrt a t ht
  have hjt : a / t < t := by omega
  have hmono : a / (t + 1) ≤ a / t := Nat.div_le_div_left (by omega) htpos
  have hlo := Nat.div_mul_le_self a t
  have hhi := Nat.lt_mul_div_succ a (show 0 < t + 1 by omega)
  have hdiff : a / t ≤ a / (t + 1) + 1 := by
    by_contra hnot
    have hlarge : a / (t + 1) + 2 ≤ a / t := by omega
    have hmul := Nat.mul_le_mul_right t hlarge
    nlinarith
  omega

theorem backward_equal_quotient_penalty (s u j q q' : ℕ) (hq : q = q' + j) :
    largePartPenalty s u j q ≤ largePartPenalty s u j q' + j := by
  unfold largePartPenalty
  omega

theorem backward_drop_quotient_penalty (s u j q q' t : ℕ) (hj : 0 < j)
    (ht : s + 1 ≤ t) (hq : q < j) (hrel : q' + j = q + t + 1) :
    largePartPenalty s u j q + s + 1 ≤
      largePartPenalty s u (j - 1) q' + j := by
  have hstep : j - u ≤ (j - 1 - u) + 1 := by omega
  have hnext : j - 1 + 1 - u = j - u := by omega
  have hpen := min_le_left (q + (j - u)) (s + (j + 1 - u))
  unfold largePartPenalty
  rw [hnext]
  omega

theorem backward_quotient_predecessor_le_sqrt (a t : ℕ)
    (ht : Nat.sqrt a < t) (hta : t < a) :
    a / t - 1 ≤ Nat.sqrt (a - (t + 1)) := by
  by_cases hj : a / t ≤ 1
  · have heq : a / t - 1 = 0 := by omega
    rw [heq]
    exact Nat.zero_le _
  · have hjpos : 2 ≤ a / t := by omega
    have hjle := backward_quotient_le_sqrt a t ht
    let k := a / t - 1
    have hkpos : 0 < k := by dsimp [k]; omega
    have hkj : a / t = k + 1 := by dsimp [k]; omega
    have hkt : k + 2 ≤ t := by omega
    have hprod := Nat.mul_le_mul_left k hkt
    have hlo := Nat.div_mul_le_self a t
    rw [hkj] at hlo
    have hsub := Nat.sub_add_cancel (show t + 1 ≤ a by omega)
    apply Nat.le_sqrt'.mpr
    change k ^ 2 ≤ a - (t + 1)
    nlinarith

/-- The right side's quotient/penalty contribution can lose at most j per step. -/
theorem backward_contribution_step (a t : ℕ) (ht : Nat.sqrt a < t) (hta : t < a) :
    Nat.sqrt a * (a / t) +
      largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / t) (a % t) ≤
    Nat.sqrt a * (a / (t + 1)) +
      largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / (t + 1)) (a % (t + 1)) + a / t := by
  have htpos : 0 < t := by omega
  have hjpos : 0 < a / t := Nat.div_pos (by omega) htpos
  have hdecomp := Nat.div_add_mod' a t
  have hdecomp' := Nat.div_add_mod' a (t + 1)
  rcases backward_quotient_changes_by_at_most_one a t ht with heq | heq
  · have hrel : a % t = a % (t + 1) + a / t := by
      rw [heq] at hdecomp'
      nlinarith
    have hpen := backward_equal_quotient_penalty (Nat.sqrt a) (nextSquareDistance a)
      (a / t) (a % t) (a % (t + 1)) hrel
    rw [heq]
    omega
  · have hrel : a % (t + 1) + a / t = a % t + t + 1 := by
      nlinarith
    have hrem := Nat.mod_lt a (show 0 < t + 1 by omega)
    have hq : a % t < a / t := by omega
    have hpen := backward_drop_quotient_penalty (Nat.sqrt a) (nextSquareDistance a)
      (a / t) (a % t) (a % (t + 1)) t hjpos (by omega) hq hrel
    have hj : a / (t + 1) = a / t - 1 := by omega
    have hprod : Nat.sqrt a * (a / (t + 1)) + Nat.sqrt a = Nat.sqrt a * (a / t) := by
      rw [← Nat.mul_succ]
      exact congrArg (fun n => Nat.sqrt a * n) (show (a / (t + 1)).succ = a / t by omega)
    rw [← hj] at hpen
    omega

/-- The actual one-step propagation of the backward-window estimate. -/
theorem backwardRootBound_step (a t : ℕ) (ht : Nat.sqrt a < t) (hta : t < a)
    (hbound : rootSum (a - t) + (a - t) + a ≤ rootSum a + Nat.sqrt a * (a / t) +
      largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / t) (a % t)) :
    rootSum (a - (t + 1)) + (a - (t + 1)) + a ≤
      rootSum a + Nat.sqrt a * (a / (t + 1)) +
        largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / (t + 1)) (a % (t + 1)) := by
  have hstep := backward_contribution_step a t ht hta
  have hsqrt := backward_quotient_predecessor_le_sqrt a t ht hta
  have hindex : a - t = a - (t + 1) + 1 := by omega
  rw [hindex, rootSum_succ] at hbound
  have hjpos : 0 < a / t := Nat.div_pos (by omega) (by omega)
  omega

/-- The same argument preserves every nonnegative offset, so strict slack at
the initial case cannot disappear during the induction. -/
theorem backwardRootBound_step_with_slack (a t d : ℕ) (ht : Nat.sqrt a < t) (hta : t < a)
    (hbound : rootSum (a - t) + (a - t) + a + d ≤ rootSum a + Nat.sqrt a * (a / t) +
      largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / t) (a % t)) :
    rootSum (a - (t + 1)) + (a - (t + 1)) + a + d ≤
      rootSum a + Nat.sqrt a * (a / (t + 1)) +
        largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / (t + 1)) (a % (t + 1)) := by
  have hstep := backward_contribution_step a t ht hta
  have hsqrt := backward_quotient_predecessor_le_sqrt a t ht hta
  have hindex : a - t = a - (t + 1) + 1 := by omega
  rw [hindex, rootSum_succ] at hbound
  have hjpos : 0 < a / t := Nat.div_pos (by omega) (by omega)
  omega

theorem backwardRootBound_from_initial_with_slack (a d : ℕ)
    (hinitial : rootSum (a - (Nat.sqrt a + 1)) + (a - (Nat.sqrt a + 1)) + a + d ≤
      rootSum a + Nat.sqrt a * (a / (Nat.sqrt a + 1)) +
        largePartPenalty (Nat.sqrt a) (nextSquareDistance a)
          (a / (Nat.sqrt a + 1)) (a % (Nat.sqrt a + 1)))
    (t : ℕ) (ht : Nat.sqrt a < t) (hta : t ≤ a) :
    rootSum (a - t) + (a - t) + a + d ≤ rootSum a + Nat.sqrt a * (a / t) +
      largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / t) (a % t) := by
  let P : ℕ → Prop := fun x => rootSum (a - x) + (a - x) + a + d ≤
    rootSum a + Nat.sqrt a * (a / x) +
      largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / x) (a % x)
  have hbase : P (Nat.sqrt a + 1) := hinitial
  have hstep : ∀ x, Nat.sqrt a + 1 ≤ x → x < a → P x → P (x + 1) := by
    intro x hx hxa hpx
    exact backwardRootBound_step_with_slack a x d (by omega) hxa hpx
  have hall : ∀ n : ℕ, Nat.sqrt a + 1 + n ≤ a → P (Nat.sqrt a + 1 + n) := by
    intro n
    induction n with
    | zero => intro _; simpa using hbase
    | succ n ih =>
      intro hn
      have hp := ih (show Nat.sqrt a + 1 + n ≤ a by omega)
      have hs := hstep (Nat.sqrt a + 1 + n) (by omega) (by omega) hp
      have heq : Nat.sqrt a + 1 + (n + 1) = (Nat.sqrt a + 1 + n) + 1 := by omega
      simpa only [heq] using hs
  have hindex : Nat.sqrt a + 1 + (t - (Nat.sqrt a + 1)) = t := by omega
  have hfinal := hall (t - (Nat.sqrt a + 1)) (by omega)
  rw [hindex] at hfinal
  exact hfinal

/-- Iterating the proved step establishes the full estimate from its initial case. -/
theorem backwardRootBound_of_initial
    (hinitial : ∀ a : ℕ, 0 < a → Nat.sqrt a + 1 ≤ a →
      rootSum (a - (Nat.sqrt a + 1)) + (a - (Nat.sqrt a + 1)) + a ≤
        rootSum a + Nat.sqrt a * (a / (Nat.sqrt a + 1)) +
          largePartPenalty (Nat.sqrt a) (nextSquareDistance a)
            (a / (Nat.sqrt a + 1)) (a % (Nat.sqrt a + 1))) : BackwardRootBound := by
  intro a t ha ht hta
  let P : ℕ → Prop := fun x => rootSum (a - x) + (a - x) + a ≤
    rootSum a + Nat.sqrt a * (a / x) +
      largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / x) (a % x)
  have hbase : P (Nat.sqrt a + 1) := hinitial a ha (by omega)
  have hstep : ∀ x, Nat.sqrt a + 1 ≤ x → x < a → P x → P (x + 1) := by
    intro x hx hxa hpx
    exact backwardRootBound_step a x (by omega) hxa hpx
  have hall : ∀ n : ℕ, Nat.sqrt a + 1 + n ≤ a → P (Nat.sqrt a + 1 + n) := by
    intro n
    induction n with
    | zero => intro _; simpa using hbase
    | succ n ih =>
      intro hn
      have hp := ih (show Nat.sqrt a + 1 + n ≤ a by omega)
      have hs := hstep (Nat.sqrt a + 1 + n) (by omega) (by omega) hp
      have heq : Nat.sqrt a + 1 + (n + 1) = (Nat.sqrt a + 1 + n) + 1 := by omega
      simpa only [heq] using hs
  have hindex : Nat.sqrt a + 1 + (t - (Nat.sqrt a + 1)) = t := by omega
  have hfinal := hall (t - (Nat.sqrt a + 1)) (by omega)
  rw [hindex] at hfinal
  exact hfinal

end ProteinFolding.Tetrahedral

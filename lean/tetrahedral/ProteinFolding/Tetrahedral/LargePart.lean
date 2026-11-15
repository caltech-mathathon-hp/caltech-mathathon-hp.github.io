import ProteinFolding.Tetrahedral.OneSided

/-!
# Arithmetic for the large-part transition (Lemma 5.1)

The extra contribution after crossing the next square is proved here.
The full `LargePartStep` inequality and its equality classification remain
proof obligations; this module does not declare them as assumptions.
-/

namespace ProteinFolding.Tetrahedral

def nextSquareDistance (a : ℕ) : ℕ := (Nat.sqrt a + 1) ^ 2 - a

theorem nextSquareDistance_pos (a : ℕ) : 0 < nextSquareDistance a := by
  have h := Nat.lt_succ_sqrt' a
  simp only [Nat.succ_eq_add_one] at h
  unfold nextSquareDistance
  omega

theorem add_nextSquareDistance (a : ℕ) :
    a + nextSquareDistance a = (Nat.sqrt a + 1) ^ 2 := by
  have h := Nat.lt_succ_sqrt' a
  simp only [Nat.succ_eq_add_one] at h
  unfold nextSquareDistance
  omega

/-- Lemma 5.1(i): the window gains one extra unit per term beyond the next square. -/
theorem rootWindow_enhanced_lower (a l : ℕ) :
    Nat.sqrt a * l + (l - nextSquareDistance a) ≤ rootWindow a (a + l) := by
  by_cases hl : l ≤ nextSquareDistance a
  · rw [Nat.sub_eq_zero_of_le hl, Nat.add_zero]
    exact rootWindow_add_lower a l
  · have hu : nextSquareDistance a ≤ l := by omega
    have h₁ := rootSum_add_lower a (nextSquareDistance a)
    have h₂ := rootSum_add_lower (a + nextSquareDistance a) (l - nextSquareDistance a)
    have hsqrt : Nat.sqrt (a + nextSquareDistance a) = Nat.sqrt a + 1 := by
      rw [add_nextSquareDistance, Nat.sqrt_eq']
    rw [hsqrt, Nat.add_mul, Nat.one_mul] at h₂
    have hsum : a + nextSquareDistance a + (l - nextSquareDistance a) = a + l := by omega
    rw [hsum] at h₂
    have hparts : l = nextSquareDistance a + (l - nextSquareDistance a) := by omega
    have hmul := congrArg (fun x => Nat.sqrt a * x) hparts
    dsimp only at hmul
    rw [Nat.mul_add] at hmul
    unfold rootWindow
    omega

/-- The two candidates from Lemma 5.1(ii), written without signed subtraction. -/
def largePartPenalty (s u j q : ℕ) : ℕ := min (q + (j - u)) (s + (j + 1 - u))

/-- The maximum over all final parts is controlled by the two parts j and j+1.
Later one takes j = a/t, q = a mod t, s = floor(sqrt(a)). -/
theorem largePart_two_point_bound (a s t j q u l : ℕ)
    (ha : a = j * t + q) (ht : s + 1 ≤ t) :
    min a (t * l) + s * j + largePartPenalty s u j q ≤ a + s * l + (l - u) := by
  by_cases hl : l ≤ j
  · let d := j - l
    have hj : j = l + d := by dsimp [d]; omega
    have hprod := Nat.mul_le_mul_right d ht
    rw [Nat.add_mul, Nat.one_mul] at hprod
    have he : j - u ≤ (l - u) + d := by dsimp [d]; omega
    have hpen : largePartPenalty s u j q ≤ q + (j - u) := min_le_left _ _
    have hmin := min_le_right a (t * l)
    have hA : a = t * l + t * d + q := by rw [ha, hj]; ring
    have hS : s * j = s * l + s * d := by rw [hj, Nat.mul_add]
    omega
  · have hprod := Nat.mul_le_mul_left s (show j + 1 ≤ l by omega)
    rw [Nat.mul_succ] at hprod
    have he : j + 1 - u ≤ l - u := by omega
    have hpen : largePartPenalty s u j q ≤ s + (j + 1 - u) := min_le_right _ _
    have hmin := min_le_left a (t * l)
    omega

/-- The remaining backward-window estimate in Lemma 5.1(iii)–(iv), in a
subtraction-free form. This is a proof target; it has not been established. -/
def BackwardRootBound : Prop := ∀ a t : ℕ, 0 < a → Nat.sqrt a < t → t ≤ a →
  rootSum (a - t) + (a - t) + a ≤ rootSum a + Nat.sqrt a * (a / t) +
    largePartPenalty (Nat.sqrt a) (nextSquareDistance a) (a / t) (a % t)

/-- The enhanced forward window and the two-point reduction discharge the
rest of the large-part inequality once the backward bound has been proved. -/
theorem largePartStep_of_backwardRootBound (hback : BackwardRootBound) : LargePartStep := by
  intro a t l ha ht hta _
  have hdecomp : a = (a / t) * t + a % t := by
    nlinarith [Nat.mod_add_div a t]
  have htwo := largePart_two_point_bound a (Nat.sqrt a) t (a / t) (a % t)
    (nextSquareDistance a) l hdecomp (by omega)
  have hleft := hback a t ha ht hta
  have hright := rootWindow_enhanced_lower a l
  have hmono := rootSum_mono (Nat.le_add_right a l)
  unfold rootWindow at hright
  omega

end ProteinFolding.Tetrahedral

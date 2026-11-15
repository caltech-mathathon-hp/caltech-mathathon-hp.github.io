import ProteinFolding.Tetrahedral.FiniteSets
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The square-root sum in Section 5.3

F(x) = Σ_(0≤y<x) floor(sqrt(y)). These lemmas establish its basic window
bounds and its values at square breakpoints, used by the one-sided optimum
and the octahedral composition. No optimum or rigidity theorem is assumed.
-/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

def rootSum (x : ℕ) : ℕ := ∑ y ∈ Finset.range x, Nat.sqrt y

def rootWindow (a b : ℕ) : ℕ := rootSum b - rootSum a

@[simp] theorem rootSum_zero : rootSum 0 = 0 := by simp [rootSum]

theorem rootSum_succ (x : ℕ) : rootSum (x + 1) = rootSum x + Nat.sqrt x :=
  Finset.sum_range_succ _ _

theorem rootSum_mono : Monotone rootSum := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    (fun _ _ _ => Nat.zero_le _)

theorem rootWindow_add {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    rootWindow a b + rootWindow b c = rootWindow a c := by
  have h₁ := rootSum_mono hab
  have h₂ := rootSum_mono hbc
  unfold rootWindow
  omega

theorem rootSum_add_lower (a n : ℕ) :
    rootSum a + Nat.sqrt a * n ≤ rootSum (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    change rootSum a + Nat.sqrt a * (n + 1) ≤ rootSum ((a + n) + 1)
    rw [rootSum_succ, Nat.mul_succ]
    have hm := Nat.sqrt_le_sqrt (Nat.le_add_right a n)
    omega

/-- The lower window bound used in Case I of the one-sided induction. -/
theorem rootWindow_add_lower (a n : ℕ) :
    Nat.sqrt a * n ≤ rootWindow a (a + n) := by
  have h := rootSum_add_lower a n
  unfold rootWindow
  omega

/-- The complete numerical step in Case I of Lemma 5.2, when the preceding
part is at most floor(sqrt(a)). -/
theorem rootSum_small_part_step (a t l : ℕ) (ht : t ≤ Nat.sqrt a) :
    rootSum a + min a (t * l) ≤ rootSum (a + l) := by
  have hmin := min_le_right a (t * l)
  have hmul := Nat.mul_le_mul_right l ht
  have hwindow := rootSum_add_lower a l
  omega

/-- The numerical equality conditions for that case: the part must equal
floor(sqrt(a)), the product must not be truncated, and the window is linear. -/
theorem rootSum_small_part_equality (a t l : ℕ) (ht : t ≤ Nat.sqrt a) (hl : 0 < l)
    (heq : rootSum a + min a (t * l) = rootSum (a + l)) :
    t = Nat.sqrt a ∧ Nat.sqrt a * l ≤ a ∧
      rootSum (a + l) = rootSum a + Nat.sqrt a * l := by
  have hmin := min_le_right a (t * l)
  have hbound := min_le_left a (t * l)
  have hmul := Nat.mul_le_mul_right l ht
  have hwindow := rootSum_add_lower a l
  have hts : t = Nat.sqrt a := by
    apply le_antisymm ht
    by_contra hnot
    have hlt : t < Nat.sqrt a := by omega
    have hprod := Nat.mul_lt_mul_of_pos_right hlt hl
    omega
  exact ⟨hts, by omega, by omega⟩

theorem rootSum_add_of_constant (a n s : ℕ)
    (hs : ∀ i < n, Nat.sqrt (a + i) = s) : rootSum (a + n) = rootSum a + s * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev : ∀ i < n, Nat.sqrt (a + i) = s := fun i hi => hs i (by omega)
    rw [Nat.add_succ, rootSum_succ, ih hprev, hs n (by omega), Nat.mul_succ]
    omega

theorem rootSum_square_block (s r : ℕ) (hr : r ≤ 2 * s + 1) :
    rootSum (s ^ 2 + r) = rootSum (s ^ 2) + s * r := by
  apply rootSum_add_of_constant
  intro i hi
  exact Nat.sqrt_add_eq' s (by omega)

theorem rootSum_square_succ (s : ℕ) :
    rootSum ((s + 1) ^ 2) = rootSum (s ^ 2) + s * (2 * s + 1) := by
  have heq : (s + 1) ^ 2 = s ^ 2 + (2 * s + 1) := by ring
  rw [heq]
  exact rootSum_square_block s _ le_rfl

/-- The closed square-breakpoint sum, without division or truncated subtraction. -/
theorem rootSum_square_polynomial (s : ℕ) :
    6 * rootSum (s ^ 2) + 3 * s ^ 2 + s = 4 * s ^ 3 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [rootSum_square_succ]
    nlinarith [ih]

/-- The octahedral site number in Claim U, N_m = m² + 2F(m²). -/
def octahedralNumber (m : ℕ) : ℕ := m ^ 2 + 2 * rootSum (m ^ 2)

theorem octahedralNumber_polynomial (m : ℕ) :
    3 * octahedralNumber m + m = 4 * m ^ 3 := by
  unfold octahedralNumber
  have h := rootSum_square_polynomial m
  nlinarith

theorem octahedralNumber_succ (m : ℕ) :
    octahedralNumber (m + 1) = octahedralNumber m + (2 * m + 1) ^ 2 := by
  unfold octahedralNumber
  rw [rootSum_square_succ]
  ring

theorem octahedralNumber_formula (m : ℕ) :
    octahedralNumber m = m * (4 * m ^ 2 - 1) / 3 := by
  cases m with
  | zero => simp [octahedralNumber]
  | succ m =>
    have h := octahedralNumber_polynomial (m + 1)
    have hpos : 1 ≤ 4 * (m + 1) ^ 2 := by nlinarith
    have hm : (m + 1) * (4 * (m + 1) ^ 2 - 1) =
        3 * octahedralNumber (m + 1) := by
      have hsub := Nat.sub_add_cancel hpos
      nlinarith
    rw [hm]
    omega

end ProteinFolding.Tetrahedral

import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

/-! An injective finite integer sequence with unit steps has one direction. -/

namespace ProteinFolding.Tetrahedral

private theorem integer_unit_segment_increasing (N : ℕ) (f : ℕ → ℤ)
    (hstep : ∀ i < N, f (i + 1) = f i + 1 ∨ f (i + 1) = f i - 1)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, f i = f j → i = j)
    (hfirst : f 1 = f 0 + 1) : ∀ i ≤ N, f i = f 0 + (i : ℤ) := by
  have hdir : ∀ i, i < N → f (i + 1) = f i + 1 := by
    intro i
    induction i with
    | zero => intro _; exact hfirst
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      rcases hstep (i + 1) hi with hup | hdown
      · exact hup
      · change f (i + 2) = f (i + 1) - 1 at hdown
        have heq : f i = f (i + 2) := by omega
        have hbad := hinj i (by omega) (i + 2) (by omega) heq
        omega
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hnext := hdir i (by omega)
    omega

theorem integer_unit_segment_affine (N : ℕ) (f : ℕ → ℤ)
    (hstep : ∀ i < N, f (i + 1) = f i + 1 ∨ f (i + 1) = f i - 1)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, f i = f j → i = j) :
    (∀ i ≤ N, f i = f 0 + (i : ℤ)) ∨ (∀ i ≤ N, f i = f 0 - (i : ℤ)) := by
  by_cases hN : N = 0
  · left
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    change f 0 = f 0 + 0
    omega
  · rcases hstep 0 (by omega) with hfirst | hfirst
    · exact Or.inl (integer_unit_segment_increasing N f hstep hinj hfirst)
    · right
      change f 1 = f 0 - 1 at hfirst
      have hnegstep : ∀ i < N, -f (i + 1) = -f i + 1 ∨ -f (i + 1) = -f i - 1 := by
        intro i hi
        rcases hstep i hi with hup | hdown <;> omega
      have hneginj : ∀ i ≤ N, ∀ j ≤ N, -f i = -f j → i = j := by
        intro i hi j hj heq
        exact hinj i hi j hj (by omega)
      have hnegfirst : -f 1 = -f 0 + 1 := by omega
      have hneg := integer_unit_segment_increasing N (fun i => -f i)
        hnegstep hneginj hnegfirst
      intro i hi
      have h := hneg i hi
      change -f i = -f 0 + (i : ℤ) at h
      omega

theorem integer_affine_zero_endpoint_signs (N : ℕ) (f : ℕ → ℤ) (j : ℕ)
    (hj0 : 0 < j) (hjN : j < N) (hzero : f j = 0)
    (haffine : (∀ i ≤ N, f i = f 0 + (i : ℤ)) ∨
      (∀ i ≤ N, f i = f 0 - (i : ℤ))) :
    (f 0 < 0 ∧ 0 < f N) ∨ (0 < f 0 ∧ f N < 0) := by
  rcases haffine with hup | hdown
  · have hj := hup j (by omega)
    have hN := hup N (le_refl _)
    left
    constructor <;> omega
  · have hj := hdown j (by omega)
    have hN := hdown N (le_refl _)
    right
    constructor <;> omega

end ProteinFolding.Tetrahedral

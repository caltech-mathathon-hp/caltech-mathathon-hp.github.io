import ProteinFolding.Common.SAT.ThreeDimensionalMatching
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Consistency of the variable-cycle gadget in the SAT-to-3DM construction.
Each Y vertex chooses either the same X index or its cyclic successor. Exact
X coverage makes these choices constant around each variable's occurrence
cycle. This proof uses the finite permutation property and does not assume
any complexity result. -/

namespace ProteinFolding.ThreeDimensionalMatching

def cycleSelector {α : Type} (σ : Equiv.Perm α) (b : α → Bool) (i : α) : α :=
  if b i then i else σ i

theorem selector_injective_forces_invariance {α : Type} [Finite α]
    (σ : Equiv.Perm α) (b : α → Bool) (h : Function.Injective (cycleSelector σ b)) :
    ∀ i, b (σ i) = b i := by
  have hsurj := Finite.surjective_of_injective h
  intro i
  cases hi : b i <;> cases hs : b (σ i)
  · rfl
  · have he : cycleSelector σ b i = cycleSelector σ b (σ i) := by
      simp [cycleSelector, hi, hs]
    have he' := h he
    rw [he'] at hi
    simp [hs] at hi
  · obtain ⟨j, hj⟩ := hsurj (σ i)
    cases hb : b j
    · have he : σ j = σ i := by simpa [cycleSelector, hb] using hj
      have he' := σ.injective he
      rw [he'] at hb
      simp [hi] at hb
    · have he : j = σ i := by simpa [cycleSelector, hb] using hj
      rw [he] at hb
      simp [hs] at hb
  · rfl

/-- A perfect matching of a variable-cycle gadget has one uniform truth
choice across every occurrence, even for a one-occurrence cycle. -/
theorem cycle_selector_constant (n : ℕ) (b : Fin n → Bool)
    (h : Function.Injective (cycleSelector (finRotate n) b)) :
    ∀ i j, b i = b j := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    have hi := selector_injective_forces_invariance (finRotate (n + 1)) b h
    have hz : ∀ i : Fin (n + 1), b i = b 0 := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
        have he : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
        exact (he ▸ hi i.castSucc).trans ih
    intro i j
    exact (hz i).trans (hz j).symm

def selectorPerm {α : Type} (σ : Equiv.Perm α) (b : α → Bool)
    (h : ∀ i, b (σ i) = b i) : Equiv.Perm α where
  toFun := cycleSelector σ b
  invFun i := if b i then i else σ.symm i
  left_inv i := by
    cases hi : b i
    · simp [cycleSelector, hi, h i]
    · simp [cycleSelector, hi]
  right_inv i := by
    have hs : b (σ.symm i) = b i := by simpa using (h (σ.symm i)).symm
    cases hi : b i
    · simp [cycleSelector, hi, hs]
    · simp [cycleSelector, hi]

end ProteinFolding.ThreeDimensionalMatching

import ProteinFolding.Common.SAT.MatchingGadgetComplete
import Mathlib.Data.Finset.Sort

/-! Constructive occurrence cycles grouped by equality of variable identifiers.
Each finite fiber is sorted by occurrence index before cyclic rotation. This
does not enumerate all natural numbers below an original variable identifier.
The construction therefore remains suitable for binary-index SAT inputs. -/

namespace ProteinFolding.ThreeDimensionalMatching

open Fin.NatCast

theorem finRotate_iterate (n : ℕ) (i : Fin (n + 1)) (k : ℕ) :
    (finRotate (n + 1))^[k] i = i + (k : Fin (n + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', finRotate_succ_apply, ih]
    simp [Nat.cast_add, add_assoc]

theorem finRotate_connected (n : ℕ) (i j : Fin n) :
    ∃ k : ℕ, (finRotate n)^[k] i = j := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    refine ⟨(j - i).val, ?_⟩
    rw [finRotate_iterate, Fin.cast_val_eq_self]
    rw [← add_sub_assoc, add_sub_cancel_left]

def rotateOn {n : ℕ} {α : Type} (e : Fin n ≃ α) : Equiv.Perm α :=
  e.symm.trans ((finRotate n).trans e)

theorem rotateOn_iterate {n : ℕ} {α : Type} (e : Fin n ≃ α) (i : Fin n) (k : ℕ) :
    (rotateOn e)^[k] (e i) = e ((finRotate n)^[k] i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp [rotateOn]

theorem rotateOn_connected {n : ℕ} {α : Type} (e : Fin n ≃ α) (i j : α) :
    ∃ k : ℕ, (rotateOn e)^[k] i = j := by
  obtain ⟨k, hk⟩ := finRotate_connected n (e.symm i) (e.symm j)
  refine ⟨k, ?_⟩
  have h := rotateOn_iterate e (e.symm i) k
  simpa [hk] using h

def variableFiberSet {q : ℕ} (v : Fin q → ℕ) (a : ℕ) : Finset (Fin q) :=
  Finset.univ.filter (fun i => v i = a)

def variableFiberEquiv {q : ℕ} (v : Fin q → ℕ) (a : ℕ) :
    Fin (variableFiberSet v a).card ≃ {i : Fin q // v i = a} :=
  ((variableFiberSet v a).orderIsoOfFin rfl).toEquiv.trans
    (Equiv.subtypeEquivRight (fun i => by simp [variableFiberSet]))

def variableFiberCycle {q : ℕ} (v : Fin q → ℕ) (a : ℕ) :
    Equiv.Perm {i : Fin q // v i = a} := rotateOn (variableFiberEquiv v a)

def occurrenceCycle {q : ℕ} (v : Fin q → ℕ) : Equiv.Perm (Fin q) :=
  (Equiv.sigmaFiberEquiv v).symm.trans
    ((Equiv.sigmaCongrRight (variableFiberCycle v)).trans (Equiv.sigmaFiberEquiv v))

theorem occurrenceCycle_fiber {q : ℕ} (v : Fin q → ℕ) (a : ℕ)
    (i : {i : Fin q // v i = a}) :
    occurrenceCycle v i.val = (variableFiberCycle v a i).val := by
  obtain ⟨i, hi⟩ := i
  subst a
  rfl

theorem occurrenceCycle_variable {q : ℕ} (v : Fin q → ℕ) (i : Fin q) :
    v (occurrenceCycle v i) = v i :=
  (variableFiberCycle v (v i) ⟨i, rfl⟩).property

theorem occurrenceCycle_fiber_iterate {q : ℕ} (v : Fin q → ℕ) (a : ℕ)
    (i : {i : Fin q // v i = a}) (k : ℕ) :
    (occurrenceCycle v)^[k] i.val = ((variableFiberCycle v a)^[k] i).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      occurrenceCycle_fiber]

theorem occurrenceCycle_connected {q : ℕ} (v : Fin q → ℕ) (i j : Fin q)
    (h : v i = v j) : ∃ k : ℕ, (occurrenceCycle v)^[k] i = j := by
  let y : {k : Fin q // v k = v i} := ⟨j, h.symm⟩
  obtain ⟨k, hk⟩ := rotateOn_connected (variableFiberEquiv v (v i)) ⟨i, rfl⟩ y
  refine ⟨k, ?_⟩
  have he := occurrenceCycle_fiber_iterate v (v i) ⟨i, rfl⟩ k
  rw [show (variableFiberCycle v (v i))^[k] ⟨i, rfl⟩ = y from hk] at he
  exact he

end ProteinFolding.ThreeDimensionalMatching

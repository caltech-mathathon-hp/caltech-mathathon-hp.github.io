import ProteinFolding.Common.CookLevinProofAlphabet

/-! Fixed-horizon runs of the actual mathlib machine. Padding repeats a
halted configuration. Theorems relate this total transition to the original
partial-step execution and its existing TM2OutputsInTime convention.
-/

namespace ProteinFolding.SAT.CookLevinPadded

open Turing TM2 CookLevinAlphabet

def paddedStep (tm : FinTM2) (c : tm.Cfg) : tm.Cfg := (tm.step c).getD c

theorem paddedStep_of_step (tm : FinTM2) {a b : tm.Cfg} (h : tm.step a = some b) :
    paddedStep tm a = b := by simp only [paddedStep, h, Option.getD_some]

theorem paddedStep_of_halted (tm : FinTM2) (c : tm.Cfg) (h : c.l = none) :
    paddedStep tm c = c := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => rfl
  | some l => contradiction

theorem paddedStep_haltList (tm : FinTM2) (out : List (tm.Γ tm.k₁)) :
    paddedStep tm (haltList tm out) = haltList tm out :=
  paddedStep_of_halted tm _ rfl

theorem paddedStep_stacksIn (tm : FinTM2) (c : tm.Cfg)
    (h : StacksIn (machineSymbols tm) c.stk) :
    StacksIn (machineSymbols tm) (paddedStep tm c).stk := by
  cases hs : tm.step c with
  | none => simpa only [paddedStep, hs, Option.getD_none] using h
  | some d =>
    rw [paddedStep_of_step tm hs]
    exact step_stacksIn tm c d h hs

theorem paddedStep_stack_length (tm : FinTM2) (c : tm.Cfg) (k : tm.K) :
    ((paddedStep tm c).stk k).length ≤ (c.stk k).length + TM2Bounds.machinePushBound tm := by
  cases hs : tm.step c with
  | none => simp only [paddedStep, hs, Option.getD_none]; omega
  | some d =>
    rw [paddedStep_of_step tm hs]
    exact TM2Bounds.step_stack_length tm c d k hs

theorem paddedRun_stacksIn (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (n : ℕ) :
    StacksIn (machineSymbols tm) ((paddedStep tm)^[n] (initList tm input)).stk := by
  induction n with
  | zero => exact initList_stacksIn tm input
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact paddedStep_stacksIn tm _ ih

theorem initList_stack_length (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm input).stk k).length ≤ input.length := by
  by_cases hk : k = tm.k₀
  · subst k; simp [initList]
  · simp [initList, hk]

theorem paddedRun_stack_length (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (n : ℕ) (k : tm.K) :
    (((paddedStep tm)^[n] (initList tm input)).stk k).length ≤
      input.length + n * TM2Bounds.machinePushBound tm := by
  induction n with
  | zero => simpa using initList_stack_length tm input k
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hs := paddedStep_stack_length tm ((paddedStep tm)^[n] (initList tm input)) k
    rw [Nat.succ_mul]
    omega

/-- Partial executions that have not dropped to none agree with the padded run. -/
theorem optionRun_paddedRun (tm : FinTM2) (a b : tm.Cfg) (n : ℕ)
    (h : (fun x : Option tm.Cfg => x.bind tm.step)^[n] (some a) = some b) :
    (paddedStep tm)^[n] a = b := by
  induction n generalizing b with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h ⊢
    change ((fun x : Option tm.Cfg => x.bind tm.step)^[n] (some a)).bind tm.step = some b at h
    cases hc : (fun x : Option tm.Cfg => x.bind tm.step)^[n] (some a) with
    | none => rw [hc] at h; contradiction
    | some c =>
      rw [hc] at h
      rw [ih c hc]
      exact paddedStep_of_step tm h

theorem paddedRun_of_fixed (tm : FinTM2) (a : tm.Cfg) (n : ℕ)
    (h : paddedStep tm a = a) : (paddedStep tm)^[n] a = a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, h]

theorem outputsInTime_paddedRun (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (out : List (tm.Γ tm.k₁)) (T : ℕ) (h : TM2OutputsInTime tm input (some out) T) :
    (paddedStep tm)^[T] (initList tm input) = haltList tm out := by
  have hr := optionRun_paddedRun tm (initList tm input) (haltList tm out) h.steps h.evals_in_steps
  have hb := h.steps_le_m
  have hT : T = (T - h.steps) + h.steps := by omega
  rw [hT, Function.iterate_add_apply, hr]
  exact paddedRun_of_fixed tm _ _ (paddedStep_haltList tm out)

end ProteinFolding.SAT.CookLevinPadded

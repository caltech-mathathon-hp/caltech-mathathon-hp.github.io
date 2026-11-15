import ProteinFolding.Common.TM2Transfer
import Mathlib.Algebra.BigOperators.Fin

/-! An actual TM2 scan of a direction word into six signed-unary counters.
Adjacent directions 0/1, 2/3, 4/5 are opposite signs on three axes. Cancelling
an opposite token before adding a same-sign token keeps the counters bounded.
This is a machine stage: its continuation still has to inspect or serialize
the counters. No complete geometric verifier is asserted by this module. -/

namespace ProteinFolding.TM2WalkCounters

open Turing TM2
open scoped BigOperators

inductive Stack where
  | input
  | counter : Fin 6 → Stack
  deriving DecidableEq, Fintype

inductive Phase where
  | scan
  | finish
  deriving DecidableEq, Fintype

def Alphabet (I : Type) : Stack → Type
  | .input => I
  | .counter _ => Unit

abbrev Counts := Fin 6 → ℕ

def opposite : Fin 6 → Fin 6
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 4

theorem opposite_ne (d : Fin 6) : opposite d ≠ d := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 => decide

def updateCounts (c : Counts) (d : Fin 6) : Counts :=
  match c (opposite d) with
  | 0 => Function.update c d (c d + 1)
  | m + 1 => Function.update c (opposite d) m

def runCounts : Counts → List (Fin 6) → Counts
  | c, [] => c
  | c, d :: ds => runCounts (updateCounts c d) ds

def totalCounts (c : Counts) : ℕ := c 0 + c 1 + c 2 + c 3 + c 4 + c 5

def coordinate (c : Counts) : Fin 3 → ℤ
  | 0 => (c 0 : ℤ) - c 1
  | 1 => (c 2 : ℤ) - c 3
  | 2 => (c 4 : ℤ) - c 5

def increment (d : Fin 6) (k : Fin 3) : ℤ :=
  if k = 0 then if d = 0 then 1 else if d = 1 then -1 else 0
  else if k = 1 then if d = 2 then 1 else if d = 3 then -1 else 0
  else if d = 4 then 1 else if d = 5 then -1 else 0

def displacement : List (Fin 6) → Fin 3 → ℤ
  | [], _ => 0
  | d :: ds, k => increment d k + displacement ds k

theorem displacement_append (ds es : List (Fin 6)) (k : Fin 3) :
    displacement (ds ++ es) k = displacement ds k + displacement es k := by
  induction ds with
  | nil => simp [displacement]
  | cons d ds ih => simp only [List.cons_append, displacement, ih]; omega

theorem updateCounts_coordinate (c : Counts) (d : Fin 6) (k : Fin 3) :
    coordinate (updateCounts c d) k = coordinate c k + increment d k := by
  have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl
  all_goals simp only [updateCounts, opposite]
  all_goals split <;> simp_all [coordinate, increment, Function.update] <;> omega

theorem runCounts_coordinate (c : Counts) (ds : List (Fin 6)) (k : Fin 3) :
    coordinate (runCounts c ds) k = coordinate c k + displacement ds k := by
  induction ds generalizing c with
  | nil => simp [runCounts, displacement]
  | cons d ds ih =>
    rw [runCounts, ih, updateCounts_coordinate]
    simp only [displacement]
    omega

theorem updateCounts_total_le (c : Counts) (d : Fin 6) :
    totalCounts (updateCounts c d) ≤ totalCounts c + 1 := by
  have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [updateCounts, opposite]
  all_goals split <;> simp_all [totalCounts, Function.update] <;> omega

theorem runCounts_total_le (c : Counts) (ds : List (Fin 6)) :
    totalCounts (runCounts c ds) ≤ totalCounts c + ds.length := by
  induction ds generalizing c with
  | nil => simp [runCounts]
  | cons d ds ih =>
    have h := ih (updateCounts c d)
    have hu := updateCounts_total_le c d
    simp only [runCounts, List.length_cons]
    omega

def Reduced (c : Counts) : Prop := ∀ d, c d = 0 ∨ c (opposite d) = 0

theorem updateCounts_reduced (c : Counts) (h : Reduced c) (d : Fin 6) :
    Reduced (updateCounts c d) := by
  intro e
  have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  have he : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 := by omega
  have h0 := h 0
  have h2 := h 2
  have h4 := h 4
  cases hc : c (opposite d) <;>
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [updateCounts, opposite, Function.update] <;> omega

theorem runCounts_reduced (c : Counts) (h : Reduced c) (ds : List (Fin 6)) :
    Reduced (runCounts c ds) := by
  induction ds generalizing c with
  | nil => exact h
  | cons d ds ih => exact ih _ (updateCounts_reduced c h d)

theorem totalCounts_eq_manhattan (c : Counts) (h : Reduced c) :
    totalCounts c = (coordinate c 0).natAbs + (coordinate c 1).natAbs +
      (coordinate c 2).natAbs := by
  have h0 := h 0
  have h2 := h 2
  have h4 := h 4
  simp only [opposite] at h0 h2 h4
  rcases h0 with h0 | h0 <;> rcases h2 with h2 | h2 <;> rcases h4 with h4 | h4
  all_goals simp [coordinate, totalCounts, h0, h2, h4, Nat.add_assoc]

theorem zero_reduced : Reduced (fun _ => 0) := fun _ => Or.inl rfl

theorem coordinate_zero (k : Fin 3) : coordinate (fun _ => 0) k = 0 := by
  match k with
  | 0 | 1 | 2 => rfl

theorem runCounts_zero_coordinate (ds : List (Fin 6)) (k : Fin 3) :
    coordinate (runCounts (fun _ => 0) ds) k = displacement ds k := by
  rw [runCounts_coordinate, coordinate_zero, zero_add]

theorem runCounts_zero_total_le (ds : List (Fin 6)) :
    totalCounts (runCounts (fun _ => 0) ds) ≤ ds.length := by
  simpa [totalCounts] using runCounts_total_le (fun _ => 0) ds

theorem runCounts_zero_manhattan (ds : List (Fin 6)) :
    totalCounts (runCounts (fun _ => 0) ds) = (displacement ds 0).natAbs +
      (displacement ds 1).natAbs + (displacement ds 2).natAbs := by
  rw [totalCounts_eq_manhattan _ (runCounts_reduced _ zero_reduced ds)]
  simp only [runCounts_zero_coordinate]

def stackContents {I : Type} (input : List I) (c : Counts) : ∀ k, List (Alphabet I k)
  | .input => input
  | .counter k => List.replicate (c k) ()

theorem update_input {I : Type} (input input' : List I) (c : Counts) :
    Function.update (stackContents input c) .input input' = stackContents input' c := by
  funext k
  cases k <;> simp [stackContents, Function.update_of_ne]

theorem update_counter {I : Type} (input : List I) (c : Counts) (d : Fin 6) (m : ℕ) :
    Function.update (stackContents input c) (.counter d) (List.replicate m ()) =
      stackContents input (Function.update c d m) := by
  funext k
  cases k with
  | input => simp [stackContents, Function.update_of_ne]
  | counter k =>
    by_cases hk : k = d
    · subst k; simp [stackContents]
    · simp [stackContents, Function.update_of_ne, hk]

def resetGoto {I : Type} : Stmt (Alphabet I) Phase (Option I × Bool) :=
  .load (fun _ => (none, false)) (.goto (fun _ => .scan))

def updateStmt {I : Type} (d : Fin 6) : Stmt (Alphabet I) Phase (Option I × Bool) :=
  .pop (.counter (opposite d)) (fun st x => (st.1, x.isSome))
    (.branch Prod.snd resetGoto
      (.push (.counter d) (fun _ => ()) resetGoto))

def dispatch {I : Type} (direction : I → Fin 6) : Stmt (Alphabet I) Phase (Option I × Bool) :=
  .branch (fun st => decide (st.1.map direction = some 0)) (updateStmt 0)
    (.branch (fun st => decide (st.1.map direction = some 1)) (updateStmt 1)
      (.branch (fun st => decide (st.1.map direction = some 2)) (updateStmt 2)
        (.branch (fun st => decide (st.1.map direction = some 3)) (updateStmt 3)
          (.branch (fun st => decide (st.1.map direction = some 4)) (updateStmt 4)
            (updateStmt 5)))))

def program {I : Type} (direction : I → Fin 6) : Phase → Stmt (Alphabet I) Phase (Option I × Bool)
  | .scan => .pop .input (fun _ x => (x, false))
      (.branch (fun st => st.1.isSome) (dispatch direction)
        (.load (fun _ => (none, false)) (.goto (fun _ => .finish))))
  | .finish => .halt

def cfg {I : Type} (phase : Phase) (reg : Option I × Bool) (input : List I) (c : Counts) :
    Cfg (Alphabet I) Phase (Option I × Bool) := ⟨some phase, reg, stackContents input c⟩

theorem updateStmt_stepAux {I : Type} (d : Fin 6) (reg : Option I × Bool)
    (input : List I) (c : Counts) :
    stepAux (updateStmt d) reg (stackContents input c) =
      cfg .scan (none, false) input (updateCounts c d) := by
  cases hc : c (opposite d) with
  | zero =>
    have hid : Function.update c (opposite d) 0 = c := by
      rw [← hc]
      exact Function.update_eq_self _ _
    have hpop : Function.update (stackContents input c) (.counter (opposite d)) [] =
        stackContents input c := by
      change Function.update (stackContents input c) (.counter (opposite d))
        (List.replicate 0 ()) = stackContents input c
      rw [update_counter, hid]
    have hpush : Function.update (stackContents input c) (.counter d)
        (() :: List.replicate (c d) ()) = stackContents input (Function.update c d (c d + 1)) :=
      update_counter input c d (c d + 1)
    simp [updateStmt, stepAux, stackContents, hc, hpop, hpush,
      updateCounts, resetGoto, cfg]
  | succ m =>
    simp [updateStmt, stepAux, stackContents, hc, update_counter, List.replicate_succ,
      updateCounts, resetGoto, cfg]

theorem dispatch_stepAux {I : Type} (direction : I → Fin 6) (a : I) (flag : Bool)
    (input : List I) (c : Counts) :
    stepAux (dispatch direction) (some a, flag) (stackContents input c) =
      cfg .scan (none, false) input (updateCounts c (direction a)) := by
  have hd : direction a = 0 ∨ direction a = 1 ∨ direction a = 2 ∨
      direction a = 3 ∨ direction a = 4 ∨ direction a = 5 := by omega
  rcases hd with hd | hd | hd | hd | hd | hd <;>
    simp [dispatch, stepAux, hd, updateStmt_stepAux]

theorem scan_step_cons {I : Type} (direction : I → Fin 6) (a : I)
    (reg : Option I × Bool) (input : List I) (c : Counts) :
    step (program direction) (cfg .scan reg (a :: input) c) =
      some (cfg .scan (none, false) input (updateCounts c (direction a))) := by
  simpa only [cfg, program, step, stepAux, stackContents, List.head?_cons,
    List.tail_cons, update_input, Option.isSome_some, cond_true] using
      congrArg some (dispatch_stepAux direction a false input c)

theorem scan_step_nil {I : Type} (direction : I → Fin 6) (reg : Option I × Bool) (c : Counts) :
    step (program direction) (cfg .scan reg [] c) =
      some (cfg .finish (none, false) [] c) := by
  simp [cfg, program, step, stepAux, stackContents, update_input]

/-- Each input letter is processed by exactly one actual TM2 step; one final
empty-input test enters the continuation. Both finite registers are cleared. -/
theorem scan_run {I : Type} (direction : I → Fin 6) (input : List I)
    (reg : Option I × Bool) (c : Counts) :
    (fun x : Option (Cfg (Alphabet I) Phase (Option I × Bool)) =>
      x.bind (step (program direction)))^[input.length + 1]
      (some (cfg .scan reg input c)) =
        some (cfg .finish (none, false) [] (runCounts c (input.map direction))) := by
  induction input generalizing reg c with
  | nil => simpa using scan_step_nil direction reg c
  | cons a input ih =>
    rw [List.length_cons, Nat.add_right_comm input.length 1 1, Function.iterate_succ_apply]
    simpa only [Option.bind_some, scan_step_cons, List.map_cons, runCounts] using
      ih (none, false) (updateCounts c (direction a))

def scanner (I : Type) [Fintype I] (direction : I → Fin 6) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .counter 0
  Γ := Alphabet I
  Λ := Phase
  main := .scan
  σ := Option I × Bool
  initialState := (none, false)
  Γk₀Fin := inferInstanceAs (Fintype I)
  m := program direction

end ProteinFolding.TM2WalkCounters

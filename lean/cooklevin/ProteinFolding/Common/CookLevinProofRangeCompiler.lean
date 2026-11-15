import ProteinFolding.Common.TM2ListMap
import Mathlib.Tactic.Linarith

/-! Actual unary index enumeration for the generic tableau compiler. A persistent
counter is copied and restored for each output record; every copy, separator,
counter increment and final output reversal is included in the runtime. -/

namespace ProteinFolding.SAT.CookLevinRangeCompiler

open Computability Turing ProteinFolding.TM2ListMap

inductive Stack where
  | input | counter | temp | accumulator | output
  deriving DecidableEq, Fintype

def alphabet : Stack → Type
  | .input => Bool
  | .counter | .temp => Unit
  | .accumulator | .output => Option Bool

inductive Label where
  | next | copy | restore | clear | reverse
  deriving DecidableEq, Fintype

def clean (l : Label) : TM2.Stmt alphabet Label (Option (Option Bool)) :=
  .load (fun _ => none) (.goto (fun _ => l))

def Program : Label → TM2.Stmt alphabet Label (Option (Option Bool))
  | .next => .pop .input (fun _ a => a.map some)
      (.branch Option.isSome (clean .copy) (clean .clear))
  | .copy => .pop .counter (fun _ a => if a.isSome then some none else none)
      (.branch Option.isSome
        (.push .temp (fun _ => ()) (.push .accumulator (fun _ => some true) (clean .copy)))
        (.push .accumulator (fun _ => none) (clean .restore)))
  | .restore => .pop .temp (fun _ a => if a.isSome then some none else none)
      (.branch Option.isSome (.push .counter (fun _ => ()) (clean .restore))
        (.push .counter (fun _ => ()) (clean .next)))
  | .clear => .pop .counter (fun _ a => if a.isSome then some none else none)
      (.branch Option.isSome (clean .clear) (clean .reverse))
  | .reverse => .pop .accumulator (fun _ a => a)
      (.branch Option.isSome
        (.push .output (fun s => s.getD none) (clean .reverse)) (.load (fun _ => none) .halt))

def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := alphabet
  Λ := Label
  main := .next
  σ := Option (Option Bool)
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := Program

def store (w : List Bool) (k t : ℕ) (a o : List (Option Bool)) :
    (s : Stack) → List (alphabet s)
  | .input => w | .counter => List.replicate k () | .temp => List.replicate t ()
  | .accumulator => a | .output => o

def config (l : Label) (w : List Bool) (k t : ℕ) (a o : List (Option Bool)) : machine.Cfg :=
  ⟨some l, none, store w k t a o⟩

def run (n : ℕ) (c : machine.Cfg) : Option machine.Cfg :=
  (fun q : Option machine.Cfg => q.bind machine.step)^[n] (some c)

theorem run_step {c e : machine.Cfg} (h : machine.step c = some e) (n : ℕ) :
    run (n + 1) c = run n e := by
  unfold run
  rw [Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add {c e : machine.Cfg} {n : ℕ} (h : run n c = some e) (m : ℕ) :
    run (n + m) c = run m e := by
  unfold run at *
  rw [Nat.add_comm n m, Function.iterate_add_apply, h]

theorem step_next (w : List Bool) (k : ℕ) (a : List (Option Bool)) :
    machine.step (config .next (true :: w) k 0 a []) =
      some (config .copy w k 0 a []) := by
  simp [machine, FinTM2.step, TM2.step, Program, clean, config, store,
    TM2.stepAux, Function.update]
  funext s; cases s <;> simp [store, Function.update]

theorem step_next_end (k : ℕ) (a : List (Option Bool)) :
    machine.step (config .next [] k 0 a []) = some (config .clear [] k 0 a []) := by
  simp [machine, FinTM2.step, TM2.step, Program, clean, config, store,
    TM2.stepAux, Function.update]

theorem step_copy (w : List Bool) (k t : ℕ) (a : List (Option Bool)) :
    machine.step (config .copy w (k + 1) t a []) =
      some (config .copy w k (t + 1) (some true :: a) []) := by
  simp [machine, FinTM2.step, TM2.step, Program, clean, config, store,
    TM2.stepAux, Function.update, List.replicate_succ]
  funext s; cases s <;> simp [store, Function.update, List.replicate_succ]

theorem step_copy_end (w : List Bool) (t : ℕ) (a : List (Option Bool)) :
    machine.step (config .copy w 0 t a []) = some (config .restore w 0 t (none :: a) []) := by
  simp [machine, FinTM2.step, TM2.step, Program, clean, config, store,
    TM2.stepAux, Function.update]
  funext s; cases s <;> simp [store, Function.update]

theorem step_restore (w : List Bool) (k t : ℕ) (a : List (Option Bool)) :
    machine.step (config .restore w k (t + 1) a []) =
      some (config .restore w (k + 1) t a []) := by
  simp [machine, FinTM2.step, TM2.step, Program, clean, config, store,
    TM2.stepAux, Function.update, List.replicate_succ]
  funext s; cases s <;> simp [store, Function.update, List.replicate_succ]

theorem step_restore_end (w : List Bool) (k : ℕ) (a : List (Option Bool)) :
    machine.step (config .restore w k 0 a []) = some (config .next w (k + 1) 0 a []) := by
  simp [machine, FinTM2.step, TM2.step, Program, clean, config, store,
    TM2.stepAux, Function.update]
  funext s; cases s <;> simp [store, Function.update, List.replicate_succ]

theorem step_clear (k : ℕ) (a : List (Option Bool)) :
    machine.step (config .clear [] (k + 1) 0 a []) = some (config .clear [] k 0 a []) := by
  simp [machine, FinTM2.step, TM2.step, Program, clean, config, store,
    TM2.stepAux, Function.update, List.replicate_succ]
  funext s; cases s <;> simp [store, Function.update]

theorem step_clear_end (a : List (Option Bool)) :
    machine.step (config .clear [] 0 0 a []) = some (config .reverse [] 0 0 a []) := by
  simp [machine, FinTM2.step, TM2.step, Program, clean, config, store,
    TM2.stepAux, Function.update]

theorem step_reverse (b : Option Bool) (a o : List (Option Bool)) :
    machine.step (config .reverse [] 0 0 (b :: a) o) = some (config .reverse [] 0 0 a (b :: o)) := by
  simp [machine, FinTM2.step, TM2.step, Program, clean, config, store,
    TM2.stepAux, Function.update]
  funext s; cases s <;> simp [store, Function.update]

theorem step_halt (o : List (Option Bool)) :
    machine.step (config .reverse [] 0 0 [] o) = some (haltList machine o) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, store, TM2.stepAux, haltList]
  funext s; cases s <;> rfl

theorem copy_run (w : List Bool) (k t : ℕ) (a : List (Option Bool)) :
    run (k + 1) (config .copy w k t a []) =
      some (config .restore w 0 (t + k) (none :: List.replicate k (some true) ++ a) []) := by
  induction k generalizing t a with
  | zero => simpa [run] using step_copy_end w t a
  | succ k ih =>
    rw [run_step (step_copy w k t a), ih]
    have ht : t + 1 + k = t + (k + 1) := by omega
    rw [ht]
    congr 2
    simp [List.replicate_succ', List.append_assoc]

theorem restore_run (w : List Bool) (k t : ℕ) (a : List (Option Bool)) :
    run (t + 1) (config .restore w k t a []) =
      some (config .next w (k + t + 1) 0 a []) := by
  induction t generalizing k with
  | zero => simpa [run] using step_restore_end w k a
  | succ t ih =>
    rw [run_step (step_restore w k t a), ih]
    congr 2
    omega

def field (k : ℕ) : List (Option Bool) := List.replicate k (some true) ++ [none]

theorem iteration_run (w : List Bool) (k : ℕ) (a : List (Option Bool)) :
    run (2 * k + 3) (config .next (true :: w) k 0 a []) =
      some (config .next w (k + 1) 0 ((field k).reverse ++ a) []) := by
  rw [show 2 * k + 3 = ((k + 1) + (k + 1)) + 1 by omega,
    run_step (step_next w k a), run_add (copy_run w k 0 a)]
  simp only [Nat.zero_add]
  rw [restore_run]
  simp [field]

def words : ℕ → ℕ → List (Option Bool)
  | _, 0 => []
  | k, n + 1 => field k ++ words (k + 1) n

def coreTime : ℕ → ℕ → ℕ
  | _, 0 => 0
  | k, n + 1 => 2 * k + 3 + coreTime (k + 1) n

theorem core_run (k n : ℕ) (a : List (Option Bool)) :
    run (coreTime k n) (config .next (unaryEncodeNat n) k 0 a []) =
      some (config .next [] (k + n) 0 ((words k n).reverse ++ a) []) := by
  induction n generalizing k a with
  | zero => rfl
  | succ n ih =>
    rw [coreTime, unaryEncodeNat, run_add (iteration_run (unaryEncodeNat n) k a), ih]
    have hk : k + 1 + n = k + (n + 1) := by omega
    simp only [hk, words, List.reverse_append, List.append_assoc]

theorem coreTime_bound (k n : ℕ) : coreTime k n ≤ 2 * n * k + 2 * n ^ 2 + 3 * n := by
  induction n generalizing k with
  | zero => simp [coreTime]
  | succ n ih =>
    have ht := ih (k + 1)
    simp only [coreTime]
    nlinarith

theorem words_length_bound (k n : ℕ) : (words k n).length ≤ n * (k + n + 1) := by
  induction n generalizing k with
  | zero => simp [words]
  | succ n ih =>
    have ht := ih (k + 1)
    simp only [words, field, List.length_append, List.length_replicate, List.length_singleton]
    nlinarith

theorem clear_run (k : ℕ) (a : List (Option Bool)) :
    run (k + 1) (config .clear [] k 0 a []) = some (config .reverse [] 0 0 a []) := by
  induction k with
  | zero => simpa [run] using step_clear_end a
  | succ k ih => rw [run_step (step_clear k a), ih]

theorem reverse_run (a o : List (Option Bool)) :
    run (a.length + 1) (config .reverse [] 0 0 a o) =
      some (haltList machine (a.reverse ++ o)) := by
  induction a generalizing o with
  | nil => simpa [run] using step_halt o
  | cons b a ih =>
    rw [List.length_cons, run_step (step_reverse b a o), ih]
    simp

theorem unary_replicate (n : ℕ) : unaryEncodeNat n = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, List.replicate_succ, ih]

theorem words_encode_range' (k n : ℕ) :
    words k n = encodeFields unaryFinEncodingNat (List.range' k n) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [words, field, List.range'_succ, encodeFields, unaryFinEncodingNat,
      unary_replicate, ih, List.append_assoc]

theorem words_encode_range (n : ℕ) :
    words 0 n = (listEncoding unaryFinEncodingNat).encode (List.range n) := by
  rw [words_encode_range', List.range_eq_range']
  rfl

def steps (n : ℕ) : ℕ := coreTime 0 n + n + (words 0 n).length + 3

theorem machine_init (n : ℕ) :
    initList machine (unaryEncodeNat n) = config .next (unaryEncodeNat n) 0 0 [] [] := by
  simp [initList, machine, config]
  congr 1
  funext s; cases s <;> rfl

theorem canonical_run (n : ℕ) :
    run (steps n) (initList machine (unaryEncodeNat n)) =
      some (haltList machine ((listEncoding unaryFinEncodingNat).encode (List.range n))) := by
  rw [machine_init]
  unfold steps
  rw [show coreTime 0 n + n + (words 0 n).length + 3 =
      coreTime 0 n + (((n + 1) + ((words 0 n).length + 1)) + 1) by omega,
    run_add (core_run 0 n [])]
  simp only [Nat.zero_add, List.append_nil]
  rw [run_step (step_next_end n _), run_add (clear_run n _)]
  have hr := reverse_run (words 0 n).reverse []
  simpa only [List.length_reverse, List.reverse_reverse, List.append_nil, words_encode_range] using hr

theorem steps_bound (n : ℕ) : steps n ≤ 4 * n ^ 2 + 8 * n + 5 := by
  have hc := coreTime_bound 0 n
  have hw := words_length_bound 0 n
  unfold steps
  nlinarith

noncomputable def computable :
    TM2ComputableInPolyTime unaryFinEncodingNat (listEncoding unaryFinEncodingNat) List.range where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X ^ 2 + 8 * Polynomial.X + 5
  outputsFun n :=
    { steps := steps n
      evals_in_steps := by
        change run _ (initList machine (List.map id (unaryEncodeNat n))) =
          some (haltList machine (List.map id ((listEncoding unaryFinEncodingNat).encode (List.range n))))
        rw [List.map_id, List.map_id]
        exact canonical_run n
      steps_le_m := by simpa [unaryFinEncodingNat, unary_replicate] using steps_bound n }

example : (run 3 (initList machine [])).map (fun c => (c.l, c.stk .output)) =
    some (none, []) := by
  simp [run, Function.iterate_succ_apply, initList, machine, Program, clean,
    FinTM2.step, TM2.step, TM2.stepAux, Function.update]

example : (run 8 (initList machine [true])).map (fun c => (c.l, c.stk .counter, c.stk .output)) =
    some (none, [], [none]) := by
  simp [run, Function.iterate_succ_apply, initList, machine, Program, clean,
    FinTM2.step, TM2.step, TM2.stepAux, Function.update]

example : (run 27 (initList machine [true, true, true])).map
    (fun c => (c.l, c.stk .input, c.stk .counter, c.stk .temp, c.stk .accumulator, c.stk .output)) =
    some (none, [], [], [], [], [none, some true, none, some true, some true, none]) := by
  simp [run, Function.iterate_succ_apply, initList, machine, Program, clean,
    FinTM2.step, TM2.step, TM2.stepAux, Function.update]

end ProteinFolding.SAT.CookLevinRangeCompiler

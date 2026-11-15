import ProteinFolding.Square.TM2LengthVerifier
import ProteinFolding.Square.EncodingUtilities

/-!
Finite-alphabet word equality for comparing serialized lattice sites. This is a
pair-comparison primitive, not the iteration over all pairs of residues.
Both words are read from the existing tagged pair encoding. Two finite-alphabet
work stacks restore the first word's order before symbolwise comparison.
-/

namespace ProteinFolding.Square

open Computability Turing

inductive EqualityStack where
  | input | first | second | output
  deriving DecidableEq, Fintype

def equalityAlphabet (A : Type) : EqualityStack → Type
  | .input => PairSymbol A A
  | .first | .second => A
  | .output => Bool

instance equalityAlphabetFintype (A : Type) [Fintype A] (k : EqualityStack) :
    Fintype (equalityAlphabet A k) := by
  cases k <;> dsimp [equalityAlphabet] <;> infer_instance

inductive EqualityLabel where
  | scan | reverse | compare | drain
  deriving DecidableEq, Fintype

abbrev EqualityState (A : Type) := Option (PairSymbol A A) × Bool

def equalityInitialState (A : Type) : EqualityState A := (none, true)

def equalityProgram (A : Type) [DecidableEq A] [Inhabited A] :
    EqualityLabel → TM2.Stmt (equalityAlphabet A) EqualityLabel (EqualityState A)
  | .scan =>
    .pop .input (fun s a => (a, s.2))
      (.branch (fun s => match s.1 with | some (.left _) => true | _ => false)
        (.push .first (fun s => match s.1 with | some (.left a) => a | _ => (default : A))
          (.load (fun s => (none, s.2)) (.goto (fun _ => .scan))))
        (.load (fun s => (none, s.2)) (.goto (fun _ => .reverse))))
  | .reverse =>
    .pop .first (fun s a => (a.map PairSymbol.left, s.2))
      (.branch (fun s => s.1.isSome)
        (.push .second (fun s => match s.1 with | some (.left a) => a | _ => (default : A))
          (.load (fun s => (none, s.2)) (.goto (fun _ => .reverse))))
        (.goto (fun _ => .compare)))
  | .compare =>
    .pop .input (fun s a => (a, s.2))
      (.branch (fun s => s.1.isSome)
        (.pop .second (fun s a => (none, s.2 && decide (s.1 = a.map PairSymbol.right)))
          (.goto (fun _ => .compare)))
        (.peek .second (fun s a => (none, s.2 && a.isNone)) (.goto (fun _ => .drain))))
  | .drain =>
    .pop .second (fun s a => (a.map PairSymbol.right, s.2))
      (.branch (fun s => s.1.isSome)
        (.load (fun s => (none, s.2)) (.goto (fun _ => .drain)))
        (.push .output Prod.snd (.load (fun _ => equalityInitialState A) .halt)))

def wordEqualityMachine (A : Type) [Fintype A] [DecidableEq A] [Inhabited A] : FinTM2 where
  K := EqualityStack
  k₀ := .input
  k₁ := .output
  Γ := equalityAlphabet A
  Λ := EqualityLabel
  main := .scan
  σ := EqualityState A
  initialState := equalityInitialState A
  Γk₀Fin := inferInstanceAs (Fintype (PairSymbol A A))
  m := equalityProgram A

def equalityStacks {A : Type} (w : List (PairSymbol A A)) (xs ys : List A) (o : List Bool) :
    (k : EqualityStack) → List (equalityAlphabet A k)
  | .input => w
  | .first => xs
  | .second => ys
  | .output => o

section WordEquality

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]

def equalityConfig (l : EqualityLabel) (w : List (PairSymbol A A)) (xs ys : List A) (b : Bool) :
    (wordEqualityMachine A).Cfg :=
  ⟨some l, (none, b), equalityStacks w xs ys []⟩

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem equalityStacks_update_input (w w' : List (PairSymbol A A)) (xs ys : List A) (o : List Bool) :
    Function.update (equalityStacks w xs ys o) .input w' = equalityStacks w' xs ys o := by
  funext k
  cases k <;> simp [equalityStacks]

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem equalityStacks_update_first (w : List (PairSymbol A A)) (xs xs' ys : List A) (o : List Bool) :
    Function.update (equalityStacks w xs ys o) .first xs' = equalityStacks w xs' ys o := by
  funext k
  cases k <;> simp [equalityStacks]

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem equalityStacks_update_second (w : List (PairSymbol A A)) (xs ys ys' : List A) (o : List Bool) :
    Function.update (equalityStacks w xs ys o) .second ys' = equalityStacks w xs ys' o := by
  funext k
  cases k <;> simp [equalityStacks]

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem equalityStacks_update_output (w : List (PairSymbol A A)) (xs ys : List A) (o o' : List Bool) :
    Function.update (equalityStacks w xs ys o) .output o' = equalityStacks w xs ys o' := by
  funext k
  cases k <;> simp [equalityStacks]

def equalityRun (t : ℕ) (c : (wordEqualityMachine A).Cfg) : Option (wordEqualityMachine A).Cfg :=
  (fun q : Option (wordEqualityMachine A).Cfg => q.bind (wordEqualityMachine A).step)^[t] (some c)

theorem equalityRun_zero (c : (wordEqualityMachine A).Cfg) : equalityRun 0 c = some c := rfl

theorem equalityRun_step {c c' : (wordEqualityMachine A).Cfg}
    (h : (wordEqualityMachine A).step c = some c') (t : ℕ) :
    equalityRun (t + 1) c = equalityRun t c' := by
  unfold equalityRun
  rw [Function.iterate_succ_apply, Option.bind_some, h]

theorem equalityRun_add {c c' : (wordEqualityMachine A).Cfg} {t : ℕ}
    (h : equalityRun t c = some c') (u : ℕ) : equalityRun (t + u) c = equalityRun u c' := by
  unfold equalityRun at *
  rw [Nat.add_comm t u, Function.iterate_add_apply, h]

theorem equality_step_scan (a : A) (w : List (PairSymbol A A)) (xs ys : List A) :
    (wordEqualityMachine A).step (equalityConfig .scan (.left a :: w) xs ys true) =
      some (equalityConfig .scan w (a :: xs) ys true) := by
  simp [wordEqualityMachine, FinTM2.step, TM2.step, equalityProgram, equalityConfig,
    TM2.stepAux, Function.update, equalityStacks, equalityStacks_update_input, equalityStacks_update_first]

theorem equality_step_separator (w : List (PairSymbol A A)) (xs ys : List A) :
    (wordEqualityMachine A).step (equalityConfig .scan (.sep :: w) xs ys true) =
      some (equalityConfig .reverse w xs ys true) := by
  simp [wordEqualityMachine, FinTM2.step, TM2.step, equalityProgram, equalityConfig,
    TM2.stepAux, Function.update, equalityStacks, equalityStacks_update_input]

theorem equality_step_reverse (a : A) (w : List (PairSymbol A A)) (xs ys : List A) :
    (wordEqualityMachine A).step (equalityConfig .reverse w (a :: xs) ys true) =
      some (equalityConfig .reverse w xs (a :: ys) true) := by
  simp [wordEqualityMachine, FinTM2.step, TM2.step, equalityProgram, equalityConfig,
    TM2.stepAux, Function.update, equalityStacks, equalityStacks_update_first, equalityStacks_update_second]

theorem equality_step_reverse_end (w : List (PairSymbol A A)) (ys : List A) :
    (wordEqualityMachine A).step (equalityConfig .reverse w [] ys true) =
      some (equalityConfig .compare w [] ys true) := by
  simp [wordEqualityMachine, FinTM2.step, TM2.step, equalityProgram, equalityConfig,
    TM2.stepAux, Function.update, equalityStacks, equalityStacks_update_first]

theorem equality_step_compare_empty (a : A) (w : List (PairSymbol A A)) (b : Bool) :
    (wordEqualityMachine A).step (equalityConfig .compare (.right a :: w) [] [] b) =
      some (equalityConfig .compare w [] [] false) := by
  simp [wordEqualityMachine, FinTM2.step, TM2.step, equalityProgram, equalityConfig,
    TM2.stepAux, Function.update, equalityStacks, equalityStacks_update_input, equalityStacks_update_second]

theorem equality_step_compare_cons (a x : A) (w : List (PairSymbol A A)) (ys : List A) (b : Bool) :
    (wordEqualityMachine A).step (equalityConfig .compare (.right a :: w) [] (x :: ys) b) =
      some (equalityConfig .compare w [] ys (b && decide (a = x))) := by
  by_cases h : a = x <;>
    simp [wordEqualityMachine, FinTM2.step, TM2.step, equalityProgram, equalityConfig,
      TM2.stepAux, Function.update, equalityStacks, equalityStacks_update_input,
      equalityStacks_update_second, h]
  all_goals exact fun _ he => h (PairSymbol.right.inj he)

theorem equality_step_compare_end (ys : List A) (b : Bool) :
    (wordEqualityMachine A).step (equalityConfig .compare [] [] ys b) =
      some (equalityConfig .drain [] [] ys (b && decide (ys = []))) := by
  cases ys <;>
    simp [wordEqualityMachine, FinTM2.step, TM2.step, equalityProgram, equalityConfig,
      TM2.stepAux, Function.update, equalityStacks, equalityStacks_update_input]

theorem equality_step_drain (x : A) (ys : List A) (b : Bool) :
    (wordEqualityMachine A).step (equalityConfig .drain [] [] (x :: ys) b) =
      some (equalityConfig .drain [] [] ys b) := by
  simp [wordEqualityMachine, FinTM2.step, TM2.step, equalityProgram, equalityConfig,
    TM2.stepAux, Function.update, equalityStacks, equalityStacks_update_second]

theorem equality_step_halt (b : Bool) :
    (wordEqualityMachine A).step (equalityConfig .drain [] [] [] b) =
      some (haltList (wordEqualityMachine A) [b]) := by
  simp [wordEqualityMachine, FinTM2.step, TM2.step, equalityProgram, equalityConfig,
    TM2.stepAux, Function.update, equalityStacks, equalityStacks_update_second, equalityStacks_update_output,
    equalityInitialState, haltList]
  funext k
  cases k <;> rfl

theorem equality_drain_run (ys : List A) (b : Bool) :
    equalityRun (ys.length + 1) (equalityConfig .drain [] [] ys b) =
      some (haltList (wordEqualityMachine A) [b]) := by
  induction ys with
  | nil => rw [List.length_nil, equalityRun_step (equality_step_halt b), equalityRun_zero]
  | cons x ys ih => rw [List.length_cons, equalityRun_step (equality_step_drain x ys b), ih]

theorem equality_compare_run (as bs : List A) (b : Bool) :
    equalityRun (as.length + 2 + (bs.length - as.length))
      (equalityConfig .compare (as.map PairSymbol.right) [] bs b) =
      some (haltList (wordEqualityMachine A) [b && decide (as = bs)]) := by
  induction as generalizing bs b with
  | nil =>
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, eq_comm] using
      (equalityRun_step (equality_step_compare_end bs b) (bs.length + 1)).trans
        (equality_drain_run bs (b && decide (bs = [])))
  | cons a as ih =>
    cases bs with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_sub, Nat.add_zero, List.map_cons]
      rw [show as.length + 1 + 2 = (as.length + 2) + 1 by omega,
        equalityRun_step (equality_step_compare_empty a _ b)]
      simpa using ih [] false
    | cons x bs =>
      have ht : (a :: as).length + 2 + ((x :: bs).length - (a :: as).length) =
          (as.length + 2 + (bs.length - as.length)) + 1 := by simp; omega
      rw [ht, List.map_cons, equalityRun_step (equality_step_compare_cons a x _ bs b), ih]
      simp [List.cons.injEq, Bool.and_assoc]

theorem equality_scan_run (as : List A) (w : List (PairSymbol A A)) (xs ys : List A) :
    equalityRun as.length (equalityConfig .scan (as.map PairSymbol.left ++ w) xs ys true) =
      some (equalityConfig .scan w (as.reverse ++ xs) ys true) := by
  induction as generalizing xs with
  | nil => simp [equalityRun_zero]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [equalityRun_step (equality_step_scan a _ xs ys), ih]
    simp

theorem equality_reverse_run (xs : List A) (w : List (PairSymbol A A)) (ys : List A) :
    equalityRun (xs.length + 1) (equalityConfig .reverse w xs ys true) =
      some (equalityConfig .compare w [] (xs.reverse ++ ys) true) := by
  induction xs generalizing ys with
  | nil => rw [List.length_nil, equalityRun_step (equality_step_reverse_end w ys), equalityRun_zero]; simp
  | cons x xs ih =>
    rw [List.length_cons, equalityRun_step (equality_step_reverse x w xs ys), ih]
    simp

theorem equality_init (w : List (PairSymbol A A)) :
    initList (wordEqualityMachine A) w = equalityConfig .scan w [] [] true := by
  simp [initList, wordEqualityMachine, equalityConfig, equalityInitialState]
  congr 1
  funext k
  cases k <;> rfl

theorem wordEquality_canonical_run (as bs : List A) :
    equalityRun (2 * as.length + bs.length + 4 + (as.length - bs.length))
      (initList (wordEqualityMachine A)
        ((pairEncoding (wordEncoding A) (wordEncoding A)).encode (as, bs))) =
      some (haltList (wordEqualityMachine A) [decide (bs = as)]) := by
  rw [equality_init]
  change equalityRun _ (equalityConfig .scan
    (as.map (PairSymbol.left (B := A)) ++ PairSymbol.sep :: bs.map (PairSymbol.right (A := A))) [] [] true) = _
  rw [show 2 * as.length + bs.length + 4 + (as.length - bs.length) = as.length +
      ((as.length + 1 + (bs.length + 2 + (as.length - bs.length))) + 1) by omega]
  rw [equalityRun_add (equality_scan_run as _ [] [])]
  simp only [List.append_nil]
  rw [equalityRun_step (equality_step_separator _ _ [])]
  have hr := equality_reverse_run as.reverse (bs.map (PairSymbol.right (A := A))) []
  simp only [List.length_reverse] at hr
  rw [equalityRun_add hr]
  simp only [List.reverse_reverse, List.append_nil]
  exact equality_compare_run bs as true

def wordEqualityVerifier (input : List A × List A) : Bool := decide (input.2 = input.1)

omit [Fintype A] [Inhabited A] in
theorem wordEqualityVerifier_spec (input : List A × List A) :
    wordEqualityVerifier input = true ↔ input.1 = input.2 := by
  simp [wordEqualityVerifier, eq_comm]

noncomputable def wordEqualityComputable :
    TM2ComputableInPolyTime (pairEncoding (wordEncoding A) (wordEncoding A))
      finEncodingBoolBool wordEqualityVerifier where
  tm := wordEqualityMachine A
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 1
  outputsFun input :=
    { steps := 2 * input.1.length + input.2.length + 4 + (input.1.length - input.2.length)
      evals_in_steps := by
        change equalityRun _
          (initList (wordEqualityMachine A)
            (List.map id ((pairEncoding (wordEncoding A) (wordEncoding A)).encode input))) =
          some (haltList (wordEqualityMachine A) [wordEqualityVerifier input])
        rw [List.map_id]
        exact wordEquality_canonical_run input.1 input.2
      steps_le_m := by
        simp [pairEncoding, wordEncoding]
        omega }

theorem wordEquality_polyTimeDecidable :
    PolyTimeDecidable (pairEncoding (wordEncoding A) (wordEncoding A))
      (fun input : List A × List A => input.1 = input.2) :=
  ⟨wordEqualityVerifier, ⟨wordEqualityComputable⟩, wordEqualityVerifier_spec⟩

end WordEquality

namespace RecordCollision

inductive Stack where
  | input | first | saved | work | output
  deriving DecidableEq, Fintype

def Alphabet (A : Type) : Stack → Type
  | .input | .work => Option A
  | .first | .saved => A
  | .output => Bool

instance alphabetFintype (A : Type) [Fintype A] (k : Stack) : Fintype (Alphabet A k) := by
  cases k <;> dsimp [Alphabet] <;> infer_instance

inductive Label where
  | outer | flipFirst | beginRow | inner | restore | clearSaved | rewind
  deriving DecidableEq, Fintype

structure State (A : Type) where
  token : Option (Option A)
  held : Option A
  good : Bool
  same : Bool
  deriving Fintype

def initialState (A : Type) : State A := ⟨none, none, true, false⟩

def clean {A : Type} (s : State A) : State A := ⟨none, none, s.good, s.same⟩

def Program (A : Type) [DecidableEq A] [Inhabited A] :
    Label → TM2.Stmt (Alphabet A) Label (State A)
  | .outer =>
    .pop .input (fun s a => {s with token := a})
      (.branch (fun s => s.token.isSome)
        (.branch (fun s => (s.token.getD none).isSome)
          (.push .first (fun s => (s.token.getD none).getD default)
            (.load clean (.goto (fun _ => .outer))))
          (.load clean (.goto (fun _ => .flipFirst))))
        (.push .output State.good (.load (fun _ => initialState A) .halt)))
  | .flipFirst =>
    .pop .first (fun s a => {s with held := a})
      (.branch (fun s => s.held.isSome)
        (.push .saved (fun s => s.held.getD default) (.load clean (.goto (fun _ => .flipFirst))))
        (.load clean (.goto (fun _ => .beginRow))))
  | .beginRow =>
    .peek .input (fun s a => {s with token := a})
      (.branch (fun s => s.token.isSome)
        (.load (fun s => {clean s with same := true}) (.goto (fun _ => .inner)))
        (.load clean (.goto (fun _ => .clearSaved))))
  | .inner =>
    .pop .input (fun s a => {s with token := a})
      (.branch (fun s => (s.token.getD none).isSome)
        (.push .work (fun s => s.token.getD none)
          (.pop .saved (fun s a => {s with held := a, same := s.same && decide (s.token = some a)})
            (.branch (fun s => s.held.isSome)
              (.push .first (fun s => s.held.getD default) (.load clean (.goto (fun _ => .inner))))
              (.load clean (.goto (fun _ => .inner))))))
        (.push .work (fun _ => none)
          (.peek .saved (fun s a => {s with good := s.good && !(s.same && a.isNone), same := false})
            (.load clean (.goto (fun _ => .restore))))))
  | .restore =>
    .pop .first (fun s a => {s with held := a})
      (.branch (fun s => s.held.isSome)
        (.push .saved (fun s => s.held.getD default) (.load clean (.goto (fun _ => .restore))))
        (.load clean (.goto (fun _ => .beginRow))))
  | .clearSaved =>
    .pop .saved (fun s a => {s with held := a})
      (.branch (fun s => s.held.isSome)
        (.load clean (.goto (fun _ => .clearSaved)))
        (.load clean (.goto (fun _ => .rewind))))
  | .rewind =>
    .pop .work (fun s a => {s with token := a})
      (.branch (fun s => s.token.isSome)
        (.push .input (fun s => s.token.getD none) (.load clean (.goto (fun _ => .rewind))))
        (.load clean (.goto (fun _ => .outer))))

def machine (A : Type) [Fintype A] [DecidableEq A] [Inhabited A] : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A
  Λ := Label
  main := .outer
  σ := State A
  initialState := initialState A
  Γk₀Fin := inferInstanceAs (Fintype (Option A))
  m := Program A

def recordStacks {A : Type} (w : List (Option A)) (xs ys : List A) (work : List (Option A)) (o : List Bool) :
    (k : Stack) → List (Alphabet A k)
  | .input => w | .first => xs | .saved => ys | .work => work | .output => o

section

variable {A : Type}

@[simp]
theorem recordStacks_update_input (w w' : List (Option A)) (xs ys : List A)
    (work : List (Option A)) (o : List Bool) :
    Function.update (recordStacks w xs ys work o) .input w' = recordStacks w' xs ys work o := by
  funext k; cases k <;> simp [recordStacks]

@[simp]
theorem recordStacks_update_first (w : List (Option A)) (xs xs' ys : List A)
    (work : List (Option A)) (o : List Bool) :
    Function.update (recordStacks w xs ys work o) .first xs' = recordStacks w xs' ys work o := by
  funext k; cases k <;> simp [recordStacks]

@[simp]
theorem recordStacks_update_saved (w : List (Option A)) (xs ys ys' : List A)
    (work : List (Option A)) (o : List Bool) :
    Function.update (recordStacks w xs ys work o) .saved ys' = recordStacks w xs ys' work o := by
  funext k; cases k <;> simp [recordStacks]

@[simp]
theorem recordStacks_update_work (w : List (Option A)) (xs ys : List A)
    (work work' : List (Option A)) (o : List Bool) :
    Function.update (recordStacks w xs ys work o) .work work' = recordStacks w xs ys work' o := by
  funext k; cases k <;> simp [recordStacks]

@[simp]
theorem recordStacks_update_output (w : List (Option A)) (xs ys : List A)
    (work : List (Option A)) (o o' : List Bool) :
    Function.update (recordStacks w xs ys work o) .output o' = recordStacks w xs ys work o' := by
  funext k; cases k <;> simp [recordStacks]

variable [Fintype A] [DecidableEq A] [Inhabited A]

def config (l : Label) (w : List (Option A)) (xs ys : List A) (work : List (Option A))
    (good same : Bool) : (machine A).Cfg :=
  ⟨some l, ⟨none, none, good, same⟩, recordStacks w xs ys work []⟩

def run (t : ℕ) (c : (machine A).Cfg) : Option (machine A).Cfg :=
  (fun q : Option (machine A).Cfg => q.bind (machine A).step)^[t] (some c)

theorem run_zero (c : (machine A).Cfg) : run 0 c = some c := rfl

theorem run_step {c c' : (machine A).Cfg} (h : (machine A).step c = some c') (t : ℕ) :
    run (t + 1) c = run t c' := by
  unfold run
  rw [Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add {c c' : (machine A).Cfg} {t : ℕ} (h : run t c = some c') (u : ℕ) :
    run (t + u) c = run u c' := by
  unfold run at *
  rw [Nat.add_comm t u, Function.iterate_add_apply, h]

theorem step_outer_symbol (a : A) (w : List (Option A)) (xs ys : List A) (work : List (Option A))
    (g s : Bool) :
    (machine A).step (config .outer (some a :: w) xs ys work g s) =
      some (config .outer w (a :: xs) ys work g s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, Function.update]

theorem step_outer_end (w : List (Option A)) (xs ys : List A) (work : List (Option A)) (g s : Bool) :
    (machine A).step (config .outer (none :: w) xs ys work g s) =
      some (config .flipFirst w xs ys work g s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, Function.update]

theorem step_flip_symbol (a : A) (w : List (Option A)) (xs ys : List A) (work : List (Option A))
    (g s : Bool) :
    (machine A).step (config .flipFirst w (a :: xs) ys work g s) =
      some (config .flipFirst w xs (a :: ys) work g s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, Function.update]

theorem step_flip_end (w : List (Option A)) (ys : List A) (work : List (Option A)) (g s : Bool) :
    (machine A).step (config .flipFirst w [] ys work g s) =
      some (config .beginRow w [] ys work g s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, Function.update]

theorem step_begin_nonempty (a : Option A) (w : List (Option A)) (ys : List A)
    (work : List (Option A)) (g s : Bool) :
    (machine A).step (config .beginRow (a :: w) [] ys work g s) =
      some (config .inner (a :: w) [] ys work g true) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_begin_empty (ys : List A) (work : List (Option A)) (g s : Bool) :
    (machine A).step (config .beginRow [] [] ys work g s) =
      some (config .clearSaved [] [] ys work g s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_inner_symbol_empty (a : A) (w : List (Option A)) (xs : List A)
    (work : List (Option A)) (g s : Bool) :
    (machine A).step (config .inner (some a :: w) xs [] work g s) =
      some (config .inner w xs [] (some a :: work) g false) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, Function.update]

theorem step_inner_symbol_cons (a y : A) (w : List (Option A)) (xs ys : List A)
    (work : List (Option A)) (g s : Bool) :
    (machine A).step (config .inner (some a :: w) xs (y :: ys) work g s) =
      some (config .inner w (y :: xs) ys (some a :: work) g (s && decide (a = y))) := by
  by_cases h : a = y <;>
    simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks,
      TM2.stepAux, Function.update, h]
  all_goals exact fun _ he => h (Option.some.inj he)

theorem step_inner_end (w : List (Option A)) (xs ys : List A) (work : List (Option A)) (g s : Bool) :
    (machine A).step (config .inner (none :: w) xs ys work g s) =
      some (config .restore w xs ys (none :: work) (g && !(s && decide (ys = []))) false) := by
  cases ys <;>
    simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, Function.update]

theorem step_restore_symbol (a : A) (w : List (Option A)) (xs ys : List A)
    (work : List (Option A)) (g s : Bool) :
    (machine A).step (config .restore w (a :: xs) ys work g s) =
      some (config .restore w xs (a :: ys) work g s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, Function.update]

theorem step_restore_end (w : List (Option A)) (ys : List A) (work : List (Option A)) (g s : Bool) :
    (machine A).step (config .restore w [] ys work g s) =
      some (config .beginRow w [] ys work g s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, Function.update]

theorem step_clear_symbol (a : A) (ys : List A) (work : List (Option A)) (g s : Bool) :
    (machine A).step (config .clearSaved [] [] (a :: ys) work g s) =
      some (config .clearSaved [] [] ys work g s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_clear_end (work : List (Option A)) (g s : Bool) :
    (machine A).step (config .clearSaved [] [] [] work g s) =
      some (config .rewind [] [] [] work g s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_rewind_symbol (a : Option A) (w work : List (Option A)) (g s : Bool) :
    (machine A).step (config .rewind w [] [] (a :: work) g s) =
      some (config .rewind (a :: w) [] [] work g s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, Function.update]

theorem step_rewind_end (w : List (Option A)) (g s : Bool) :
    (machine A).step (config .rewind w [] [] [] g s) = some (config .outer w [] [] [] g s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, Function.update]

theorem step_halt (g s : Bool) :
    (machine A).step (config .outer [] [] [] [] g s) = some (haltList (machine A) [g]) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux,
    Function.update, initialState, haltList]
  funext k
  cases k <;> rfl

def row (xs : List A) : List (Option A) := xs.map some ++ [none]

def stream : List (List A) → List (Option A)
  | [] => []
  | xs :: xss => row xs ++ stream xss

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem row_length (xs : List A) : (row xs).length = xs.length + 1 := by simp [row]

omit [DecidableEq A] [Inhabited A] in
theorem stream_encode (xss : List (List A)) :
    stream xss = (listEncoding (wordEncoding A)).encode xss := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => simp [stream, row, listEncoding, encodeFields, wordEncoding, ih]

theorem outer_read_run (xs : List A) (w : List (Option A)) (first saved : List A)
    (work : List (Option A)) (g s : Bool) :
    run (xs.length + 1) (config .outer (row xs ++ w) first saved work g s) =
      some (config .flipFirst w (xs.reverse ++ first) saved work g s) := by
  induction xs generalizing first with
  | nil => simp [row, run_step (step_outer_end w first saved work g s), run_zero]
  | cons a xs ih =>
    simp only [row, List.map_cons, List.cons_append, List.length_cons]
    rw [run_step (step_outer_symbol a _ first saved work g s)]
    simpa [row] using ih (a :: first)

theorem flip_run (first saved : List A) (w : List (Option A)) (work : List (Option A)) (g s : Bool) :
    run (first.length + 1) (config .flipFirst w first saved work g s) =
      some (config .beginRow w [] (first.reverse ++ saved) work g s) := by
  induction first generalizing saved with
  | nil => rw [List.length_nil, run_step (step_flip_end w saved work g s), run_zero]; simp
  | cons a first ih =>
    rw [List.length_cons, run_step (step_flip_symbol a w first saved work g s), ih]
    simp

theorem restore_run (first saved : List A) (w : List (Option A)) (work : List (Option A)) (g s : Bool) :
    run (first.length + 1) (config .restore w first saved work g s) =
      some (config .beginRow w [] (first.reverse ++ saved) work g s) := by
  induction first generalizing saved with
  | nil => rw [List.length_nil, run_step (step_restore_end w saved work g s), run_zero]; simp
  | cons a first ih =>
    rw [List.length_cons, run_step (step_restore_symbol a w first saved work g s), ih]
    simp

theorem inner_run (ys xs first : List A) (w : List (Option A)) (work : List (Option A)) (g s : Bool) :
    run (ys.length + 1) (config .inner (row ys ++ w) first xs work g s) =
      some (config .restore w ((xs.take ys.length).reverse ++ first) (xs.drop ys.length)
        ((row ys).reverse ++ work) (g && !(s && decide (ys = xs))) false) := by
  induction ys generalizing xs first work s with
  | nil =>
    simpa [row, eq_comm] using
      (run_step (step_inner_end w first xs work g s) 0).trans (run_zero _)
  | cons a ys ih =>
    cases xs with
    | nil =>
      simp only [row, List.map_cons, List.cons_append, List.length_cons]
      rw [run_step (step_inner_symbol_empty a _ first work g s)]
      simpa [row] using ih [] first (some a :: work) false
    | cons x xs =>
      simp only [row, List.map_cons, List.cons_append, List.length_cons]
      rw [run_step (step_inner_symbol_cons a x _ first xs work g s)]
      simpa [row, List.cons.injEq, Bool.and_assoc] using
        ih xs (x :: first) (some a :: work) (s && decide (a = x))

def pairTime (xs : List A) : List (List A) → ℕ
  | [] => 1
  | ys :: yss => ys.length + min xs.length ys.length + 3 + pairTime xs yss

theorem compare_records_run (xs : List A) (yss : List (List A))
    (work : List (Option A)) (g : Bool) :
    run (pairTime xs yss) (config .beginRow (stream yss) [] xs work g false) =
      some (config .clearSaved [] [] xs ((stream yss).reverse ++ work)
        (g && decide (xs ∉ yss)) false) := by
  induction yss generalizing work g with
  | nil =>
    simpa [pairTime, stream] using
      (run_step (step_begin_empty xs work g false) 0).trans (run_zero _)
  | cons ys yss ih =>
    have hr : row ys ++ stream yss ≠ [] := by simp [row]
    have hs : ∃ a w, row ys ++ stream yss = a :: w := List.exists_cons_of_ne_nil hr
    obtain ⟨a, w, hw⟩ := hs
    have hbegin := step_begin_nonempty a w xs work g false
    rw [← hw] at hbegin
    rw [show pairTime xs (ys :: yss) =
      ((ys.length + 1) + (((xs.take ys.length).reverse).length + 1 + pairTime xs yss)) + 1 by
        simp [pairTime]; omega]
    change run _ (config .beginRow (row ys ++ stream yss) [] xs work g false) = _
    rw [run_step hbegin]
    rw [run_add (inner_run ys xs [] (stream yss) work g true)]
    simp only [List.append_nil, Bool.true_and]
    rw [run_add (restore_run _ _ _ _ _ false)]
    simp only [List.reverse_reverse, List.take_append_drop]
    rw [ih]
    simp [stream, List.mem_cons, Bool.and_assoc, eq_comm, List.append_assoc]

theorem clear_run (xs : List A) (work : List (Option A)) (g s : Bool) :
    run (xs.length + 1) (config .clearSaved [] [] xs work g s) =
      some (config .rewind [] [] [] work g s) := by
  induction xs with
  | nil => rw [List.length_nil, run_step (step_clear_end work g s), run_zero]
  | cons x xs ih => rw [List.length_cons, run_step (step_clear_symbol x xs work g s), ih]

theorem rewind_run (work w : List (Option A)) (g s : Bool) :
    run (work.length + 1) (config .rewind w [] [] work g s) =
      some (config .outer (work.reverse ++ w) [] [] [] g s) := by
  induction work generalizing w with
  | nil => rw [List.length_nil, run_step (step_rewind_end w g s), run_zero]; simp
  | cons a work ih =>
    rw [List.length_cons, run_step (step_rewind_symbol a w work g s), ih]
    simp

def totalTime : List (List A) → ℕ
  | [] => 1
  | xs :: xss => (xs.length + 1) + (xs.length + 1) + pairTime xs xss +
    (xs.length + 1) + ((stream xss).length + 1) + totalTime xss

theorem all_pairs_run (xss : List (List A)) (g : Bool) :
    run (totalTime xss) (config .outer (stream xss) [] [] [] g false) =
      some (haltList (machine A) [g && decide xss.Nodup]) := by
  induction xss generalizing g with
  | nil =>
    simpa [totalTime, stream] using (run_step (step_halt g false) 0).trans (run_zero _)
  | cons xs xss ih =>
    rw [show totalTime (xs :: xss) = (xs.length + 1) + ((xs.length + 1) +
      (pairTime xs xss + ((xs.length + 1) + (((stream xss).length + 1) + totalTime xss)))) by
        simp [totalTime]; omega]
    change run _ (config .outer (row xs ++ stream xss) [] [] [] g false) = _
    rw [run_add (outer_read_run xs _ [] [] [] g false)]
    simp only [List.append_nil]
    have hf := flip_run xs.reverse [] (stream xss) [] g false
    simp only [List.length_reverse] at hf
    rw [run_add hf]
    simp only [List.reverse_reverse, List.append_nil]
    rw [run_add (compare_records_run xs xss [] g)]
    simp only [List.append_nil]
    rw [run_add (clear_run xs _ _ false)]
    have hw := rewind_run (stream xss).reverse [] (g && decide (xs ∉ xss)) false
    simp only [List.length_reverse] at hw
    rw [run_add hw]
    simp only [List.reverse_reverse, List.append_nil]
    rw [ih]
    simp [List.nodup_cons, Bool.and_assoc]

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem records_le_stream_length (xss : List (List A)) : xss.length ≤ (stream xss).length := by
  induction xss with
  | nil => simp [stream]
  | cons xs xss ih => simp only [stream, List.length_append, row_length, List.length_cons]; omega

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem pairTime_bound (xs : List A) (xss : List (List A)) :
    pairTime xs xss ≤ 3 * (stream xss).length + 1 := by
  induction xss with
  | nil => simp [pairTime, stream]
  | cons ys yss ih =>
    have hm := Nat.min_le_right xs.length ys.length
    simp only [pairTime, stream, List.length_append, row_length]
    omega

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem totalTime_bound (xss : List (List A)) :
    totalTime xss ≤ 5 * (stream xss).length * xss.length + 1 := by
  induction xss with
  | nil => simp [totalTime, stream]
  | cons xs xss ih =>
    have hp := pairTime_bound xs xss
    have hl : (stream xss).length ≤ (stream (xs :: xss)).length := by
      simp [stream]
    have hm := Nat.mul_le_mul_right xss.length (Nat.mul_le_mul_left 5 hl)
    have hr : (xs.length + 1) + (xs.length + 1) + pairTime xs xss +
        (xs.length + 1) + ((stream xss).length + 1) ≤ 5 * (stream (xs :: xss)).length := by
      simp only [stream, List.length_append, row_length]
      omega
    calc
      totalTime (xs :: xss) ≤ 5 * (stream (xs :: xss)).length +
          (5 * (stream xss).length * xss.length + 1) := by
        simp only [totalTime]
        omega
      _ ≤ 5 * (stream (xs :: xss)).length +
          (5 * (stream (xs :: xss)).length * xss.length + 1) := by omega
      _ = 5 * (stream (xs :: xss)).length * (xs :: xss).length + 1 := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem totalTime_quadratic (xss : List (List A)) :
    totalTime xss ≤ 5 * (stream xss).length * (stream xss).length + 1 := by
  have h := Nat.mul_le_mul_left (5 * (stream xss).length) (records_le_stream_length xss)
  exact (totalTime_bound xss).trans (Nat.add_le_add_right h 1)

theorem machine_init (w : List (Option A)) :
    initList (machine A) w = config .outer w [] [] [] true false := by
  simp [initList, machine, config, initialState]
  congr 1
  funext k
  cases k <;> rfl

def collisionVerifier (xss : List (List A)) : Bool := decide xss.Nodup

omit [Fintype A] [Inhabited A] in
theorem collisionVerifier_spec (xss : List (List A)) : collisionVerifier xss = true ↔ xss.Nodup := by
  simp [collisionVerifier]

/-- Complete pairwise traversal of delimited records, with all work stacks
empty at halt and a quadratic bound in the actual serialized input length. -/
noncomputable def collisionComputable :
    TM2ComputableInPolyTime (listEncoding (wordEncoding A)) finEncodingBoolBool collisionVerifier where
  tm := machine A
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 5 * Polynomial.X * Polynomial.X + 1
  outputsFun xss :=
    { steps := totalTime xss
      evals_in_steps := by
        change run _ (initList (machine A) (List.map id ((listEncoding (wordEncoding A)).encode xss))) =
          some (haltList (machine A) [collisionVerifier xss])
        rw [List.map_id, ← stream_encode, machine_init]
        simpa [collisionVerifier] using all_pairs_run xss true
      steps_le_m := by
        simpa [← stream_encode] using totalTime_quadratic xss }

theorem collision_polyTimeDecidable :
    PolyTimeDecidable (listEncoding (wordEncoding A)) (fun xss : List (List A) => xss.Nodup) :=
  ⟨collisionVerifier, ⟨collisionComputable⟩, collisionVerifier_spec⟩

end

end RecordCollision

end ProteinFolding.Square

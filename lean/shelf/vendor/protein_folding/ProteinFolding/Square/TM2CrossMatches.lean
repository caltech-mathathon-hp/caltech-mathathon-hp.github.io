import ProteinFolding.Square.TM2Collision

/-! A finite-alphabet TM2 counting equal records across two lists. Queries and
records retain multiplicity. Each query is compared with every record, and the
record stream is preserved for the next query. The output is a unary count. -/

namespace ProteinFolding.Square.CrossMatches

open Turing Computability

abbrev Stack := RecordCollision.Stack

abbrev Raw (A : Type) := PairSymbol (Option A) (Option A)

def Alphabet (A : Type) : Stack → Type
  | .input | .work => Raw A
  | .first | .saved => A
  | .output => Unit

instance alphabetFintype (A : Type) [Fintype A] (k : Stack) : Fintype (Alphabet A k) := by
  cases k <;> dsimp [Alphabet] <;> infer_instance

inductive Label where
  | outer | flipFirst | seek | beginRow | inner | restore | clearSaved | rewind | finish
  deriving DecidableEq, Fintype

structure State (A : Type) where
  token : Option (Raw A)
  held : Option A
  same : Bool
  deriving Fintype

def initialState (A : Type) : State A := ⟨none, none, false⟩

def clean {A : Type} (s : State A) : State A := ⟨none, none, s.same⟩

def leftValue {A : Type} : Option (Raw A) → Option A
  | some (.left a) => a | _ => none

def rightValue {A : Type} : Option (Raw A) → Option A
  | some (.right a) => a | _ => none

def Program (A : Type) [DecidableEq A] [Inhabited A] :
    Label → TM2.Stmt (Alphabet A) Label (State A)
  | .outer =>
    .pop .input (fun s a => {s with token := a})
      (.branch (fun s => (leftValue s.token).isSome)
        (.push .first (fun s => (leftValue s.token).getD default)
          (.load clean (.goto (fun _ => .outer))))
        (.branch (fun s => match s.token with | some (.left none) => true | _ => false)
          (.load clean (.goto (fun _ => .flipFirst)))
          (.load clean (.goto (fun _ => .finish)))))
  | .flipFirst =>
    .pop .first (fun s a => {s with held := a})
      (.branch (fun s => s.held.isSome)
        (.push .saved (fun s => s.held.getD default) (.load clean (.goto (fun _ => .flipFirst))))
        (.load clean (.goto (fun _ => .seek))))
  | .seek =>
    .pop .input (fun s a => {s with token := a})
      (.push .work (fun s => s.token.getD .sep)
        (.branch (fun s => match s.token with | some .sep => true | _ => false)
          (.load clean (.goto (fun _ => .beginRow)))
          (.load clean (.goto (fun _ => .seek)))))
  | .beginRow =>
    .peek .input (fun s a => {s with token := a})
      (.branch (fun s => s.token.isSome)
        (.load (fun s => {clean s with same := true}) (.goto (fun _ => .inner)))
        (.load clean (.goto (fun _ => .clearSaved))))
  | .inner =>
    .pop .input (fun s a => {s with token := a})
      (.branch (fun s => (rightValue s.token).isSome)
        (.push .work (fun s => s.token.getD .sep)
          (.pop .saved (fun s a => {s with held := a, same := s.same && decide (s.token = some (.right a))})
            (.branch (fun s => s.held.isSome)
              (.push .first (fun s => s.held.getD default) (.load clean (.goto (fun _ => .inner))))
              (.load clean (.goto (fun _ => .inner))))))
        (.push .work (fun _ => .right none)
          (.peek .saved (fun s a => {s with same := s.same && a.isNone})
            (.branch State.same
              (.push .output (fun _ => ())
                (.load (fun _ => initialState A) (.goto (fun _ => .restore))))
              (.load (fun _ => initialState A) (.goto (fun _ => .restore)))))))
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
        (.push .input (fun s => s.token.getD .sep) (.load clean (.goto (fun _ => .rewind))))
        (.load clean (.goto (fun _ => .outer))))
  | .finish =>
    .pop .input (fun s a => {s with token := a})
      (.branch (fun s => s.token.isSome)
        (.load clean (.goto (fun _ => .finish)))
        (.load (fun _ => initialState A) .halt))

def machine (A : Type) [Fintype A] [DecidableEq A] [Inhabited A] : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A
  Λ := Label
  main := .outer
  σ := State A
  initialState := initialState A
  Γk₀Fin := inferInstanceAs (Fintype (Raw A))
  m := Program A

def recordStacks {A : Type} (w : List (Raw A)) (xs ys : List A) (work : List (Raw A)) (o : List Unit) :
    (k : Stack) → List (Alphabet A k)
  | .input => w | .first => xs | .saved => ys | .work => work | .output => o

section

variable {A : Type}

@[simp]
theorem stacks_update_input (w w' : List (Raw A)) (xs ys : List A) (work : List (Raw A)) (o : List Unit) :
    Function.update (recordStacks w xs ys work o) .input w' = recordStacks w' xs ys work o := by
  funext k; cases k <;> simp [recordStacks]

@[simp]
theorem stacks_update_first (w : List (Raw A)) (xs xs' ys : List A) (work : List (Raw A)) (o : List Unit) :
    Function.update (recordStacks w xs ys work o) .first xs' = recordStacks w xs' ys work o := by
  funext k; cases k <;> simp [recordStacks]

@[simp]
theorem stacks_update_saved (w : List (Raw A)) (xs ys ys' : List A) (work : List (Raw A)) (o : List Unit) :
    Function.update (recordStacks w xs ys work o) .saved ys' = recordStacks w xs ys' work o := by
  funext k; cases k <;> simp [recordStacks]

@[simp]
theorem stacks_update_work (w : List (Raw A)) (xs ys : List A) (work work' : List (Raw A)) (o : List Unit) :
    Function.update (recordStacks w xs ys work o) .work work' = recordStacks w xs ys work' o := by
  funext k; cases k <;> simp [recordStacks]

@[simp]
theorem stacks_update_output (w : List (Raw A)) (xs ys : List A) (work : List (Raw A)) (o o' : List Unit) :
    Function.update (recordStacks w xs ys work o) .output o' = recordStacks w xs ys work o' := by
  funext k; cases k <;> simp [recordStacks]

variable [Fintype A] [DecidableEq A] [Inhabited A]

def config (l : Label) (w : List (Raw A)) (xs ys : List A) (work : List (Raw A)) (n : ℕ) (same : Bool) :
    (machine A).Cfg := ⟨some l, ⟨none, none, same⟩, recordStacks w xs ys work (List.replicate n ())⟩

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

theorem step_outer_symbol (a : A) (w : List (Raw A)) (xs ys : List A) (work : List (Raw A)) (n : ℕ) (s : Bool) :
    (machine A).step (config .outer (.left (some a) :: w) xs ys work n s) =
      some (config .outer w (a :: xs) ys work n s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, leftValue]

theorem step_outer_end (w : List (Raw A)) (xs ys : List A) (work : List (Raw A)) (n : ℕ) (s : Bool) :
    (machine A).step (config .outer (.left none :: w) xs ys work n s) =
      some (config .flipFirst w xs ys work n s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, leftValue]

theorem step_outer_separator (w : List (Raw A)) (n : ℕ) :
    (machine A).step (config .outer (.sep :: w) [] [] [] n false) =
      some (config .finish w [] [] [] n false) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, leftValue]

theorem step_flip_symbol (a : A) (w : List (Raw A)) (xs ys : List A) (work : List (Raw A)) (n : ℕ) (s : Bool) :
    (machine A).step (config .flipFirst w (a :: xs) ys work n s) =
      some (config .flipFirst w xs (a :: ys) work n s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_flip_end (w : List (Raw A)) (ys : List A) (work : List (Raw A)) (n : ℕ) (s : Bool) :
    (machine A).step (config .flipFirst w [] ys work n s) =
      some (config .seek w [] ys work n s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_seek_left (a : Option A) (w : List (Raw A)) (ys : List A) (work : List (Raw A)) (n : ℕ) :
    (machine A).step (config .seek (.left a :: w) [] ys work n false) =
      some (config .seek w [] ys (.left a :: work) n false) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_seek_separator (w : List (Raw A)) (ys : List A) (work : List (Raw A)) (n : ℕ) :
    (machine A).step (config .seek (.sep :: w) [] ys work n false) =
      some (config .beginRow w [] ys (.sep :: work) n false) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_begin_nonempty (a : Raw A) (w : List (Raw A)) (ys : List A) (work : List (Raw A)) (n : ℕ) :
    (machine A).step (config .beginRow (a :: w) [] ys work n false) =
      some (config .inner (a :: w) [] ys work n true) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_begin_empty (ys : List A) (work : List (Raw A)) (n : ℕ) :
    (machine A).step (config .beginRow [] [] ys work n false) =
      some (config .clearSaved [] [] ys work n false) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_inner_empty (a : A) (w : List (Raw A)) (xs : List A) (work : List (Raw A)) (n : ℕ) (s : Bool) :
    (machine A).step (config .inner (.right (some a) :: w) xs [] work n s) =
      some (config .inner w xs [] (.right (some a) :: work) n false) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, rightValue]
  intro _ h
  cases PairSymbol.right.inj h

theorem step_inner_cons (a y : A) (w : List (Raw A)) (xs ys : List A) (work : List (Raw A)) (n : ℕ) (s : Bool) :
    (machine A).step (config .inner (.right (some a) :: w) xs (y :: ys) work n s) =
      some (config .inner w (y :: xs) ys (.right (some a) :: work) n (s && decide (a = y))) := by
  by_cases h : a = y <;>
    simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, rightValue, h]
  all_goals exact fun _ he => h (Option.some.inj (PairSymbol.right.inj he))

theorem step_inner_end (w : List (Raw A)) (xs ys : List A) (work : List (Raw A)) (n : ℕ) (s : Bool) :
    (machine A).step (config .inner (.right none :: w) xs ys work n s) =
      some (config .restore w xs ys (.right none :: work)
        (n + if s && decide (ys = []) then 1 else 0) false) := by
  cases ys <;> cases s <;>
    simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux,
      rightValue, initialState, List.replicate_succ]

theorem step_restore_symbol (a : A) (w : List (Raw A)) (xs ys : List A) (work : List (Raw A)) (n : ℕ) (s : Bool) :
    (machine A).step (config .restore w (a :: xs) ys work n s) =
      some (config .restore w xs (a :: ys) work n s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_restore_end (w : List (Raw A)) (ys : List A) (work : List (Raw A)) (n : ℕ) (s : Bool) :
    (machine A).step (config .restore w [] ys work n s) =
      some (config .beginRow w [] ys work n s) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_clear_symbol (a : A) (ys : List A) (work : List (Raw A)) (n : ℕ) :
    (machine A).step (config .clearSaved [] [] (a :: ys) work n false) =
      some (config .clearSaved [] [] ys work n false) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_clear_end (work : List (Raw A)) (n : ℕ) :
    (machine A).step (config .clearSaved [] [] [] work n false) =
      some (config .rewind [] [] [] work n false) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_rewind_symbol (a : Raw A) (w work : List (Raw A)) (n : ℕ) :
    (machine A).step (config .rewind w [] [] (a :: work) n false) =
      some (config .rewind (a :: w) [] [] work n false) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_rewind_end (w : List (Raw A)) (n : ℕ) :
    (machine A).step (config .rewind w [] [] [] n false) = some (config .outer w [] [] [] n false) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_finish_symbol (a : Raw A) (w : List (Raw A)) (n : ℕ) :
    (machine A).step (config .finish (a :: w) [] [] [] n false) =
      some (config .finish w [] [] [] n false) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux]

theorem step_finish_halt (n : ℕ) :
    (machine A).step (config .finish [] [] [] [] n false) =
      some (haltList (machine A) (List.replicate n ())) := by
  simp [machine, FinTM2.step, TM2.step, Program, config, clean, recordStacks, TM2.stepAux, initialState, haltList]
  funext k
  cases k <;> rfl

def leftRow (xs : List A) : List (Raw A) := xs.map (fun a => .left (some a)) ++ [.left none]
def rightRow (xs : List A) : List (Raw A) := xs.map (fun a => .right (some a)) ++ [.right none]

def leftStream : List (List A) → List (Raw A)
  | [] => [] | xs :: xss => leftRow xs ++ leftStream xss

def rightStream : List (List A) → List (Raw A)
  | [] => [] | xs :: xss => rightRow xs ++ rightStream xss

def inputStream (queries records : List (List A)) : List (Raw A) :=
  leftStream queries ++ .sep :: rightStream records

def countMatches (xs : List A) : List (List A) → ℕ
  | [] => 0
  | ys :: yss => (if ys = xs then 1 else 0) + countMatches xs yss

def crossCount : List (List A) → List (List A) → ℕ
  | [], _ => 0
  | xs :: xss, yss => countMatches xs yss + crossCount xss yss

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem leftRow_length (xs : List A) : (leftRow xs).length = xs.length + 1 := by simp [leftRow]
omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem rightRow_length (xs : List A) : (rightRow xs).length = xs.length + 1 := by simp [rightRow]

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem leftStream_eq (xss : List (List A)) :
    leftStream xss = (RecordCollision.stream xss).map PairSymbol.left := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    simp [leftStream, RecordCollision.stream, leftRow, RecordCollision.row, ih, List.map_map, Function.comp_def]

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem rightStream_eq (xss : List (List A)) :
    rightStream xss = (RecordCollision.stream xss).map PairSymbol.right := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    simp [rightStream, RecordCollision.stream, rightRow, RecordCollision.row, ih, List.map_map, Function.comp_def]

omit [DecidableEq A] [Inhabited A] in
theorem inputStream_encode (queries records : List (List A)) :
    inputStream queries records =
      (pairEncoding (listEncoding (wordEncoding A)) (listEncoding (wordEncoding A))).encode
        (queries, records) := by
  simp [inputStream, leftStream_eq, rightStream_eq, RecordCollision.stream_encode, pairEncoding]

theorem read_run (xs : List A) (w : List (Raw A)) (first saved : List A) (work : List (Raw A)) (n : ℕ) :
    run (xs.length + 1) (config .outer (leftRow xs ++ w) first saved work n false) =
      some (config .flipFirst w (xs.reverse ++ first) saved work n false) := by
  induction xs generalizing first with
  | nil => simp [leftRow, run_step (step_outer_end w first saved work n false), run_zero]
  | cons a xs ih =>
    simp only [leftRow, List.map_cons, List.cons_append, List.length_cons]
    rw [run_step (step_outer_symbol a _ first saved work n false)]
    simpa [leftRow] using ih (a :: first)

theorem flip_run (first saved : List A) (w : List (Raw A)) (work : List (Raw A)) (n : ℕ) :
    run (first.length + 1) (config .flipFirst w first saved work n false) =
      some (config .seek w [] (first.reverse ++ saved) work n false) := by
  induction first generalizing saved with
  | nil => rw [List.length_nil, run_step (step_flip_end w saved work n false), run_zero]; simp
  | cons a first ih =>
    rw [List.length_cons, run_step (step_flip_symbol a w first saved work n false), ih]
    simp

theorem seek_run (qs : List (Option A)) (w : List (Raw A)) (saved : List A) (work : List (Raw A)) (n : ℕ) :
    run (qs.length + 1) (config .seek (qs.map PairSymbol.left ++ .sep :: w) [] saved work n false) =
      some (config .beginRow w [] saved
        ((qs.map (PairSymbol.left (B := Option A)) ++ [PairSymbol.sep]).reverse ++ work) n false) := by
  induction qs generalizing work with
  | nil => simp [run_step (step_seek_separator w saved work n), run_zero]
  | cons a qs ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [run_step (step_seek_left a _ saved work n), ih]
    simp

theorem restore_run (first saved : List A) (w : List (Raw A)) (work : List (Raw A)) (n : ℕ) :
    run (first.length + 1) (config .restore w first saved work n false) =
      some (config .beginRow w [] (first.reverse ++ saved) work n false) := by
  induction first generalizing saved with
  | nil => rw [List.length_nil, run_step (step_restore_end w saved work n false), run_zero]; simp
  | cons a first ih =>
    rw [List.length_cons, run_step (step_restore_symbol a w first saved work n false), ih]
    simp

theorem inner_run (ys xs first : List A) (w : List (Raw A)) (work : List (Raw A)) (n : ℕ) (s : Bool) :
    run (ys.length + 1) (config .inner (rightRow ys ++ w) first xs work n s) =
      some (config .restore w ((xs.take ys.length).reverse ++ first) (xs.drop ys.length)
        ((rightRow ys).reverse ++ work) (n + if s && decide (ys = xs) then 1 else 0) false) := by
  induction ys generalizing xs first work s with
  | nil =>
    cases xs with
    | nil =>
      simpa [rightRow] using
        (run_step (step_inner_end w first [] work n s) 0).trans (run_zero _)
    | cons x xs =>
      simpa [rightRow] using
        (run_step (step_inner_end w first (x :: xs) work n s) 0).trans (run_zero _)
  | cons a ys ih =>
    cases xs with
    | nil =>
      simp only [rightRow, List.map_cons, List.cons_append, List.length_cons]
      rw [run_step (step_inner_empty a _ first work n s)]
      simpa [rightRow] using ih [] first (.right (some a) :: work) false
    | cons x xs =>
      simp only [rightRow, List.map_cons, List.cons_append, List.length_cons]
      rw [run_step (step_inner_cons a x _ first xs work n s)]
      simpa [rightRow, List.cons.injEq, Bool.and_assoc] using
        ih xs (x :: first) (.right (some a) :: work) (s && decide (a = x))

theorem compare_records_run (xs : List A) (records : List (List A)) (work : List (Raw A)) (n : ℕ) :
    run (RecordCollision.pairTime xs records) (config .beginRow (rightStream records) [] xs work n false) =
      some (config .clearSaved [] [] xs ((rightStream records).reverse ++ work)
        (n + countMatches xs records) false) := by
  induction records generalizing work n with
  | nil =>
    simpa [RecordCollision.pairTime, rightStream, countMatches] using
      (run_step (step_begin_empty xs work n) 0).trans (run_zero _)
  | cons ys records ih =>
    have hr : rightRow ys ++ rightStream records ≠ [] := by simp [rightRow]
    obtain ⟨a, w, hw⟩ := List.exists_cons_of_ne_nil hr
    have hbegin := step_begin_nonempty a w xs work n
    rw [← hw] at hbegin
    rw [show RecordCollision.pairTime xs (ys :: records) =
      ((ys.length + 1) + (((xs.take ys.length).reverse).length + 1 +
        RecordCollision.pairTime xs records)) + 1 by simp [RecordCollision.pairTime]; omega]
    change run _ (config .beginRow (rightRow ys ++ rightStream records) [] xs work n false) = _
    rw [run_step hbegin, run_add (inner_run ys xs [] (rightStream records) work n true)]
    simp only [List.append_nil, Bool.true_and]
    rw [run_add (restore_run _ _ _ _ _)]
    simp only [List.reverse_reverse, List.take_append_drop]
    rw [ih]
    simp [rightStream, countMatches, Nat.add_assoc, eq_comm, List.append_assoc]

theorem clear_run (xs : List A) (work : List (Raw A)) (n : ℕ) :
    run (xs.length + 1) (config .clearSaved [] [] xs work n false) =
      some (config .rewind [] [] [] work n false) := by
  induction xs with
  | nil => rw [List.length_nil, run_step (step_clear_end work n), run_zero]
  | cons x xs ih => rw [List.length_cons, run_step (step_clear_symbol x xs work n), ih]

theorem rewind_run (work w : List (Raw A)) (n : ℕ) :
    run (work.length + 1) (config .rewind w [] [] work n false) =
      some (config .outer (work.reverse ++ w) [] [] [] n false) := by
  induction work generalizing w with
  | nil => rw [List.length_nil, run_step (step_rewind_end w n), run_zero]; simp
  | cons a work ih =>
    rw [List.length_cons, run_step (step_rewind_symbol a w work n), ih]
    simp

theorem finish_run (w : List (Raw A)) (n : ℕ) :
    run (w.length + 1) (config .finish w [] [] [] n false) =
      some (haltList (machine A) (List.replicate n ())) := by
  induction w with
  | nil => rw [List.length_nil, run_step (step_finish_halt n), run_zero]
  | cons a w ih => rw [List.length_cons, run_step (step_finish_symbol a w n), ih]

def totalTime : List (List A) → List (List A) → ℕ
  | [], records => (rightStream records).length + 2
  | xs :: queries, records => (xs.length + 1) + (xs.length + 1) +
      ((leftStream queries).length + 1) + RecordCollision.pairTime xs records +
      (xs.length + 1) + ((inputStream queries records).length + 1) + totalTime queries records

theorem cross_run (queries records : List (List A)) (n : ℕ) :
    run (totalTime queries records) (config .outer (inputStream queries records) [] [] [] n false) =
      some (haltList (machine A) (List.replicate (n + crossCount queries records) ())) := by
  induction queries generalizing n with
  | nil =>
    simp only [totalTime, inputStream, leftStream, List.nil_append, crossCount, Nat.add_zero]
    rw [run_step (step_outer_separator (rightStream records) n), finish_run]
  | cons xs queries ih =>
    rw [show totalTime (xs :: queries) records = (xs.length + 1) + ((xs.length + 1) +
      (((leftStream queries).length + 1) + (RecordCollision.pairTime xs records +
        ((xs.length + 1) + (((inputStream queries records).length + 1) + totalTime queries records))))) by
        simp [totalTime]; omega]
    have hi : inputStream (xs :: queries) records = leftRow xs ++ inputStream queries records := by
      simp [inputStream, leftStream, List.append_assoc]
    rw [hi]
    rw [run_add (read_run xs _ [] [] [] n)]
    simp only [List.append_nil]
    have hf := flip_run xs.reverse [] (inputStream queries records) [] n
    simp only [List.length_reverse] at hf
    rw [run_add hf]
    simp only [List.reverse_reverse, List.append_nil]
    have hseek := seek_run (RecordCollision.stream queries) (rightStream records) xs [] n
    simp only [← leftStream_eq, List.append_nil] at hseek
    have hlen : (RecordCollision.stream queries).length = (leftStream queries).length := by simp [leftStream_eq]
    rw [hlen] at hseek
    change run ((leftStream queries).length + 1)
      (config .seek (inputStream queries records) [] xs [] n false) = _ at hseek
    rw [run_add hseek, run_add (compare_records_run xs records _ n)]
    rw [run_add (clear_run xs _ _)]
    have hwork : (rightStream records).reverse ++
        (leftStream queries ++ [(PairSymbol.sep : Raw A)]).reverse =
        (inputStream queries records).reverse := by simp [inputStream, List.append_assoc]
    rw [hwork]
    have hrew := rewind_run (inputStream queries records).reverse [] (n + countMatches xs records)
    simp only [List.length_reverse] at hrew
    rw [run_add hrew]
    simp only [List.reverse_reverse, List.append_nil]
    rw [ih]
    simp [crossCount, Nat.add_assoc]

omit [Fintype A] [Inhabited A] in
theorem countMatches_eq_filter (xs : List A) (records : List (List A)) :
    countMatches xs records = (records.filter (fun ys => ys = xs)).length := by
  induction records with
  | nil => rfl
  | cons ys records ih => by_cases h : ys = xs <;> simp [countMatches, h, ih, Nat.add_comm]

omit [Fintype A] [Inhabited A] in
theorem crossCount_eq_flatMap (queries records : List (List A)) :
    crossCount queries records =
      (queries.flatMap (fun xs => records.filter (fun ys => ys = xs))).length := by
  induction queries with
  | nil => rfl
  | cons xs queries ih => simp [crossCount, countMatches_eq_filter, ih]

omit [Fintype A] [Inhabited A] in
theorem crossCount_le (queries records : List (List A)) :
    crossCount queries records ≤ queries.length * records.length := by
  induction queries with
  | nil => simp [crossCount]
  | cons xs queries ih =>
    have hx : countMatches xs records ≤ records.length := by
      rw [countMatches_eq_filter]
      exact List.length_filter_le _ _
    simp only [crossCount, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem leftStream_length (queries : List (List A)) :
    (leftStream queries).length = (RecordCollision.stream queries).length := by simp [leftStream_eq]

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem rightStream_length (records : List (List A)) :
    (rightStream records).length = (RecordCollision.stream records).length := by simp [rightStream_eq]

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem inputStream_length (queries records : List (List A)) :
    (inputStream queries records).length = (leftStream queries).length + 1 + (rightStream records).length := by
  simp [inputStream, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem totalTime_bound (queries records : List (List A)) :
    totalTime queries records ≤ 7 * (inputStream queries records).length * queries.length +
      (rightStream records).length + 2 := by
  induction queries with
  | nil => simp [totalTime]
  | cons xs queries ih =>
    have hp : RecordCollision.pairTime xs records ≤ 3 * (rightStream records).length + 1 := by
      simpa [rightStream_length] using RecordCollision.pairTime_bound xs records
    have hl : (inputStream queries records).length ≤ (inputStream (xs :: queries) records).length := by
      simp only [inputStream_length, leftStream, List.length_append, leftRow_length]
      omega
    have hm := Nat.mul_le_mul_right queries.length (Nat.mul_le_mul_left 7 hl)
    have hr : (xs.length + 1) + (xs.length + 1) + ((leftStream queries).length + 1) +
        RecordCollision.pairTime xs records + (xs.length + 1) + ((inputStream queries records).length + 1) ≤
        7 * (inputStream (xs :: queries) records).length := by
      simp only [inputStream_length, leftStream, List.length_append, leftRow_length]
      omega
    calc
      totalTime (xs :: queries) records ≤ 7 * (inputStream (xs :: queries) records).length +
          (7 * (inputStream queries records).length * queries.length + (rightStream records).length + 2) := by
        simp only [totalTime]
        omega
      _ ≤ 7 * (inputStream (xs :: queries) records).length +
          (7 * (inputStream (xs :: queries) records).length * queries.length + (rightStream records).length + 2) := by omega
      _ = 7 * (inputStream (xs :: queries) records).length * (xs :: queries).length +
          (rightStream records).length + 2 := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega

omit [Fintype A] [DecidableEq A] [Inhabited A] in
theorem totalTime_quadratic (queries records : List (List A)) :
    totalTime queries records ≤ 7 * (inputStream queries records).length *
      (inputStream queries records).length + (inputStream queries records).length + 2 := by
  have hq : queries.length ≤ (inputStream queries records).length := by
    have h := RecordCollision.records_le_stream_length queries
    rw [← leftStream_length] at h
    rw [inputStream_length]
    omega
  have hr : (rightStream records).length ≤ (inputStream queries records).length := by
    rw [inputStream_length]
    omega
  have hm := Nat.mul_le_mul_left (7 * (inputStream queries records).length) hq
  have ht := totalTime_bound queries records
  omega

theorem machine_init (w : List (Raw A)) : initList (machine A) w = config .outer w [] [] [] 0 false := by
  simp [initList, machine, config, initialState]
  congr 1
  funext k
  cases k <;> rfl

def verifier (input : List (List A) × List (List A)) : List Unit :=
  List.replicate (crossCount input.1 input.2) ()

/-- All cross-list equality pairs, counted in unary, in polynomial TM2 time. -/
noncomputable def computable :
    TM2ComputableInPolyTime
      (pairEncoding (listEncoding (wordEncoding A)) (listEncoding (wordEncoding A)))
      (wordEncoding Unit) verifier where
  tm := machine A
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 7 * Polynomial.X * Polynomial.X + Polynomial.X + 2
  outputsFun input :=
    { steps := totalTime input.1 input.2
      evals_in_steps := by
        change run _ (initList (machine A) (List.map id
          ((pairEncoding (listEncoding (wordEncoding A)) (listEncoding (wordEncoding A))).encode input))) =
          some (haltList (machine A) (List.map id (verifier input)))
        simp only [List.map_id]
        rw [← inputStream_encode, machine_init]
        simpa [verifier] using cross_run input.1 input.2 0
      steps_le_m := by
        simpa [inputStream_encode] using totalTime_quadratic input.1 input.2 }

end

end ProteinFolding.Square.CrossMatches

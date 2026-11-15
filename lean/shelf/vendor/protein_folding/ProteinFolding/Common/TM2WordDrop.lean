import ProteinFolding.Common.TM2Transfer
import ProteinFolding.Common.TM2PairSwap

/-! Actual polynomial-time unary-indexed word suffix selection. The raw
machine reads a unary index first, drops that many symbols, and restores the
remaining word's order through a buffer. The public adapter swaps the ordinary
(word,index) input fields using the proved polynomial-time pair machine. -/

namespace ProteinFolding.TM2WordDrop

open Computability Turing TM2

inductive Slot where
  | input | buffer | counter | output
  deriving DecidableEq, Fintype

inductive Phase where
  | count | drop | scan | emit | finish
  deriving DecidableEq, Fintype

def Alphabet (A : Type) : Slot → Type
  | .input => PairSymbol Bool A
  | .buffer | .output => A
  | .counter => Unit

abbrev State (A : Type) := Bool × Option A

def initialState {A : Type} : State A := (false, none)

def contents {A : Type} (u : List (PairSymbol Bool A)) (v : List A) (c : ℕ) (o : List A) :
    ∀ k, List (Alphabet A k)
  | .input => u
  | .buffer => v
  | .counter => List.replicate c ()
  | .output => o

def cfg {A : Type} (p : Phase) (u : List (PairSymbol Bool A)) (v : List A)
    (c : ℕ) (o : List A) : Cfg (Alphabet A) Phase (State A) :=
  ⟨some p, initialState, contents u v c o⟩

def readRight {A : Type} : PairSymbol Bool A → Option A
  | .right a => some a
  | _ => none

def countHead {A : Type} : Option (PairSymbol Bool A) → Bool
  | some (.left _) => true
  | _ => false

instance {A : Type} [Inhabited A] : Inhabited (Alphabet A .buffer) := inferInstanceAs (Inhabited A)

def program {A : Type} [Inhabited A] : Phase → Stmt (Alphabet A) Phase (State A)
  | .count => .pop .input (fun _ h => (countHead h, none))
    (.branch Prod.fst
      (.push .counter (fun _ => ()) (.load (fun _ => initialState) (.goto (fun _ => .count))))
      (.load (fun _ => initialState) (.goto (fun _ => .drop))))
  | .drop => .pop .counter (fun _ h => (h.isSome, none))
    (.branch Prod.fst
      (.pop .input (fun _ _ => initialState) (.goto (fun _ => .drop)))
      (.load (fun _ => initialState) (.goto (fun _ => .scan))))
  | .scan => .pop .input (fun _ h => (false, h.bind readRight))
    (.branch (fun st => st.2.isSome)
      (.push .buffer (fun st => st.2.getD default)
        (.load (fun _ => initialState) (.goto (fun _ => .scan))))
      (.load (fun _ => initialState) (.goto (fun _ => .emit))))
  | .emit => TM2Transfer.transferStmt (Γ := Alphabet A) (σ := Bool)
    Slot.buffer Slot.output (id : A → A) Phase.emit Phase.finish
  | .finish => .load (fun _ => initialState) .halt

def run {A : Type} [Inhabited A] (n : ℕ) (q : Cfg (Alphabet A) Phase (State A)) :
    Option (Cfg (Alphabet A) Phase (State A)) :=
  (fun x : Option (Cfg (Alphabet A) Phase (State A)) => x.bind (step program))^[n] (some q)

theorem run_add {A : Type} [Inhabited A] {q q' : Cfg (Alphabet A) Phase (State A)} {n : ℕ}
    (h : run n q = some q') (m : ℕ) : run (n + m) q = run m q' := by
  rw [Nat.add_comm n m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg (Alphabet A) Phase (State A)) => x.bind (step program))^[n] (some q) = some q' from h]

theorem run_step {A : Type} [Inhabited A] {q q' : Cfg (Alphabet A) Phase (State A)}
    (h : step program q = some q') (n : ℕ) : run (n + 1) q = run n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem update_input {A : Type} (u u' : List (PairSymbol Bool A)) (v : List A) (c : ℕ) (o : List A) :
    Function.update (contents u v c o) .input u' = contents u' v c o := by
  funext k; cases k <;> simp [contents]

theorem update_buffer {A : Type} (u : List (PairSymbol Bool A)) (v v' : List A) (c : ℕ) (o : List A) :
    Function.update (contents u v c o) .buffer v' = contents u v' c o := by
  funext k; cases k <;> simp [contents]

theorem update_counter {A : Type} (u : List (PairSymbol Bool A)) (v : List A) (c c' : ℕ) (o : List A) :
    Function.update (contents u v c o) .counter (List.replicate c' ()) = contents u v c' o := by
  funext k; cases k <;> simp [contents]

theorem count_step_cons {A : Type} [Inhabited A] (u : List (PairSymbol Bool A))
    (v : List A) (c : ℕ) (o : List A) :
    step program (cfg .count (.left true :: u) v c o) = some (cfg .count u v (c + 1) o) := by
  simp [cfg, program, step, stepAux, contents, countHead]
  change Function.update (Function.update (contents (.left true :: u) v c o) .input u)
    .counter (List.replicate (c + 1) ()) = contents u v (c + 1) o
  rw [update_input, update_counter]

theorem count_step_sep {A : Type} [Inhabited A] (u : List (PairSymbol Bool A))
    (v : List A) (c : ℕ) (o : List A) :
    step program (cfg .count (.sep :: u) v c o) = some (cfg .drop u v c o) := by
  simp [cfg, program, step, stepAux, contents, countHead]
  exact update_input _ _ _ _ _

theorem count_run {A : Type} [Inhabited A] (n : ℕ) (u : List (PairSymbol Bool A))
    (v : List A) (c : ℕ) (o : List A) :
    run (n + 1) (cfg .count ((unaryEncodeNat n).map .left ++ .sep :: u) v c o) =
      some (cfg .drop u v (c + n) o) := by
  induction n generalizing c with
  | zero => simpa only [run, unaryEncodeNat, List.map_nil, List.nil_append, Nat.add_zero,
      Nat.zero_add, Function.iterate_one, Option.bind_some] using count_step_sep u v c o
  | succ n ih =>
    simp only [unaryEncodeNat, List.map_cons, List.cons_append]
    rw [run_step (count_step_cons _ _ _ _)]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (c + 1)

theorem drop_step_succ {A : Type} [Inhabited A] (u : List (PairSymbol Bool A))
    (v : List A) (c : ℕ) (o : List A) :
    step program (cfg .drop u v (c + 1) o) = some (cfg .drop u.tail v c o) := by
  simp [cfg, program, step, stepAux, contents, List.replicate_succ]
  change Function.update (Function.update (contents u v (c + 1) o) .counter (List.replicate c ()))
    .input u.tail = contents u.tail v c o
  rw [update_counter, update_input]

theorem drop_step_zero {A : Type} [Inhabited A] (u : List (PairSymbol Bool A))
    (v : List A) (o : List A) :
    step program (cfg .drop u v 0 o) = some (cfg .scan u v 0 o) := by
  simp [cfg, program, step, stepAux, contents]

theorem drop_run {A : Type} [Inhabited A] (u : List (PairSymbol Bool A))
    (v : List A) (n : ℕ) (o : List A) :
    run (n + 1) (cfg .drop u v n o) = some (cfg .scan (u.drop n) v 0 o) := by
  induction n generalizing u with
  | zero => simpa only [run, Function.iterate_one, Option.bind_some, List.drop_zero] using drop_step_zero u v o
  | succ n ih =>
    rw [run_step (drop_step_succ u v n o), ih]
    simp

theorem scan_step_cons {A : Type} [Inhabited A] (a : A) (u : List (PairSymbol Bool A))
    (v : List A) (c : ℕ) (o : List A) :
    step program (cfg .scan (.right a :: u) v c o) = some (cfg .scan u (a :: v) c o) := by
  simp [cfg, program, step, stepAux, contents, readRight]
  change Function.update (Function.update (contents (.right a :: u) v c o) .input u)
    .buffer (a :: v) = contents u (a :: v) c o
  rw [update_input, update_buffer]

theorem scan_step_nil {A : Type} [Inhabited A] (v : List A) (c : ℕ) (o : List A) :
    step program (cfg .scan [] v c o) = some (cfg .emit [] v c o) := by
  simp [cfg, program, step, stepAux, contents]

theorem scan_run {A : Type} [Inhabited A] (w v : List A) (c : ℕ) (o : List A) :
    run (w.length + 1) (cfg .scan (w.map .right) v c o) =
      some (cfg .emit [] (w.reverse ++ v) c o) := by
  induction w generalizing v with
  | nil => simpa only [run, List.map_nil, List.length_nil, Nat.zero_add, Function.iterate_one,
      Option.bind_some, List.reverse_nil, List.nil_append] using scan_step_nil v c o
  | cons a w ih =>
    simp only [List.map_cons, List.length_cons]
    rw [run_step (scan_step_cons a _ _ _ _), ih]
    simp

theorem emit_contents {A : Type} (u : List (PairSymbol Bool A)) (v : List A) (c : ℕ) (o : List A) :
    TM2Transfer.setStacks Slot.buffer Slot.output (contents u [] c []) v o = contents u v c o := by
  funext k
  cases k <;> simp [TM2Transfer.setStacks, contents]

theorem emit_run {A : Type} [Inhabited A] (u : List (PairSymbol Bool A)) (v : List A)
    (c : ℕ) (o : List A) :
    run (v.length + 1) (cfg .emit u v c o) = some (cfg .finish u [] c (v.reverse ++ o)) := by
  have h := TM2Transfer.transfer_run (Γ := Alphabet A) Slot.buffer Slot.output (by decide)
    (id : A → A) Phase.emit Phase.finish program rfl false none (contents u [] c []) v o
  simpa only [run, cfg, initialState, TM2Transfer.transferCfg, emit_contents, List.map_id] using h

def halted {A : Type} (o : List A) : Cfg (Alphabet A) Phase (State A) :=
  ⟨none, initialState, contents [] [] 0 o⟩

theorem finish_step {A : Type} [Inhabited A] (o : List A) :
    step program (cfg .finish [] [] 0 o) = some (halted o) := rfl

theorem program_run {A : Type} [Inhabited A] (n : ℕ) (w : List A) :
    run (2 * n + 2 * (w.drop n).length + 5)
      (cfg .count ((unaryEncodeNat n).map .left ++ .sep :: w.map .right) [] 0 []) =
        some (halted (w.drop n)) := by
  let d := (w.drop n).length
  rw [show 2 * n + 2 * (w.drop n).length + 5 =
      (n + 1) + ((n + 1) + ((d + 1) + ((d + 1) + 1))) by dsimp [d]; omega]
  rw [run_add (count_run n (w.map .right) [] 0 [])]
  simp only [Nat.zero_add]
  rw [run_add (drop_run (w.map .right) [] n [])]
  rw [← List.map_drop]
  rw [run_add (scan_run (w.drop n) [] 0 [])]
  simp only [List.append_nil]
  have he := emit_run (A := A) [] (w.drop n).reverse 0 []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at he
  rw [run_add he]
  exact finish_step (w.drop n)

def machine (A : Type) [Fintype A] [Inhabited A] : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A
  Λ := Phase
  main := .count
  σ := State A
  initialState := initialState
  Γk₀Fin := inferInstanceAs (Fintype (PairSymbol Bool A))
  m := program

theorem unary_length (n : ℕ) : (unaryEncodeNat n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, ih]

def machine_outputs {A : Type} [Fintype A] [Inhabited A] (n : ℕ) (w : List A) :
    TM2OutputsInTime (machine A)
      ((unaryEncodeNat n).map .left ++ .sep :: w.map .right)
      (some (w.drop n))
      (2 * ((pairEncoding unaryFinEncodingNat (wordEncoding A)).encode (n, w)).length + 5) := by
  have hi : initList (machine A) ((unaryEncodeNat n).map .left ++ .sep :: w.map .right) =
      cfg .count ((unaryEncodeNat n).map .left ++ .sep :: w.map .right) [] 0 [] := by
    apply congrArg (fun S => (⟨some .count, initialState, S⟩ : Cfg (Alphabet A) Phase (State A)))
    funext k; cases k <;> rfl
  have ho : haltList (machine A) (w.drop n) = halted (w.drop n) := by
    apply congrArg (fun S => (⟨none, initialState, S⟩ : Cfg (Alphabet A) Phase (State A)))
    funext k; cases k <;> rfl
  refine
    { steps := 2 * n + 2 * (w.drop n).length + 5
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change run _ (initList (machine A) _) = some (haltList (machine A) _)
    rw [hi, ho]
    exact program_run n w
  · simp only [pairEncoding, unaryFinEncodingNat, wordEncoding, List.length_append,
      List.length_map, List.length_cons, unary_length, List.length_drop]
    dsimp only [id]
    omega

noncomputable def prefixDropComputable (A : Type) [Fintype A] [Inhabited A] :
    TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat (wordEncoding A))
      (wordEncoding A) (fun p => p.2.drop p.1) where
  tm := machine A
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  outputsFun p := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime (machine A)
      (List.map id ((pairEncoding unaryFinEncodingNat (wordEncoding A)).encode p))
      (some (List.map id (p.2.drop p.1)))
      (2 * ((pairEncoding unaryFinEncodingNat (wordEncoding A)).encode p).length + 5)
    simpa only [List.map_id] using machine_outputs p.1 p.2

/-- Actual suffix selection at a unary index, for a fixed inhabited finite
alphabet. Out-of-range indices return the empty word. -/
noncomputable def dropComputable (A : Type) [Fintype A] [Inhabited A] :
    TM2ComputableInPolyTime (pairEncoding (wordEncoding A) unaryFinEncodingNat)
      (wordEncoding A) (fun p => p.1.drop p.2) :=
  TM2CompositionPoly.compose
    (TM2PairSwap.swapComputable (wordEncoding A) unaryFinEncodingNat) (prefixDropComputable A)

end ProteinFolding.TM2WordDrop

import ProteinFolding.Common.TM2PairProjections

/-! Truncated subtraction on unary natural encodings. The machine stores the
first operand as unary tokens, cancels one for each token of the second, and
serializes what remains. Empty-counter cancellation implements truncation. -/

namespace ProteinFolding.TM2UnarySubtraction

open Computability Turing TM2

inductive Slot where
  | input | counter | output
  deriving DecidableEq, Fintype

inductive Phase where
  | first | second | emit
  deriving DecidableEq, Fintype

abbrev Symbol := PairSymbol Bool Bool
abbrev State := Option Symbol × Bool

def Alphabet : Slot → Type
  | .input => Symbol
  | .counter => Unit
  | .output => Bool

def contents (w : List Symbol) (n : ℕ) (o : List Bool) : ∀ k, List (Alphabet k)
  | .input => w
  | .counter => List.replicate n ()
  | .output => o

def cfg (p : Phase) (st : State) (w : List Symbol) (n : ℕ) (o : List Bool) :
    Cfg Alphabet Phase State := ⟨some p, st, contents w n o⟩

def halted (o : List Bool) : Cfg Alphabet Phase State :=
  ⟨none, (none, false), contents [] 0 o⟩

def program : Phase → Stmt Alphabet Phase State
  | .first => .pop .input (fun st head => (head, st.2))
      (.branch (fun st => decide (st.1 = some .sep)) (.goto (fun _ => .second))
        (.branch (fun st => st.1.isSome)
          (.push .counter (fun _ => ()) (.goto (fun _ => .first)))
          (.goto (fun _ => .emit))))
  | .second => .pop .input (fun st head => (head, st.2))
      (.branch (fun st => st.1.isSome)
        (.pop .counter (fun st _ => st) (.goto (fun _ => .second)))
        (.goto (fun _ => .emit)))
  | .emit => .pop .counter (fun _ head => (none, head.isSome))
      (.branch Prod.snd
        (.push .output (fun _ => true) (.goto (fun _ => .emit)))
        (.load (fun _ => (none, false)) .halt))

theorem update_input (w w' : List Symbol) (n : ℕ) (o : List Bool) :
    Function.update (contents w n o) .input w' = contents w' n o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_counter (w : List Symbol) (n n' : ℕ) (o : List Bool) :
    Function.update (contents w n o) .counter (List.replicate n' ()) = contents w n' o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_output (w : List Symbol) (n : ℕ) (o o' : List Bool) :
    Function.update (contents w n o) .output o' = contents w n o' := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem first_step (st : State) (w : List Symbol) (n : ℕ) (o : List Bool) :
    step program (cfg .first st (.left true :: w) n o) =
      some (cfg .first (some (.left true), st.2) w (n + 1) o) := by
  simp [cfg, program, step, stepAux, contents, update_input, ← List.replicate_succ,
    update_counter]

theorem separator_step (st : State) (w : List Symbol) (n : ℕ) (o : List Bool) :
    step program (cfg .first st (.sep :: w) n o) =
      some (cfg .second (some .sep, st.2) w n o) := by
  simp [cfg, program, step, stepAux, contents, update_input]

theorem second_step (st : State) (w : List Symbol) (n : ℕ) (o : List Bool) :
    step program (cfg .second st (.right true :: w) n o) =
      some (cfg .second (some (.right true), st.2) w (n - 1) o) := by
  cases n <;> simp [cfg, program, step, stepAux, contents, update_input,
    List.replicate_succ, update_counter]

theorem second_nil_step (st : State) (n : ℕ) (o : List Bool) :
    step program (cfg .second st [] n o) = some (cfg .emit (none, st.2) [] n o) := by
  simp [cfg, program, step, stepAux, contents, update_input]

theorem emit_succ_step (st : State) (n : ℕ) (o : List Bool) :
    step program (cfg .emit st [] (n + 1) o) =
      some (cfg .emit (none, true) [] n (true :: o)) := by
  simp [cfg, program, step, stepAux, contents, List.replicate_succ]
  change Function.update (Function.update (contents [] (n + 1) o) .counter
    (List.replicate n ())) .output (true :: o) = contents [] n (true :: o)
  rw [update_counter, update_output]

theorem emit_zero_step (st : State) (o : List Bool) :
    step program (cfg .emit st [] 0 o) = some (halted o) := by
  simp [cfg, program, step, stepAux, halted, contents]

def run (n : ℕ) (q : Cfg Alphabet Phase State) : Option (Cfg Alphabet Phase State) :=
  (fun x : Option (Cfg Alphabet Phase State) => x.bind (step program))^[n] (some q)

theorem run_step {q q' : Cfg Alphabet Phase State} (h : step program q = some q') (n : ℕ) :
    run (n + 1) q = run n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add {q q' : Cfg Alphabet Phase State} {n : ℕ} (h : run n q = some q') (m : ℕ) :
    run (n + m) q = run m q' := by
  rw [Nat.add_comm n m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg Alphabet Phase State) => x.bind (step program))^[n] (some q) = some q' from h]

theorem first_run (a : ℕ) (st : State) (w : List Symbol) (n : ℕ) (o : List Bool) :
    run (a + 1) (cfg .first st (List.replicate a (.left true) ++ .sep :: w) n o) =
      some (cfg .second (some .sep, st.2) w (n + a) o) := by
  induction a generalizing st n with
  | zero => simpa [run] using separator_step st w n o
  | succ a ih =>
    simp only [List.replicate_succ, List.cons_append]
    rw [run_step (first_step st _ n o)]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (some (.left true), st.2) (n + 1)

theorem second_run (b : ℕ) (st : State) (n : ℕ) (o : List Bool) :
    run (b + 1) (cfg .second st (List.replicate b (.right true)) n o) =
      some (cfg .emit (none, st.2) [] (n - b) o) := by
  induction b generalizing st n with
  | zero => simpa [run] using second_nil_step st n o
  | succ b ih =>
    rw [List.replicate_succ, run_step (second_step st _ n o)]
    simpa [Nat.sub_sub, Nat.add_comm] using ih (some (.right true), st.2) (n - 1)

theorem emit_run (n : ℕ) (st : State) (o : List Bool) :
    run (n + 1) (cfg .emit st [] n o) = some (halted (List.replicate n true ++ o)) := by
  induction n generalizing st o with
  | zero => simpa [run] using emit_zero_step st o
  | succ n ih =>
    rw [run_step (emit_succ_step st n o), ih]
    simp [List.replicate_succ', List.append_assoc]

theorem unary_replicate (n : ℕ) : unaryEncodeNat n = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, ih, List.replicate_succ]

def encoding : FinEncoding (ℕ × ℕ) := pairEncoding unaryFinEncodingNat unaryFinEncodingNat

theorem encoding_word (a b : ℕ) : encoding.encode (a, b) =
    List.replicate a (.left true) ++ .sep :: List.replicate b (.right true) := by
  simp [encoding, pairEncoding, unaryFinEncodingNat, unary_replicate]

theorem program_run (a b : ℕ) :
    run (a + b + (a - b) + 3) (cfg .first (none, false) (encoding.encode (a, b)) 0 []) =
      some (halted (unaryEncodeNat (a - b))) := by
  rw [encoding_word]
  rw [show a + b + (a - b) + 3 = (a + 1) + ((b + 1) + ((a - b) + 1)) by omega,
    run_add (first_run a (none, false) _ 0 [])]
  simp only [Nat.zero_add]
  rw [run_add (second_run b (some .sep, false) a []), emit_run]
  simp only [List.append_nil, unary_replicate]

def machine : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Phase
  main := .first
  σ := State
  initialState := (none, false)
  Γk₀Fin := inferInstanceAs (Fintype Symbol)
  m := program

def machine_outputs (a b : ℕ) : TM2OutputsInTime machine (encoding.encode (a, b))
    (some (unaryEncodeNat (a - b))) (2 * (encoding.encode (a, b)).length + 1) := by
  have hi : initList machine (encoding.encode (a, b)) =
      cfg .first (none, false) (encoding.encode (a, b)) 0 [] := by
    apply congrArg (fun S => (⟨some .first, (none, false), S⟩ : Cfg Alphabet Phase State))
    funext k; cases k <;> rfl
  have ho : haltList machine (unaryEncodeNat (a - b)) = halted (unaryEncodeNat (a - b)) := by
    apply congrArg (fun S => (⟨none, (none, false), S⟩ : Cfg Alphabet Phase State))
    funext k; cases k <;> rfl
  refine
    { steps := a + b + (a - b) + 3
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change run _ (initList machine _) = some (haltList machine _)
    rw [hi, ho]
    exact program_run a b
  · rw [encoding_word]
    simp only [List.length_append, List.length_cons, List.length_replicate]
    omega

noncomputable def subtractionComputable :
    TM2ComputableInPolyTime encoding unaryFinEncodingNat (fun ab => ab.1 - ab.2) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 1
  outputsFun ab := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime machine (List.map id (encoding.encode ab))
      (some (List.map id (unaryEncodeNat (ab.1 - ab.2)))) (2 * (encoding.encode ab).length + 1)
    simpa only [List.map_id] using machine_outputs ab.1 ab.2

end ProteinFolding.TM2UnarySubtraction

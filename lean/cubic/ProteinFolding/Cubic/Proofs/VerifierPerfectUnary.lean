import ProteinFolding.Cubic.Proofs.VerifierPerfectCount

/-! Unary multiplication as an actual finite TM2 program. The verifier can use
bounded unary side witnesses, so multiplication output remains polynomial in
the verifier input length even on large or malformed candidate certificates. -/

namespace ProteinFolding.PerfectUnaryMultiplication

open Computability Turing TM2

inductive Slot where
  | input | first | second | buffer | output
  deriving DecidableEq, Fintype

inductive Phase where
  | scan | outer | inner | restore | clear | finish
  deriving DecidableEq, Fintype

abbrev InputSymbol := PairSymbol Bool Bool
abbrev Registers := Option InputSymbol × Bool

def Alphabet : Slot → Type
  | .input => InputSymbol
  | _ => Bool

def stackContents (w : List InputSymbol) (a b t : ℕ) (out : List Bool) :
    ∀ k, List (Alphabet k)
  | .input => w
  | .first => unaryEncodeNat a
  | .second => unaryEncodeNat b
  | .buffer => unaryEncodeNat t
  | .output => out

theorem update_input (w w' : List InputSymbol) (a b t : ℕ) (out : List Bool) :
    Function.update (stackContents w a b t out) .input w' = stackContents w' a b t out := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

theorem update_first (w : List InputSymbol) (a a' b t : ℕ) (out : List Bool) :
    Function.update (stackContents w a b t out) .first (unaryEncodeNat a') = stackContents w a' b t out := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

theorem update_second (w : List InputSymbol) (a b b' t : ℕ) (out : List Bool) :
    Function.update (stackContents w a b t out) .second (unaryEncodeNat b') = stackContents w a b' t out := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

theorem update_buffer (w : List InputSymbol) (a b t t' : ℕ) (out : List Bool) :
    Function.update (stackContents w a b t out) .buffer (unaryEncodeNat t') = stackContents w a b t' out := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

theorem update_output (w : List InputSymbol) (a b t : ℕ) (out out' : List Bool) :
    Function.update (stackContents w a b t out) .output out' = stackContents w a b t out' := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

theorem update_first_push (w : List InputSymbol) (a b t : ℕ) (out : List Bool) :
    Function.update (stackContents w a b t out) .first (true :: unaryEncodeNat a) =
      stackContents w (a + 1) b t out := update_first w a (a + 1) b t out

theorem update_second_push (w : List InputSymbol) (a b t : ℕ) (out : List Bool) :
    Function.update (stackContents w a b t out) .second (true :: unaryEncodeNat b) =
      stackContents w a (b + 1) t out := update_second w a b (b + 1) t out

theorem update_buffer_push (w : List InputSymbol) (a b t : ℕ) (out : List Bool) :
    Function.update (stackContents w a b t out) .buffer (true :: unaryEncodeNat t) =
      stackContents w a b (t + 1) out := update_buffer w a b t (t + 1) out

def isLeft : InputSymbol → Bool
  | .left _ => true
  | _ => false

def isRight : InputSymbol → Bool
  | .right _ => true
  | _ => false

def program : Phase → Stmt Alphabet Phase Registers
  | .scan => .pop .input (fun st x => (x, st.2))
      (.branch (fun st => st.1.isSome)
        (.branch (fun st => (st.1.map isLeft).getD false)
          (.push .first (fun _ => true) (.goto (fun _ => .scan)))
          (.branch (fun st => (st.1.map isRight).getD false)
            (.push .second (fun _ => true) (.goto (fun _ => .scan)))
            (.goto (fun _ => .scan))))
        (.load (fun _ => (none, false)) (.goto (fun _ => .outer))))
  | .outer => .pop .first (fun st x => (st.1, x.isSome))
      (.branch Prod.snd (.goto (fun _ => .inner)) (.goto (fun _ => .clear)))
  | .inner => .pop .second (fun st x => (st.1, x.isSome))
      (.branch Prod.snd
        (.push .buffer (fun _ => true)
          (.push .output (fun _ => true) (.goto (fun _ => .inner))))
        (.goto (fun _ => .restore)))
  | .restore => .pop .buffer (fun st x => (st.1, x.isSome))
      (.branch Prod.snd (.push .second (fun _ => true) (.goto (fun _ => .restore)))
        (.load (fun _ => (none, false)) (.goto (fun _ => .outer))))
  | .clear => .pop .second (fun st x => (st.1, x.isSome))
      (.branch Prod.snd (.goto (fun _ => .clear))
        (.load (fun _ => (none, false)) (.goto (fun _ => .finish))))
  | .finish => .halt

def cfg (label : Phase) (reg : Registers) (w : List InputSymbol)
    (a b t : ℕ) (out : List Bool) : Cfg Alphabet Phase Registers :=
  ⟨some label, reg, stackContents w a b t out⟩

abbrev advance : Option (Cfg Alphabet Phase Registers) → Option (Cfg Alphabet Phase Registers) :=
  fun x => x.bind (step program)

theorem unary_append (a b : ℕ) : unaryEncodeNat (a + b) = unaryEncodeNat a ++ unaryEncodeNat b := by
  induction a with
  | zero => simp [unaryEncodeNat]
  | succ a ih => simpa [unaryEncodeNat, Nat.succ_add] using congrArg (List.cons true) ih

theorem unary_slide (n : ℕ) (out : List Bool) :
    unaryEncodeNat n ++ true :: out = true :: unaryEncodeNat n ++ out := by
  induction n <;> simp [unaryEncodeNat, *]

def firstCount (w : List InputSymbol) : ℕ :=
  (w.filterMap TM2PairProjections.takeLeft).length

def secondCount (w : List InputSymbol) : ℕ :=
  (w.filterMap TM2PairProjections.takeRight).length

theorem scan_step_left (reg : Registers) (r : Bool) (w : List InputSymbol)
    (a b t : ℕ) (out : List Bool) :
    advance (some (cfg .scan reg (.left r :: w) a b t out)) =
      some (cfg .scan (some (.left r), reg.2) w (a + 1) b t out) := by
  simp [advance, cfg, program, step, stepAux, stackContents, isLeft, isRight,
    update_input, update_first_push]

theorem scan_step_right (reg : Registers) (r : Bool) (w : List InputSymbol)
    (a b t : ℕ) (out : List Bool) :
    advance (some (cfg .scan reg (.right r :: w) a b t out)) =
      some (cfg .scan (some (.right r), reg.2) w a (b + 1) t out) := by
  simp [advance, cfg, program, step, stepAux, stackContents, isLeft, isRight,
    update_input, update_second_push]

theorem scan_step_sep (reg : Registers) (w : List InputSymbol)
    (a b t : ℕ) (out : List Bool) :
    advance (some (cfg .scan reg (.sep :: w) a b t out)) =
      some (cfg .scan (some .sep, reg.2) w a b t out) := by
  simp [advance, cfg, program, step, stepAux, stackContents, isLeft, isRight, update_input]

theorem scan_step_nil (reg : Registers) (a b t : ℕ) (out : List Bool) :
    advance (some (cfg .scan reg [] a b t out)) =
      some (cfg .outer (none, false) [] a b t out) := by
  simp [advance, cfg, program, step, stepAux, stackContents, update_input]

theorem scan_run (reg : Registers) (w : List InputSymbol)
    (a b t : ℕ) (out : List Bool) :
    advance^[w.length + 1] (some (cfg .scan reg w a b t out)) =
      some (cfg .outer (none, false) [] (a + firstCount w) (b + secondCount w) t out) := by
  induction w generalizing reg a b with
  | nil => simpa [firstCount, secondCount] using scan_step_nil reg a b t out
  | cons r w ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    cases r with
    | left x =>
      rw [scan_step_left]
      simpa [firstCount, secondCount, TM2PairProjections.takeLeft, TM2PairProjections.takeRight,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (some (.left x), reg.2) (a + 1) b
    | right x =>
      rw [scan_step_right]
      simpa [firstCount, secondCount, TM2PairProjections.takeLeft, TM2PairProjections.takeRight,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (some (.right x), reg.2) a (b + 1)
    | sep =>
      rw [scan_step_sep]
      simpa [firstCount, secondCount, TM2PairProjections.takeLeft, TM2PairProjections.takeRight] using
        ih (some .sep, reg.2) a b

def inputWord (a b : ℕ) : List InputSymbol :=
  (unaryEncodeNat a).map PairSymbol.left ++
    PairSymbol.sep :: (unaryEncodeNat b).map PairSymbol.right

theorem unary_length (n : ℕ) : (unaryEncodeNat n).length = n := by
  induction n <;> simp [unaryEncodeNat, *]

theorem inputWord_firstCount (a b : ℕ) : firstCount (inputWord a b) = a := by
  rw [firstCount, inputWord, TM2PairProjections.takeLeft_join, unary_length]

theorem inputWord_secondCount (a b : ℕ) : secondCount (inputWord a b) = b := by
  rw [secondCount, inputWord, TM2PairProjections.takeRight_join, unary_length]

theorem inputWord_length (a b : ℕ) : (inputWord a b).length = a + b + 1 := by
  simp [inputWord, unary_length, Nat.add_assoc]

theorem outer_step_succ (reg : Registers) (w : List InputSymbol)
    (a b t : ℕ) (out : List Bool) :
    advance (some (cfg .outer reg w (a + 1) b t out)) =
      some (cfg .inner (reg.1, true) w a b t out) := by
  simp [advance, cfg, program, step, stepAux, stackContents, unaryEncodeNat, update_first]

theorem outer_step_zero (reg : Registers) (w : List InputSymbol)
    (b t : ℕ) (out : List Bool) :
    advance (some (cfg .outer reg w 0 b t out)) =
      some (cfg .clear (reg.1, false) w 0 b t out) := by
  simp [advance, cfg, program, step, stepAux, stackContents, unaryEncodeNat]

theorem inner_step_succ (reg : Registers) (w : List InputSymbol)
    (a b t : ℕ) (out : List Bool) :
    advance (some (cfg .inner reg w a (b + 1) t out)) =
      some (cfg .inner (reg.1, true) w a b (t + 1) (true :: out)) := by
  simp [advance, cfg, step, program, stepAux, stackContents,
    unaryEncodeNat, update_second, update_buffer_push, update_output]

theorem inner_step_zero (reg : Registers) (w : List InputSymbol)
    (a t : ℕ) (out : List Bool) :
    advance (some (cfg .inner reg w a 0 t out)) =
      some (cfg .restore (reg.1, false) w a 0 t out) := by
  simp [advance, cfg, program, step, stepAux, stackContents, unaryEncodeNat]

theorem restore_step_succ (reg : Registers) (w : List InputSymbol)
    (a b t : ℕ) (out : List Bool) :
    advance (some (cfg .restore reg w a b (t + 1) out)) =
      some (cfg .restore (reg.1, true) w a (b + 1) t out) := by
  simp [advance, cfg, step, program, stepAux, stackContents,
    unaryEncodeNat, update_buffer, update_second_push]

theorem restore_step_zero (reg : Registers) (w : List InputSymbol)
    (a b : ℕ) (out : List Bool) :
    advance (some (cfg .restore reg w a b 0 out)) =
      some (cfg .outer (none, false) w a b 0 out) := by
  simp [advance, cfg, program, step, stepAux, stackContents, unaryEncodeNat]

theorem clear_step_succ (reg : Registers) (w : List InputSymbol)
    (a b t : ℕ) (out : List Bool) :
    advance (some (cfg .clear reg w a (b + 1) t out)) =
      some (cfg .clear (reg.1, true) w a b t out) := by
  simp [advance, cfg, program, step, stepAux, stackContents, unaryEncodeNat, update_second]

theorem clear_step_zero (reg : Registers) (w : List InputSymbol)
    (a t : ℕ) (out : List Bool) :
    advance (some (cfg .clear reg w a 0 t out)) =
      some (cfg .finish (none, false) w a 0 t out) := by
  simp [advance, cfg, program, step, stepAux, stackContents, unaryEncodeNat]

theorem inner_run (reg : Registers) (w : List InputSymbol) (a b t : ℕ) (out : List Bool) :
    advance^[b + 1] (some (cfg .inner reg w a b t out)) =
      some (cfg .restore (reg.1, false) w a 0 (t + b) (unaryEncodeNat b ++ out)) := by
  induction b generalizing reg t out with
  | zero => simpa [unaryEncodeNat] using inner_step_zero reg w a t out
  | succ b ih =>
    rw [show (b + 1) + 1 = (b + 1) + 1 by rfl, Function.iterate_succ_apply, inner_step_succ]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, unaryEncodeNat, unary_slide] using
      ih (reg.1, true) (t + 1) (true :: out)

theorem restore_run (reg : Registers) (w : List InputSymbol) (a b t : ℕ) (out : List Bool) :
    advance^[t + 1] (some (cfg .restore reg w a b t out)) =
      some (cfg .outer (none, false) w a (b + t) 0 out) := by
  induction t generalizing reg b with
  | zero => simpa using restore_step_zero reg w a b out
  | succ t ih =>
    rw [Function.iterate_succ_apply, restore_step_succ]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (reg.1, true) (b + 1)

theorem clear_run (reg : Registers) (w : List InputSymbol) (a b t : ℕ) (out : List Bool) :
    advance^[b + 1] (some (cfg .clear reg w a b t out)) =
      some (cfg .finish (none, false) w a 0 t out) := by
  induction b generalizing reg with
  | zero => exact clear_step_zero reg w a t out
  | succ b ih =>
    rw [Function.iterate_succ_apply, clear_step_succ]
    exact ih (reg.1, true)

theorem outer_cycle (w : List InputSymbol) (a b : ℕ) (out : List Bool) :
    advance^[2 * b + 3] (some (cfg .outer (none, false) w (a + 1) b 0 out)) =
      some (cfg .outer (none, false) w a b 0 (unaryEncodeNat b ++ out)) := by
  rw [show 2 * b + 3 = (b + 1) + ((b + 1) + 1) by omega, Function.iterate_add_apply,
    Function.iterate_add_apply advance (b + 1) 1]
  simp only [Function.iterate_one]
  rw [outer_step_succ, inner_run]
  simpa using restore_run (none, false) w a 0 b (unaryEncodeNat b ++ out)

theorem outer_run (w : List InputSymbol) (a b : ℕ) (out : List Bool) :
    advance^[a * (2 * b + 3) + 1] (some (cfg .outer (none, false) w a b 0 out)) =
      some (cfg .clear (none, false) w 0 b 0 (unaryEncodeNat (a * b) ++ out)) := by
  induction a generalizing out with
  | zero => simpa [unaryEncodeNat] using outer_step_zero (none, false) w b 0 out
  | succ a ih =>
    rw [show (a + 1) * (2 * b + 3) + 1 = (a * (2 * b + 3) + 1) + (2 * b + 3) by
        simp only [Nat.add_mul, Nat.one_mul]; omega,
      Function.iterate_add_apply, outer_cycle, ih]
    simp only [← List.append_assoc, ← unary_append, Nat.succ_mul]

theorem program_run (a b : ℕ) :
    advance^[(inputWord a b).length + a * (2 * b + 3) + b + 4]
      (some (cfg .scan (none, false) (inputWord a b) 0 0 0 [])) =
        some ⟨none, (none, false), stackContents [] 0 0 0 (unaryEncodeNat (a * b))⟩ := by
  rw [show (inputWord a b).length + a * (2 * b + 3) + b + 4 =
      (a * (2 * b + 3) + b + 3) + ((inputWord a b).length + 1) by omega,
    Function.iterate_add_apply, scan_run]
  simp only [inputWord_firstCount, inputWord_secondCount, Nat.zero_add]
  rw [show a * (2 * b + 3) + b + 3 = (b + 2) + (a * (2 * b + 3) + 1) by omega,
    Function.iterate_add_apply, outer_run]
  simp only [List.append_nil]
  rw [show b + 2 = (b + 1) + 1 by omega, Function.iterate_succ_apply', clear_run]
  simp [advance, cfg, program, step, stepAux]

def machine : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Phase
  main := .scan
  σ := Registers
  initialState := (none, false)
  Γk₀Fin := inferInstanceAs (Fintype InputSymbol)
  m := program

def machine_outputs (a b : ℕ) : TM2OutputsInTime machine (inputWord a b)
    (some (unaryEncodeNat (a * b))) (2 * (a + b + 1) ^ 2 + 4 * (a + b + 1) + 5) := by
  have hi : initList machine (inputWord a b) =
      cfg .scan (none, false) (inputWord a b) 0 0 0 [] := by
    apply congrArg (fun S : ∀ k, List (Alphabet k) =>
      (⟨some .scan, (none, false), S⟩ : Cfg Alphabet Phase Registers))
    funext k
    cases k <;> rfl
  have ho : haltList machine (unaryEncodeNat (a * b)) =
      (⟨none, (none, false), stackContents [] 0 0 0 (unaryEncodeNat (a * b))⟩ :
        Cfg Alphabet Phase Registers) := by
    apply congrArg (fun S : ∀ k, List (Alphabet k) =>
      (⟨none, (none, false), S⟩ : Cfg Alphabet Phase Registers))
    funext k
    cases k <;> rfl
  refine ⟨⟨(inputWord a b).length + a * (2 * b + 3) + b + 4, ?_⟩, ?_⟩
  · change advance^[_] (some (initList machine (inputWord a b))) =
      some (haltList machine (unaryEncodeNat (a * b)))
    rw [hi, ho]
    exact program_run a b
  · change (inputWord a b).length + a * (2 * b + 3) + b + 4 ≤
      2 * (a + b + 1) ^ 2 + 4 * (a + b + 1) + 5
    rw [inputWord_length]
    have ha : a ≤ a + b + 1 := by omega
    have hb : b ≤ a + b + 1 := by omega
    have hab := Nat.mul_le_mul ha hb
    nlinarith

/-- A quadratic-time unary multiplier with both inputs in the existing tagged
pair format. Every auxiliary stack is empty and the registers are reset at halt. -/
noncomputable def unaryMulComputable :
    TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)
      unaryFinEncodingNat (fun ab : ℕ × ℕ => ab.1 * ab.2) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 4 * Polynomial.X + Polynomial.C 5
  outputsFun ab := by
    obtain ⟨a, b⟩ := ab
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    change TM2OutputsInTime machine (List.map id (inputWord a b))
      (some (List.map id (unaryEncodeNat (a * b))))
      (2 * (inputWord a b).length ^ 2 + 4 * (inputWord a b).length + 5)
    simpa only [List.map_id, inputWord_length]
      using machine_outputs a b

end ProteinFolding.PerfectUnaryMultiplication

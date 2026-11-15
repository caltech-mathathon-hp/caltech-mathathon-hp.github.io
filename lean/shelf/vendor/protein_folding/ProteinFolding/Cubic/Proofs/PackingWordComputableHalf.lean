import ProteinFolding.Common.TM2WordRepeat

/-! A one-pass unary halving machine for the paired-H face word generator.
The finite parity register alternates on each token; every second token emits
one output token. The final empty-input step resets the parity register. -/

namespace ProteinFolding.CubicPacking.UnaryHalf

open Computability Turing TM2

inductive Slot where
  | input | output
  deriving DecidableEq, Fintype

abbrev State := Bool × Bool
abbrev Alphabet (_ : Slot) := Bool

def contents (n m : ℕ) : Slot → List Bool
  | .input => unaryEncodeNat n
  | .output => unaryEncodeNat m

theorem update_input (n n' m : ℕ) :
    Function.update (contents n m) .input (unaryEncodeNat n') = contents n' m := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_output (n m m' : ℕ) :
    Function.update (contents n m) .output (unaryEncodeNat m') = contents n m' := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_output_push (n m : ℕ) :
    Function.update (contents n m) .output (true :: unaryEncodeNat m) = contents n (m + 1) :=
  update_output n m (m + 1)

def program (_ : Unit) : Stmt Alphabet Unit State :=
  .pop .input (fun st head => (st.1, head.isSome))
    (.branch Prod.snd
      (.branch Prod.fst
        (.push .output (fun _ => true) (.load (fun _ => (false, false)) (.goto (fun _ => ()))))
        (.load (fun _ => (true, false)) (.goto (fun _ => ()))))
      (.load (fun _ => (false, false)) .halt))

def cfg (p : Bool) (n m : ℕ) : Cfg Alphabet Unit State :=
  ⟨some (), (p, false), contents n m⟩

def halted (m : ℕ) : Cfg Alphabet Unit State := ⟨none, (false, false), contents 0 m⟩

def run (n : ℕ) (q : Cfg Alphabet Unit State) : Option (Cfg Alphabet Unit State) :=
  (fun x : Option (Cfg Alphabet Unit State) => x.bind (step program))^[n] (some q)

theorem step_false (n m : ℕ) : step program (cfg false (n + 1) m) = some (cfg true n m) := by
  simp [cfg, program, step, stepAux, contents, unaryEncodeNat, update_input]

theorem step_true (n m : ℕ) : step program (cfg true (n + 1) m) = some (cfg false n (m + 1)) := by
  simp [cfg, program, step, stepAux, contents, unaryEncodeNat, update_input, update_output_push]

theorem step_nil (p : Bool) (m : ℕ) : step program (cfg p 0 m) = some (halted m) := by
  simp [cfg, halted, program, step, stepAux, contents, unaryEncodeNat]

theorem run_step {q q' : Cfg Alphabet Unit State} (h : step program q = some q') (n : ℕ) :
    run (n + 1) q = run n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem program_run (n m : ℕ) (p : Bool) :
    run (n + 1) (cfg p n m) = some (halted (m + (n + p.toNat) / 2)) := by
  induction n generalizing m p with
  | zero =>
    cases p <;> simpa [run] using step_nil _ m
  | succ n ih =>
    cases p with
    | false =>
      rw [run_step (step_false n m), ih]
      rfl
    | true =>
      rw [run_step (step_true n m), ih]
      have he : m + 1 + (n + Bool.toNat false) / 2 = m + (n + 1 + Bool.toNat true) / 2 := by
        simp only [Bool.toNat_false, Bool.toNat_true]
        omega
      rw [he]

def machine : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Unit
  main := ()
  σ := State
  initialState := (false, false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

def machine_outputs (n : ℕ) : TM2OutputsInTime machine (unaryEncodeNat n)
    (some (unaryEncodeNat (n / 2))) (n + 1) := by
  have hi : initList machine (unaryEncodeNat n) = cfg false n 0 := by
    apply congrArg (fun S => (⟨some (), (false, false), S⟩ : Cfg Alphabet Unit State))
    funext k; cases k <;> rfl
  have ho : haltList machine (unaryEncodeNat (n / 2)) = halted (n / 2) := by
    apply congrArg (fun S => (⟨none, (false, false), S⟩ : Cfg Alphabet Unit State))
    funext k; cases k <;> rfl
  refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
  change run (n + 1) (initList machine _) = some (haltList machine _)
  rw [hi, ho]
  simpa only [Bool.toNat_false, Nat.add_zero, Nat.zero_add] using program_run n 0 false

/-- Floor division by two on the exact unary encoding, in X+1 TM2 steps. -/
noncomputable def computable : TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat
    (fun n : ℕ => n / 2) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + Polynomial.C 1
  outputsFun n := by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    change TM2OutputsInTime machine (List.map id (unaryEncodeNat n))
      (some (List.map id (unaryEncodeNat (n / 2)))) ((unaryEncodeNat n).length + 1)
    simpa only [List.map_id, TM2WordRepeat.unary_length] using machine_outputs n

end ProteinFolding.CubicPacking.UnaryHalf

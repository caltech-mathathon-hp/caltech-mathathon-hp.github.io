import ProteinFolding.Tetrahedral.ReductionTM2Basics

namespace ProteinFolding.Tetrahedral.ReductionTM2.Third

open Computability Turing TM2

inductive Slot where
  | input | output
  deriving DecidableEq, Fintype
abbrev State := Fin 3 × Bool
abbrev Alphabet (_ : Slot) := Bool
def advance (p : Fin 3) : Fin 3 := ⟨(p.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
def contents (n m : ℕ) : Slot → List Bool
  | .input => unaryEncodeNat n
  | .output => unaryEncodeNat m
theorem update_input (n n' m : ℕ) :
    Function.update (contents n m) .input (unaryEncodeNat n') = contents n' m := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]
theorem update_output_push (n m : ℕ) :
    Function.update (contents n m) .output (true :: unaryEncodeNat m) = contents n (m + 1) := by
  funext k; cases k <;> simp [contents, Function.update_of_ne, unaryEncodeNat]
def program (_ : Unit) : Stmt Alphabet Unit State :=
  .pop .input (fun st head => (st.1, head.isSome))
    (.branch Prod.snd
      (.branch (fun st => st.1.val == 2)
        (.push .output (fun _ => true) (.load (fun _ => (0, false)) (.goto (fun _ => ()))))
        (.load (fun st => (advance st.1, false)) (.goto (fun _ => ()))))
      (.load (fun _ => (0, false)) .halt))
def cfg (p : Fin 3) (n m : ℕ) : Cfg Alphabet Unit State := ⟨some (), (p, false), contents n m⟩
def halted (m : ℕ) : Cfg Alphabet Unit State := ⟨none, (0, false), contents 0 m⟩
def run (n : ℕ) (q : Cfg Alphabet Unit State) : Option (Cfg Alphabet Unit State) :=
  (fun q : Option (Cfg Alphabet Unit State) => q.bind (Turing.TM2.step program))^[n] (some q)
theorem run_step {q q' : Cfg Alphabet Unit State} (h : Turing.TM2.step program q = some q') (n : ℕ) :
    run (n + 1) q = run n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]
theorem step_succ (p : Fin 3) (n m : ℕ) :
    Turing.TM2.step program (cfg p (n + 1) m) = some (cfg (advance p) n (m + if p.val = 2 then 1 else 0)) := by
  fin_cases p <;> simp [cfg, program, advance, Turing.TM2.step, stepAux, contents,
    unaryEncodeNat, update_input, update_output_push]
theorem step_nil (p : Fin 3) (m : ℕ) : Turing.TM2.step program (cfg p 0 m) = some (halted m) := by
  simp [cfg, program, halted, Turing.TM2.step, stepAux, contents, unaryEncodeNat]
theorem program_run (n m : ℕ) (p : Fin 3) :
    run (n + 1) (cfg p n m) = some (halted (m + (n + p.val) / 3)) := by
  induction n generalizing m p with
  | zero =>
    have hp : p.val < 3 := p.isLt
    have he : p.val / 3 = 0 := by omega
    simpa [run, he] using step_nil p m
  | succ n ih =>
    rw [run_step (step_succ p n m), ih]
    have he : m + (if p.val = 2 then 1 else 0) + (n + (advance p).val) / 3 = m + (n + 1 + p.val) / 3 := by
      fin_cases p <;> simp only [advance] <;> norm_num <;> omega
    rw [he]
def machine : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Unit
  main := ()
  σ := State
  initialState := (0, false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program
def machine_outputs (n : ℕ) :
    TM2OutputsInTime machine (unaryEncodeNat n) (some (unaryEncodeNat (n / 3))) (n + 1) := by
  have hi : initList machine (unaryEncodeNat n) = cfg 0 n 0 := by
    apply congrArg (fun S => (⟨some (), (0, false), S⟩ : Cfg Alphabet Unit State))
    funext k; cases k <;> rfl
  have ho : haltList machine (unaryEncodeNat (n / 3)) = halted (n / 3) := by
    apply congrArg (fun S => (⟨none, (0, false), S⟩ : Cfg Alphabet Unit State))
    funext k; cases k <;> rfl
  refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
  change run (n + 1) (initList machine _) = some (haltList machine _)
  rw [hi, ho]
  simpa only [Fin.val_zero, Nat.add_zero, Nat.zero_add] using program_run n 0 0
noncomputable def computable : TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat (fun n => n / 3) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + Polynomial.C 1
  outputsFun n := by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    change TM2OutputsInTime machine (List.map id (unaryEncodeNat n))
      (some (List.map id (unaryEncodeNat (n / 3)))) ((unaryEncodeNat n).length + 1)
    simpa only [List.map_id, TM2WordRepeat.unary_length] using machine_outputs n

end ProteinFolding.Tetrahedral.ReductionTM2.Third

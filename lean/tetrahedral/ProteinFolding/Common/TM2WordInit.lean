import ProteinFolding.Common.TM2PairProjections
import ProteinFolding.Common.TM2Constants

/-! Removing the last symbol of a finite word by an actual linear-time TM2.
A one-symbol lookbehind register delays output until the following symbol is
seen. The final cached symbol is discarded; a transfer restores output order.
The construction also covers the empty alphabet and empty input word. -/

namespace ProteinFolding.TM2WordInit

open Computability Turing TM2

inductive Slot where
  | input | buffer | output
  deriving DecidableEq, Fintype

inductive Phase where
  | scan | restore | finish
  deriving DecidableEq, Fintype

abbrev Alphabet (A : Type) (_ : Slot) := A
abbrev State (A : Type) := Option A × Option A

variable {A : Type}

def contents (u v o : List A) : Slot → List A
  | .input => u
  | .buffer => v
  | .output => o

theorem update_input (u u' v o : List A) :
    Function.update (contents u v o) .input u' = contents u' v o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_buffer (u v v' o : List A) :
    Function.update (contents u v o) .buffer v' = contents u v' o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_output (u v o o' : List A) :
    Function.update (contents u v o) .output o' = contents u v o' := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

def cfg (phase : Phase) (reg : State A) (u v o : List A) : Cfg (Alphabet A) Phase (State A) :=
  ⟨some phase, reg, contents u v o⟩

def program (A : Type) [Inhabited A] : Phase → Stmt (Alphabet A) Phase (State A)
  | .scan => .pop .input (fun st head => (st.1, head))
      (.branch (fun st => st.2.isSome)
        (.branch (fun st => st.1.isSome)
          (.push .buffer (fun st => st.1.getD default)
            (.load (fun st => (st.2, none)) (.goto (fun _ => .scan))))
          (.load (fun st => (st.2, none)) (.goto (fun _ => .scan))))
        (.load (fun _ => (none, none)) (.goto (fun _ => .restore))))
  | .restore => TM2Transfer.transferStmt .buffer .output id .restore .finish
  | .finish => .halt

def run (A : Type) [Inhabited A] (n : ℕ) (q : Cfg (Alphabet A) Phase (State A)) :
    Option (Cfg (Alphabet A) Phase (State A)) :=
  (fun x : Option (Cfg (Alphabet A) Phase (State A)) => x.bind (step (program A)))^[n] (some q)

theorem run_step [Inhabited A] {q q' : Cfg (Alphabet A) Phase (State A)}
    (h : step (program A) q = some q') (n : ℕ) : run A (n + 1) q = run A n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add [Inhabited A] {q q' : Cfg (Alphabet A) Phase (State A)} {n : ℕ}
    (h : run A n q = some q') (m : ℕ) : run A (n + m) q = run A m q' := by
  rw [Nat.add_comm n m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg (Alphabet A) Phase (State A)) => x.bind (step (program A)))^[n] (some q) =
      some q' from h]

def delayed : Option A → List A → List A
  | _, [] => []
  | none, a :: u => delayed (some a) u
  | some b, a :: u => b :: delayed (some a) u

theorem delayed_none (u : List A) : delayed none u = u.dropLast := by
  have h (p : Option A) (u : List A) :
      delayed p u = (p.toList ++ u).dropLast := by
    induction u generalizing p with
    | nil => cases p <;> rfl
    | cons a u ih => cases p <;> simp [delayed, ih]
  exact h none u

section Inhabited
variable [Inhabited A]

theorem scan_step_none (a : A) (u v o : List A) :
    step (program A) (cfg .scan (none, none) (a :: u) v o) =
      some (cfg .scan (some a, none) u v o) := by
  simp [cfg, program, step, stepAux, contents, update_input]

theorem scan_step_some (a b : A) (u v o : List A) :
    step (program A) (cfg .scan (some b, none) (a :: u) v o) =
      some (cfg .scan (some a, none) u (b :: v) o) := by
  simp [cfg, program, step, stepAux, contents, update_input, update_buffer]

theorem scan_step_nil (p : Option A) (v o : List A) :
    step (program A) (cfg .scan (p, none) [] v o) =
      some (cfg .restore (none, none) [] v o) := by
  simp [cfg, program, step, stepAux, contents]

theorem scan_run (p : Option A) (u v o : List A) :
    run A (u.length + 1) (cfg .scan (p, none) u v o) =
      some (cfg .restore (none, none) [] ((delayed p u).reverse ++ v) o) := by
  induction u generalizing p v with
  | nil => simpa [run, delayed] using scan_step_nil p v o
  | cons a u ih =>
    cases p with
    | none =>
      rw [List.length_cons, run_step (scan_step_none a u v o)]
      exact ih (some a) v
    | some b =>
      rw [List.length_cons, run_step (scan_step_some a b u v o)]
      simpa [delayed, List.reverse_cons, List.append_assoc] using ih (some a) (b :: v)

omit [Inhabited A] in
theorem transferCfg_eq (phase : Phase) (reg : State A) (u v o : List A) :
    TM2Transfer.transferCfg (Γ := Alphabet A) .buffer .output phase reg.1 reg.2
      (contents u [] []) v o = cfg phase reg u v o := by
  apply congrArg (fun S => (⟨some phase, reg, S⟩ : Cfg (Alphabet A) Phase (State A)))
  funext k; cases k <;> simp [TM2Transfer.setStacks, contents]

theorem restore_run (reg : State A) (u v o : List A) :
    run A (v.length + 1) (cfg .restore reg u v o) =
      some (cfg .finish (reg.1, none) u [] (v.reverse ++ o)) := by
  have h := TM2Transfer.transfer_run (Γ := Alphabet A) (Λ := Phase) (σ := Option A)
    .buffer .output (by decide) id .restore .finish (program A) rfl reg.1 reg.2 (contents u [] []) v o
  simp only [List.map_id, transferCfg_eq] at h
  exact h.trans (congrArg some (transferCfg_eq .finish (reg.1, none) u [] (v.reverse ++ o)))

def halted (o : List A) : Cfg (Alphabet A) Phase (State A) :=
  ⟨none, (none, none), contents [] [] o⟩

theorem program_run (u : List A) :
    run A (u.length + u.dropLast.length + 3) (cfg .scan (none, none) u [] []) =
      some (halted u.dropLast) := by
  have hs := scan_run (none : Option A) u [] []
  simp only [delayed_none, List.append_nil] at hs
  rw [show u.length + u.dropLast.length + 3 =
    (u.length + 1) + ((u.dropLast.reverse.length + 1) + 1) by simp; omega,
    run_add hs]
  rw [run_add (restore_run (none, none) [] u.dropLast.reverse [])]
  simp [run, cfg, halted, program, step, stepAux]

def machine (A : Type) [Fintype A] [Inhabited A] : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A
  Λ := Phase
  main := .scan
  σ := State A
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype A)
  m := program A

def machine_outputs [Fintype A] (u : List A) :
    TM2OutputsInTime (machine A) u (some u.dropLast) (2 * u.length + 3) := by
  have hi : initList (machine A) u = cfg .scan (none, none) u [] [] := by
    apply congrArg (fun S => (⟨some .scan, (none, none), S⟩ : Cfg (Alphabet A) Phase (State A)))
    funext k; cases k <;> rfl
  have ho : haltList (machine A) u.dropLast = halted u.dropLast := by
    apply congrArg (fun S => (⟨none, (none, none), S⟩ : Cfg (Alphabet A) Phase (State A)))
    funext k; cases k <;> rfl
  refine ⟨⟨u.length + u.dropLast.length + 3, ?_⟩, ?_⟩
  · change run A _ (initList (machine A) _) = some (haltList (machine A) _)
    rw [hi, ho]
    exact program_run u
  · simp only [List.length_dropLast]
    omega

noncomputable def inhabitedComputable (A : Type) [Fintype A] [Inhabited A] :
    TM2ComputableInPolyTime (wordEncoding A) (wordEncoding A) (fun u => u.dropLast) where
  tm := machine A
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun u := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime (machine A) (List.map id u) (some (List.map id u.dropLast)) (2 * u.length + 3)
    simpa only [List.map_id] using machine_outputs u

end Inhabited

noncomputable def computable (A : Type) [Fintype A] :
    TM2ComputableInPolyTime (wordEncoding A) (wordEncoding A) (fun u => u.dropLast) := by
  classical
  by_cases h : Nonempty A
  · letI : Inhabited A := ⟨Classical.choice h⟩
    exact inhabitedComputable A
  · have he (u : List A) : u = [] := by
      cases u with
      | nil => rfl
      | cons a u => exact False.elim (h ⟨a⟩)
    have hf : (fun u : List A => u.dropLast) = fun _ => [] := by funext u; rw [he u]; rfl
    rw [hf]
    exact TM2Constants.constantComputable _ (wordEncoding A) []

end ProteinFolding.TM2WordInit

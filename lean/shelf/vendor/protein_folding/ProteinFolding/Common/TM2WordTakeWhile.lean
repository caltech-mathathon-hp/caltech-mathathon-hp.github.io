import ProteinFolding.Common.TM2Transfer

/-! A finite TM2 for a word prefix selected by a fixed finite-alphabet
predicate. The machine drains the rest of the input after the first failure,
restores the prefix's order, clears its buffer and resets its internal state.
-/

namespace ProteinFolding.TM2WordTakeWhile

open Computability Turing TM2

inductive Slot where
  | input | buffer | output
  deriving DecidableEq, Fintype

inductive Phase where
  | scan | emit | finish
  deriving DecidableEq, Fintype

abbrev State (A : Type) := Bool × Option A

def initialState {A : Type} : State A := (true, none)

def contents {A : Type} (u v o : List A) : Slot → List A
  | .input => u
  | .buffer => v
  | .output => o

def cfg {A : Type} (phase : Phase) (active : Bool) (u v o : List A) :
    Cfg (fun _ : Slot => A) Phase (State A) := ⟨some phase, (active, none), contents u v o⟩

def program {A : Type} [Inhabited A] (p : A → Bool) :
    Phase → Stmt (fun _ : Slot => A) Phase (State A)
  | .scan => .pop .input (fun st h => (st.1, h))
    (.branch (fun st => st.2.isSome)
      (.branch (fun st => st.1 && p (st.2.getD default))
        (.push .buffer (fun st => st.2.getD default)
          (.load (fun _ => (true, none)) (.goto (fun _ => .scan))))
        (.load (fun _ => (false, none)) (.goto (fun _ => .scan))))
      (.goto (fun _ => .emit)))
  | .emit => TM2Transfer.transferStmt (Γ := fun _ : Slot => A) (σ := Bool)
      Slot.buffer Slot.output id Phase.emit Phase.finish
  | .finish => .load (fun _ => initialState) .halt

def run {A : Type} [Inhabited A] (p : A → Bool) (n : ℕ)
    (q : Cfg (fun _ : Slot => A) Phase (State A)) : Option (Cfg (fun _ : Slot => A) Phase (State A)) :=
  (fun x : Option (Cfg (fun _ : Slot => A) Phase (State A)) => x.bind (step (program p)))^[n] (some q)

theorem run_add {A : Type} [Inhabited A] (p : A → Bool)
    {q q' : Cfg (fun _ : Slot => A) Phase (State A)} {n : ℕ}
    (h : run p n q = some q') (m : ℕ) : run p (n + m) q = run p m q' := by
  rw [Nat.add_comm n m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg (fun _ : Slot => A) Phase (State A)) => x.bind (step (program p)))^[n]
      (some q) = some q' from h]

theorem run_step {A : Type} [Inhabited A] (p : A → Bool)
    {q q' : Cfg (fun _ : Slot => A) Phase (State A)}
    (h : step (program p) q = some q') (n : ℕ) : run p (n + 1) q = run p n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem update_input {A : Type} (u u' v o : List A) :
    Function.update (contents u v o) .input u' = contents u' v o := by
  funext k; cases k <;> simp [contents]

theorem update_buffer {A : Type} (u v v' o : List A) :
    Function.update (contents u v o) .buffer v' = contents u v' o := by
  funext k; cases k <;> simp [contents]

theorem scan_step_cons {A : Type} [Inhabited A] (p : A → Bool) (active : Bool)
    (a : A) (u v o : List A) :
    step (program p) (cfg .scan active (a :: u) v o) =
      some (if active && p a then cfg .scan true u (a :: v) o else cfg .scan false u v o) := by
  cases ha : active && p a <;>
    simp [cfg, program, step, stepAux, contents, ha]
  · exact update_input _ _ _ _
  · change Function.update (Function.update (contents (a :: u) v o) .input u) .buffer (a :: v) =
      contents u (a :: v) o
    rw [update_input, update_buffer]

theorem scan_step_nil {A : Type} [Inhabited A] (p : A → Bool) (active : Bool) (v o : List A) :
    step (program p) (cfg .scan active [] v o) = some (cfg .emit active [] v o) := by
  simp [cfg, program, step, stepAux, contents]

theorem scan_run {A : Type} [Inhabited A] (p : A → Bool) (active : Bool) (u v o : List A) :
    run p (u.length + 1) (cfg .scan active u v o) =
      some (cfg .emit (active && u.all p) []
        ((if active then u.takeWhile p else []).reverse ++ v) o) := by
  induction u generalizing active v with
  | nil => simpa only [List.length_nil, Nat.zero_add, run, Function.iterate_one, Option.bind_some,
      List.all_nil, Bool.and_true, List.takeWhile_nil, ite_self, List.reverse_nil, List.nil_append]
      using scan_step_nil p active v o
  | cons a u ih =>
    rw [List.length_cons, run_step p (scan_step_cons p active a u v o)]
    cases active <;> cases hp : p a <;> simp [hp, ih, List.reverse_cons, List.append_assoc]

theorem emit_contents {A : Type} (u v o : List A) :
    TM2Transfer.setStacks Slot.buffer Slot.output (contents u [] []) v o = contents u v o := by
  funext k; cases k <;> simp [TM2Transfer.setStacks, contents]

theorem emit_run {A : Type} [Inhabited A] (p : A → Bool) (active : Bool) (u v o : List A) :
    run p (v.length + 1) (cfg .emit active u v o) =
      some (cfg .finish active u [] (v.reverse ++ o)) := by
  have h := TM2Transfer.transfer_run (Γ := fun _ : Slot => A) Slot.buffer Slot.output (by decide)
    id Phase.emit Phase.finish (program p) rfl active none (contents u [] []) v o
  simpa only [run, cfg, TM2Transfer.transferCfg, emit_contents, List.map_id] using h

def halted {A : Type} (o : List A) : Cfg (fun _ : Slot => A) Phase (State A) :=
  ⟨none, initialState, contents [] [] o⟩

theorem finish_step {A : Type} [Inhabited A] (p : A → Bool) (active : Bool) (o : List A) :
    step (program p) (cfg .finish active [] [] o) = some (halted o) := rfl

theorem program_run {A : Type} [Inhabited A] (p : A → Bool) (u : List A) :
    run p (u.length + (u.takeWhile p).length + 3) (cfg .scan true u [] []) =
      some (halted (u.takeWhile p)) := by
  rw [show u.length + (u.takeWhile p).length + 3 =
      (u.length + 1) + (((u.takeWhile p).reverse.length + 1) + 1) by simp; omega]
  rw [run_add p (scan_run p true u [] [])]
  simp only [Bool.true_and, ite_true, List.append_nil]
  rw [run_add p (emit_run p (u.all p) [] (u.takeWhile p).reverse [])]
  simp only [List.reverse_reverse, List.append_nil]
  exact finish_step p (u.all p) (u.takeWhile p)

def machine (A : Type) [Fintype A] [Inhabited A] (p : A → Bool) : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := fun _ => A
  Λ := Phase
  main := .scan
  σ := State A
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program p

def machine_outputs {A : Type} [Fintype A] [Inhabited A] (p : A → Bool) (u : List A) :
    TM2OutputsInTime (machine A p) u (some (u.takeWhile p)) (2 * u.length + 3) := by
  have hi : initList (machine A p) u = cfg .scan true u [] [] := by
    apply congrArg (fun S => (⟨some .scan, initialState, S⟩ : Cfg (fun _ : Slot => A) Phase (State A)))
    funext k; cases k <;> rfl
  have ho : haltList (machine A p) (u.takeWhile p) = halted (u.takeWhile p) := by
    apply congrArg (fun S => (⟨none, initialState, S⟩ : Cfg (fun _ : Slot => A) Phase (State A)))
    funext k; cases k <;> rfl
  refine
    { steps := u.length + (u.takeWhile p).length + 3
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change run p _ (initList (machine A p) u) = some (haltList (machine A p) _)
    rw [hi, ho]
    exact program_run p u
  · have h : (u.takeWhile p).length ≤ u.length := (List.takeWhile_sublist (l := u) p).length_le
    omega

noncomputable def takeWhileComputable (A : Type) [Fintype A] [Inhabited A] (p : A → Bool) :
    TM2ComputableInPolyTime (wordEncoding A) (wordEncoding A) (List.takeWhile p) where
  tm := machine A p
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun u := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime (machine A p) (List.map id u)
      (some (List.map id (u.takeWhile p))) (2 * u.length + 3)
    simpa only [List.map_id] using machine_outputs p u

end ProteinFolding.TM2WordTakeWhile

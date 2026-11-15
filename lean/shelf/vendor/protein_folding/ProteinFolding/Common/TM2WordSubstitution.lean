import ProteinFolding.Common.TM2PairProjections

/-! Actual finite-alphabet word substitution. Each input letter has a fixed
finite output word. A finite dispatch statement pushes that word in one TM2
step; its size depends only on the fixed substitution, never on the input.
A final transfer restores word order and empties every auxiliary stack. -/

namespace ProteinFolding.TM2WordSubstitution

open Computability Turing TM2
open TM2PairProjections

variable {I O : Type} [DecidableEq I]

def pushWord (word : List O) (next : Stmt (Alphabet I O) Phase (Option I × Option O)) :
    Stmt (Alphabet I O) Phase (Option I × Option O) :=
  match word with
  | [] => next
  | a :: word => .push .buffer (fun _ => a) (pushWord word next)

omit [DecidableEq I] in
theorem pushWord_stepAux (word : List O)
    (next : Stmt (Alphabet I O) Phase (Option I × Option O))
    (reg : Option I × Option O) (u : List I) (v w : List O) :
    stepAux (pushWord word next) reg (stackContents u v w) =
      stepAux next reg (stackContents u (word.reverse ++ v) w) := by
  induction word generalizing v with
  | nil => rfl
  | cons a word ih =>
    simp only [pushWord, stepAux, stackContents, update_buffer]
    simpa [List.reverse_cons, List.append_assoc] using ih (a :: v)

def dispatch (convert : I → List O) : List I →
    Stmt (Alphabet I O) Phase (Option I × Option O)
  | [] => .goto (fun _ => .scan)
  | a :: symbols => .branch (fun st => decide (st.1 = some a))
      (pushWord (convert a) (.goto (fun _ => .scan))) (dispatch convert symbols)

theorem dispatch_stepAux (convert : I → List O) (symbols : List I) (a : I)
    (ha : a ∈ symbols) (cache : Option O) (u : List I) (v w : List O) :
    stepAux (dispatch convert symbols) (some a, cache) (stackContents u v w) =
      cfg .scan (some a, cache) u ((convert a).reverse ++ v) w := by
  induction symbols with
  | nil => simp at ha
  | cons b symbols ih =>
    by_cases he : a = b
    · subst b
      simp [dispatch, stepAux, pushWord_stepAux, cfg]
    · have ht : a ∈ symbols := (List.mem_cons.mp ha).resolve_left he
      simpa [dispatch, stepAux, he] using ih ht

noncomputable def program [Fintype I] [Inhabited O] (convert : I → List O) :
    Phase → Stmt (Alphabet I O) Phase (Option I × Option O)
  | .scan => .pop .input (fun st a => (a, st.2))
      (.branch (fun st => st.1.isSome)
        (dispatch convert Finset.univ.toList) (.goto (fun _ => .restore)))
  | .restore =>
      letI : Inhabited (Alphabet I O .buffer) := inferInstanceAs (Inhabited O)
      TM2Transfer.transferStmt (Γ := Alphabet I O) (Λ := Phase) (σ := Option I)
        .buffer .output id .restore .finish
  | .finish => .halt

theorem scan_step_cons [Fintype I] [Inhabited O] (convert : I → List O)
    (reg : Option I × Option O) (a : I) (u : List I) (v w : List O) :
    step (program convert) (cfg .scan reg (a :: u) v w) =
      some (cfg .scan (some a, reg.2) u ((convert a).reverse ++ v) w) := by
  simp only [step, cfg, program, stepAux, stackContents, List.head?_cons,
    List.tail_cons, update_input, Option.isSome_some, cond_true]
  exact congrArg some (dispatch_stepAux convert Finset.univ.toList a (by simp) reg.2 u v w)

theorem scan_step_nil [Fintype I] [Inhabited O] (convert : I → List O)
    (reg : Option I × Option O) (v w : List O) :
    step (program convert) (cfg .scan reg [] v w) =
      some (cfg .restore (none, reg.2) [] v w) := by
  simp [cfg, program, step, stepAux, stackContents, update_input]

theorem scan_run [Fintype I] [Inhabited O] (convert : I → List O)
    (reg : Option I × Option O) (u : List I) (v w : List O) :
    (fun x : Option (Cfg (Alphabet I O) Phase (Option I × Option O)) =>
      x.bind (step (program convert)))^[u.length + 1] (some (cfg .scan reg u v w)) =
      some (cfg .restore (none, reg.2) [] ((u.flatMap convert).reverse ++ v) w) := by
  induction u generalizing reg v with
  | nil => simpa using scan_step_nil convert reg v w
  | cons a u ih =>
    rw [List.length_cons, Nat.add_right_comm u.length 1 1, Function.iterate_succ_apply]
    simp only [Option.bind_some, scan_step_cons]
    simpa [List.flatMap_cons, List.reverse_append, List.append_assoc] using
      ih (some a, reg.2) ((convert a).reverse ++ v)

theorem restore_run [Fintype I] [Inhabited O] (convert : I → List O)
    (reg : Option I × Option O) (u : List I) (v w : List O) :
    (fun x : Option (Cfg (Alphabet I O) Phase (Option I × Option O)) =>
      x.bind (step (program convert)))^[v.length + 1] (some (cfg .restore reg u v w)) =
      some (cfg .finish (reg.1, none) u [] (v.reverse ++ w)) := by
  letI : Inhabited (Alphabet I O .buffer) := inferInstanceAs (Inhabited O)
  have h := TM2Transfer.transfer_run (Γ := Alphabet I O) (Λ := Phase) (σ := Option I)
    .buffer .output (by decide) id .restore .finish (program convert) rfl
    reg.1 reg.2 (stackContents u [] []) v w
  simp only [List.map_id, transferCfg_eq] at h
  exact h.trans (congrArg some (transferCfg_eq .finish (reg.1, none) u [] (v.reverse ++ w)))

theorem program_run [Fintype I] [Inhabited O] (convert : I → List O) (u : List I) :
    (fun x : Option (Cfg (Alphabet I O) Phase (Option I × Option O)) =>
      x.bind (step (program convert)))^[u.length + (u.flatMap convert).length + 3]
        (some (cfg .scan (none, none) u [] [])) =
      some ⟨none, (none, none), stackContents [] [] (u.flatMap convert)⟩ := by
  have hscan := scan_run convert (none, none) u [] []
  simp only [List.append_nil] at hscan
  rw [show u.length + (u.flatMap convert).length + 3 =
    ((u.flatMap convert).reverse.length + 1 + 1) + (u.length + 1) by simp; omega,
    Function.iterate_add_apply, hscan]
  rw [Function.iterate_succ_apply', restore_run]
  simp [cfg, program, step, stepAux]

omit [DecidableEq I] in
theorem flatMap_length_le (convert : I → List O) (C : ℕ)
    (hC : ∀ a, (convert a).length ≤ C) (u : List I) :
    (u.flatMap convert).length ≤ C * u.length := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have ha := hC a
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [Nat.mul_succ]
    omega

noncomputable def machine [Fintype I] [Fintype O] [Inhabited O] (convert : I → List O) : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet I O
  Λ := Phase
  main := .scan
  σ := Option I × Option O
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype I)
  m := program convert

noncomputable def machine_outputs [Fintype I] [Fintype O] [Inhabited O] (convert : I → List O)
    (C : ℕ) (hC : ∀ a, (convert a).length ≤ C) (u : List I) :
    TM2OutputsInTime (machine convert) u (some (u.flatMap convert)) ((C + 1) * u.length + 3) := by
  have hi : initList (machine convert) u = cfg .scan (none, none) u [] [] := by
    apply congrArg (fun S => (⟨some .scan, (none, none), S⟩ :
      Cfg (Alphabet I O) Phase (Option I × Option O)))
    funext k; cases k <;> rfl
  have ho : haltList (machine convert) (u.flatMap convert) =
      (⟨none, (none, none), stackContents [] [] (u.flatMap convert)⟩ :
        Cfg (Alphabet I O) Phase (Option I × Option O)) := by
    apply congrArg (fun S => (⟨none, (none, none), S⟩ :
      Cfg (Alphabet I O) Phase (Option I × Option O)))
    funext k; cases k <;> rfl
  refine
    { steps := u.length + (u.flatMap convert).length + 3
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · rw [hi]
    change _ = some (haltList (machine convert) _)
    rw [ho]
    exact program_run convert u
  · have h := flatMap_length_le convert C hC u
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Substituting fixed words is polynomial-time. The explicit bound C is a
constant of the fixed finite-alphabet substitution, independent of input. -/
noncomputable def flatMapComputable [Fintype I] [Fintype O] [Inhabited O]
    (convert : I → List O) (C : ℕ) (hC : ∀ a, (convert a).length ≤ C) :
    TM2ComputableInPolyTime (wordEncoding I) (wordEncoding O) (List.flatMap convert) where
  tm := machine convert
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C (C + 1) * Polynomial.X + Polynomial.C 3
  outputsFun u := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime (machine convert) (List.map id u)
      (some (List.map id (u.flatMap convert))) ((C + 1) * u.length + 3)
    simpa only [List.map_id] using machine_outputs convert C hC u

end ProteinFolding.TM2WordSubstitution

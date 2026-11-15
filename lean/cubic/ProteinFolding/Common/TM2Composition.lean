import ProteinFolding.Common.TM2Transfer

/-!
# Sequential composition of finite TM2 machines

The component stack sets are disjoint. A third stack reverses the intermediate
word twice before the second machine starts. Each component restores its own
initial state and clears its auxiliary stacks under mathlib's output convention.
-/

namespace ProteinFolding.TM2Composition

open Turing TM2

variable (a b : FinTM2)

abbrev Stack := a.K ⊕ (b.K ⊕ Unit)
abbrev Label := a.Λ ⊕ (b.Λ ⊕ Bool)
abbrev State := (a.σ × b.σ) × Option (a.Γ a.k₁)

def Alphabet : Stack a b → Type
  | .inl k => a.Γ k
  | .inr (.inl k) => b.Γ k
  | .inr (.inr _) => a.Γ a.k₁

def combinedStacks (S : ∀ k, List (a.Γ k)) (T : ∀ k, List (b.Γ k))
    (buffer : List (a.Γ a.k₁)) : ∀ k, List (Alphabet a b k)
  | .inl k => S k
  | .inr (.inl k) => T k
  | .inr (.inr _) => buffer

theorem stacks_update_first (S : ∀ k, List (a.Γ k)) (T : ∀ k, List (b.Γ k))
    (buffer : List (a.Γ a.k₁)) (k : a.K) (w : List (a.Γ k)) :
    Function.update (combinedStacks a b S T buffer) (.inl k) w =
      combinedStacks a b (Function.update S k w) T buffer := by
  funext i
  cases i with
  | inl i =>
    by_cases h : i = k
    · subst i; simp [combinedStacks]
    · simp [combinedStacks, h, Function.update_of_ne]
  | inr i => cases i <;> simp [combinedStacks, Function.update_of_ne]

theorem stacks_update_second (S : ∀ k, List (a.Γ k)) (T : ∀ k, List (b.Γ k))
    (buffer : List (a.Γ a.k₁)) (k : b.K) (w : List (b.Γ k)) :
    Function.update (combinedStacks a b S T buffer) (.inr (.inl k)) w =
      combinedStacks a b S (Function.update T k w) buffer := by
  funext i
  cases i with
  | inl i => simp [combinedStacks, Function.update_of_ne]
  | inr i =>
    cases i with
    | inl i =>
      by_cases h : i = k
      · subst i; simp [combinedStacks]
      · simp [combinedStacks, h, Function.update_of_ne]
    | inr i => simp [combinedStacks, Function.update_of_ne]

def firstCfg (t : b.σ) (reg : Option (a.Γ a.k₁))
    (T : ∀ k, List (b.Γ k)) (buffer : List (a.Γ a.k₁))
    (c : a.Cfg) : Cfg (Alphabet a b) (Label a b) (State a b) where
  l := c.l.elim (some (.inr (.inr false))) (fun l => some (.inl l))
  var := ((c.var, t), reg)
  stk := combinedStacks a b c.stk T buffer

def secondCfg (s : a.σ) (reg : Option (a.Γ a.k₁))
    (S : ∀ k, List (a.Γ k)) (buffer : List (a.Γ a.k₁))
    (c : b.Cfg) : Cfg (Alphabet a b) (Label a b) (State a b) where
  l := c.l.map (fun l => .inr (.inl l))
  var := ((s, c.var), reg)
  stk := combinedStacks a b S c.stk buffer

def firstStmt : Stmt a.Γ a.Λ a.σ → Stmt (Alphabet a b) (Label a b) (State a b)
  | .push k f q => .push (.inl k) (fun st => f st.1.1) (firstStmt q)
  | .peek k f q => .peek (.inl k) (fun st o => ((f st.1.1 o, st.1.2), st.2)) (firstStmt q)
  | .pop k f q => .pop (.inl k) (fun st o => ((f st.1.1 o, st.1.2), st.2)) (firstStmt q)
  | .load f q => .load (fun st => ((f st.1.1, st.1.2), st.2)) (firstStmt q)
  | .branch f q r => .branch (fun st => f st.1.1) (firstStmt q) (firstStmt r)
  | .goto f => .goto (fun st => .inl (f st.1.1))
  | .halt => .goto (fun _ => .inr (.inr false))

def secondStmt : Stmt b.Γ b.Λ b.σ → Stmt (Alphabet a b) (Label a b) (State a b)
  | .push k f q => .push (.inr (.inl k)) (fun st => f st.1.2) (secondStmt q)
  | .peek k f q => .peek (.inr (.inl k)) (fun st o => ((st.1.1, f st.1.2 o), st.2)) (secondStmt q)
  | .pop k f q => .pop (.inr (.inl k)) (fun st o => ((st.1.1, f st.1.2 o), st.2)) (secondStmt q)
  | .load f q => .load (fun st => ((st.1.1, f st.1.2), st.2)) (secondStmt q)
  | .branch f q r => .branch (fun st => f st.1.2) (secondStmt q) (secondStmt r)
  | .goto f => .goto (fun st => .inr (.inl (f st.1.2)))
  | .halt => .halt

theorem firstStmt_stepAux (q : Stmt a.Γ a.Λ a.σ) (s : a.σ) (t : b.σ)
    (reg : Option (a.Γ a.k₁)) (S : ∀ k, List (a.Γ k)) (T : ∀ k, List (b.Γ k))
    (buffer : List (a.Γ a.k₁)) :
    stepAux (firstStmt a b q) ((s, t), reg) (combinedStacks a b S T buffer) =
      firstCfg a b t reg T buffer (stepAux q s S) := by
  induction q generalizing s S with
  | push k f q ih =>
    simpa only [firstStmt, stepAux, combinedStacks, stacks_update_first] using ih s (Function.update S k (f s :: S k))
  | peek k f q ih => exact ih (f s (S k).head?) S
  | pop k f q ih =>
    simpa only [firstStmt, stepAux, combinedStacks, stacks_update_first] using ih (f s (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih (f s) S
  | branch f q r ihq ihr =>
    cases hf : f s
    · simpa [firstStmt, stepAux, hf, firstCfg] using ihr s S
    · simpa [firstStmt, stepAux, hf, firstCfg] using ihq s S
  | goto f => rfl
  | halt => rfl

theorem secondStmt_stepAux (q : Stmt b.Γ b.Λ b.σ) (s : a.σ) (t : b.σ)
    (reg : Option (a.Γ a.k₁)) (S : ∀ k, List (a.Γ k)) (T : ∀ k, List (b.Γ k))
    (buffer : List (a.Γ a.k₁)) :
    stepAux (secondStmt a b q) ((s, t), reg) (combinedStacks a b S T buffer) =
      secondCfg a b s reg S buffer (stepAux q t T) := by
  induction q generalizing t T with
  | push k f q ih =>
    simpa only [secondStmt, stepAux, combinedStacks, stacks_update_second] using ih t (Function.update T k (f t :: T k))
  | peek k f q ih => exact ih (f t (T k).head?) T
  | pop k f q ih =>
    simpa only [secondStmt, stepAux, combinedStacks, stacks_update_second] using ih (f t (T k).head?) (Function.update T k (T k).tail)
  | load f q ih => exact ih (f t) T
  | branch f q r ihq ihr =>
    cases hf : f t
    · simpa [secondStmt, stepAux, hf, secondCfg] using ihr t T
    · simpa [secondStmt, stepAux, hf, secondCfg] using ihq t T
  | goto f => rfl
  | halt => rfl

def program (bridge : a.Γ a.k₁ ≃ b.Γ b.k₀) (seed : Option (a.Γ a.k₁)) :
    Label a b → Stmt (Alphabet a b) (Label a b) (State a b)
  | .inl l => firstStmt a b (a.m l)
  | .inr (.inl l) => secondStmt a b (b.m l)
  | .inr (.inr false) => match seed with
    | none => .goto (fun _ => .inr (.inl b.main))
    | some x =>
      letI : Inhabited (Alphabet a b (.inl a.k₁)) := ⟨x⟩
      TM2Transfer.transferStmt (Γ := Alphabet a b) (Λ := Label a b) (σ := a.σ × b.σ)
        (.inl a.k₁) (.inr (.inr ())) id
        (.inr (.inr false)) (.inr (.inr true))
  | .inr (.inr true) => match seed with
    | none => .goto (fun _ => .inr (.inl b.main))
    | some x =>
      letI : Inhabited (Alphabet a b (.inr (.inr ()))) := ⟨x⟩
      TM2Transfer.transferStmt (Γ := Alphabet a b) (Λ := Label a b) (σ := a.σ × b.σ)
        (.inr (.inr ())) (.inr (.inl b.k₀)) bridge
        (.inr (.inr true)) (.inr (.inl b.main))

noncomputable def machine (bridge : a.Γ a.k₁ ≃ b.Γ b.k₀) (seed : Option (a.Γ a.k₁)) : FinTM2 := by
  letI := a.kFin
  letI := b.kFin
  letI := a.ΛFin
  letI := b.ΛFin
  letI := a.σFin
  letI := b.σFin
  letI := b.Γk₀Fin
  letI : Fintype (a.Γ a.k₁) := Fintype.ofEquiv (b.Γ b.k₀) bridge.symm
  exact
    { K := Stack a b
      k₀ := .inl a.k₀
      k₁ := .inr (.inl b.k₁)
      Γ := Alphabet a b
      Λ := Label a b
      main := .inl a.main
      σ := State a b
      initialState := ((a.initialState, b.initialState), none)
      Γk₀Fin := a.Γk₀Fin
      m := program a b bridge seed }

theorem first_step (bridge : a.Γ a.k₁ ≃ b.Γ b.k₀) (seed : Option (a.Γ a.k₁))
    (t : b.σ) (reg : Option (a.Γ a.k₁)) (T : ∀ k, List (b.Γ k))
    (buffer : List (a.Γ a.k₁)) (c d : a.Cfg) (hc : a.step c = some d) :
    (machine a b bridge seed).step (firstCfg a b t reg T buffer c) =
      some (firstCfg a b t reg T buffer d) := by
  obtain ⟨l, s, S⟩ := c
  cases l with
  | none => simp [FinTM2.step, step] at hc
  | some l =>
    have hd : stepAux (a.m l) s S = d := by simpa [FinTM2.step, step] using hc
    rw [← hd]
    simpa only [firstCfg, machine, FinTM2.step, Option.elim, step, program] using
      congrArg some (firstStmt_stepAux a b (a.m l) s t reg S T buffer)

theorem second_step (bridge : a.Γ a.k₁ ≃ b.Γ b.k₀) (seed : Option (a.Γ a.k₁))
    (s : a.σ) (reg : Option (a.Γ a.k₁)) (S : ∀ k, List (a.Γ k))
    (buffer : List (a.Γ a.k₁)) (c d : b.Cfg) (hc : b.step c = some d) :
    (machine a b bridge seed).step (secondCfg a b s reg S buffer c) =
      some (secondCfg a b s reg S buffer d) := by
  obtain ⟨l, t, T⟩ := c
  cases l with
  | none => simp [FinTM2.step, step] at hc
  | some l =>
    have hd : stepAux (b.m l) t T = d := by simpa [FinTM2.step, step] using hc
    rw [← hd]
    simpa only [secondCfg, machine, FinTM2.step, Option.map, step, program] using
      congrArg some (secondStmt_stepAux a b (b.m l) s t reg S T buffer)

theorem initial_eq (bridge : a.Γ a.k₁ ≃ b.Γ b.k₀) (seed : Option (a.Γ a.k₁))
    (input : List (a.Γ a.k₀)) :
    initList (machine a b bridge seed) input =
      firstCfg a b b.initialState none (fun _ => []) [] (initList a input) := by
  unfold initList firstCfg machine
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases hk : k = a.k₀
    · subst k; simp [combinedStacks]
    · simp [combinedStacks, hk]
  | inr k => cases k <;> simp [combinedStacks]

theorem final_eq (bridge : a.Γ a.k₁ ≃ b.Γ b.k₀) (seed : Option (a.Γ a.k₁))
    (output : List (b.Γ b.k₁)) :
    secondCfg a b a.initialState none (fun _ => []) [] (haltList b output) =
      haltList (machine a b bridge seed) output := by
  unfold haltList secondCfg machine
  congr 1
  funext k
  cases k with
  | inl k => simp [combinedStacks]
  | inr k =>
    cases k with
    | inl k =>
      by_cases hk : k = b.k₁
      · subst k; simp [combinedStacks]
      · simp [combinedStacks, hk]
    | inr k => simp [combinedStacks]

theorem first_run (bridge : a.Γ a.k₁ ≃ b.Γ b.k₀) (seed : Option (a.Γ a.k₁))
    (t : b.σ) (reg : Option (a.Γ a.k₁)) (T : ∀ k, List (b.Γ k))
    (buffer : List (a.Γ a.k₁)) (c d : a.Cfg) (n : ℕ)
    (hc : (fun x : Option a.Cfg => x.bind a.step)^[n] (some c) = some d) :
    (fun x : Option (machine a b bridge seed).Cfg => x.bind (machine a b bridge seed).step)^[n]
      (some (firstCfg a b t reg T buffer c)) = some (firstCfg a b t reg T buffer d) :=
  TM2Embedding.simulate_run a.step (machine a b bridge seed).step
    (firstCfg a b t reg T buffer) (first_step a b bridge seed t reg T buffer) n c d hc

theorem second_run (bridge : a.Γ a.k₁ ≃ b.Γ b.k₀) (seed : Option (a.Γ a.k₁))
    (s : a.σ) (reg : Option (a.Γ a.k₁)) (S : ∀ k, List (a.Γ k))
    (buffer : List (a.Γ a.k₁)) (c d : b.Cfg) (n : ℕ)
    (hc : (fun x : Option b.Cfg => x.bind b.step)^[n] (some c) = some d) :
    (fun x : Option (machine a b bridge seed).Cfg => x.bind (machine a b bridge seed).step)^[n]
      (some (secondCfg a b s reg S buffer c)) = some (secondCfg a b s reg S buffer d) :=
  TM2Embedding.simulate_run b.step (machine a b bridge seed).step
    (secondCfg a b s reg S buffer) (second_step a b bridge seed s reg S buffer) n c d hc

theorem handoff_start_eq (middle : List (a.Γ a.k₁)) :
    firstCfg a b b.initialState none (fun _ => []) [] (haltList a middle) =
      TM2Transfer.transferCfg (Γ := Alphabet a b) (Λ := Label a b) (.inl a.k₁) (.inr (.inr ()))
        (.inr (.inr false)) (a.initialState, b.initialState) none (fun _ => []) middle [] := by
  unfold firstCfg haltList TM2Transfer.transferCfg
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases hk : k = a.k₁
    · subst k; simp [combinedStacks, TM2Transfer.setStacks]
    · simp [combinedStacks, TM2Transfer.setStacks, hk, Function.update_of_ne]
  | inr k => cases k <;> simp [combinedStacks, TM2Transfer.setStacks, Function.update_of_ne]

theorem handoff_middle_eq (middle : List (a.Γ a.k₁)) :
    TM2Transfer.transferCfg (Γ := Alphabet a b) (Λ := Label a b) (.inl a.k₁) (.inr (.inr ()))
      (.inr (.inr true)) (a.initialState, b.initialState) none (fun _ => []) [] middle =
    TM2Transfer.transferCfg (Γ := Alphabet a b) (Λ := Label a b) (.inr (.inr ())) (.inr (.inl b.k₀))
      (.inr (.inr true)) (a.initialState, b.initialState) none (fun _ => []) middle [] := by
  unfold TM2Transfer.transferCfg
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases hk : k = a.k₁
    · subst k; simp [TM2Transfer.setStacks, Function.update_of_ne]
    · simp [TM2Transfer.setStacks, Function.update_of_ne]
  | inr k =>
    cases k with
    | inl k =>
      by_cases hk : k = b.k₀
      · subst k; simp [TM2Transfer.setStacks, Function.update_of_ne]
      · simp [TM2Transfer.setStacks, hk, Function.update_of_ne]
    | inr k => cases k; simp [TM2Transfer.setStacks, Function.update_of_ne]

theorem handoff_finish_eq (middle : List (b.Γ b.k₀)) :
    TM2Transfer.transferCfg (Γ := Alphabet a b) (Λ := Label a b) (.inr (.inr ())) (.inr (.inl b.k₀))
      (.inr (.inl b.main)) (a.initialState, b.initialState) none (fun _ => []) [] middle =
    secondCfg a b a.initialState none (fun _ => []) [] (initList b middle) := by
  unfold secondCfg initList TM2Transfer.transferCfg
  congr 1
  funext k
  cases k with
  | inl k => simp [combinedStacks, TM2Transfer.setStacks, Function.update_of_ne]
  | inr k =>
    cases k with
    | inl k =>
      by_cases hk : k = b.k₀
      · subst k; simp [combinedStacks, TM2Transfer.setStacks]
      · simp [combinedStacks, TM2Transfer.setStacks, hk, Function.update_of_ne]
    | inr k => cases k; simp [combinedStacks, TM2Transfer.setStacks, Function.update_of_ne]

theorem handoff_run_some (bridge : a.Γ a.k₁ ≃ b.Γ b.k₀) (x : a.Γ a.k₁)
    (middle : List (a.Γ a.k₁)) :
    (fun c : Option (machine a b bridge (some x)).Cfg =>
        c.bind (machine a b bridge (some x)).step)^[2 * middle.length + 2]
      (some (firstCfg a b b.initialState none (fun _ => []) [] (haltList a middle))) =
        some (secondCfg a b a.initialState none (fun _ => []) [] (initList b (middle.map bridge))) := by
  letI : Inhabited (Alphabet a b (.inl a.k₁)) := ⟨x⟩
  letI : Inhabited (Alphabet a b (.inr (.inr ()))) := ⟨x⟩
  have h1 := TM2Transfer.transfer_run (Γ := Alphabet a b) (σ := a.σ × b.σ)
    (.inl a.k₁) (.inr (.inr ())) (by intro h; cases h) id
    (.inr (.inr false)) (.inr (.inr true)) (program a b bridge (some x)) rfl
    (a.initialState, b.initialState) none (fun _ => []) middle []
  have h2 := TM2Transfer.transfer_run (Γ := Alphabet a b) (σ := a.σ × b.σ)
    (.inr (.inr ())) (.inr (.inl b.k₀)) (by intro h; cases h) bridge
    (.inr (.inr true)) (.inr (.inl b.main)) (program a b bridge (some x)) rfl
    (a.initialState, b.initialState) none (fun _ => []) middle.reverse []
  simp only [List.map_id, List.append_nil] at h1
  simp only [List.length_reverse, List.map_reverse, List.reverse_reverse, List.append_nil] at h2
  change (fun c : Option (Cfg (Alphabet a b) (Label a b) (State a b)) =>
    c.bind (step (program a b bridge (some x))))^[2 * middle.length + 2] _ = _
  rw [show 2 * middle.length + 2 = (middle.length + 1) + (middle.length + 1) by omega,
    Function.iterate_add_apply, handoff_start_eq]
  apply (congrArg
    ((fun c : Option (Cfg (Alphabet a b) (Label a b) (State a b)) =>
      c.bind (step (program a b bridge (some x))))^[middle.length + 1]) h1).trans
  rw [handoff_middle_eq]
  exact h2.trans (congrArg some (handoff_finish_eq a b (middle.map bridge)))

theorem init_nil_stk (tm : FinTM2) : (initList tm []).stk = fun _ => [] := by
  funext k
  by_cases hk : k = tm.k₀
  · subst k; simp [initList]
  · simp [initList, hk]

theorem halt_nil_stk (tm : FinTM2) : (haltList tm []).stk = fun _ => [] := by
  funext k
  by_cases hk : k = tm.k₁
  · subst k; simp [haltList]
  · simp [haltList, hk]

theorem handoff_step_none (bridge : a.Γ a.k₁ ≃ b.Γ b.k₀) :
    (machine a b bridge none).step
      (firstCfg a b b.initialState none (fun _ => []) [] (haltList a [])) =
      some (secondCfg a b a.initialState none (fun _ => []) [] (initList b [])) := by
  change some (Cfg.mk (Γ := Alphabet a b) (Λ := Label a b) (σ := State a b)
      (some (.inr (.inl b.main))) ((a.initialState, b.initialState), none)
      (combinedStacks a b (haltList a []).stk (fun _ => []) [])) =
    some (Cfg.mk (Γ := Alphabet a b) (Λ := Label a b) (σ := State a b)
      (some (.inr (.inl b.main))) ((a.initialState, b.initialState), none)
      (combinedStacks a b (fun _ => []) (initList b []).stk []))
  rw [halt_nil_stk, init_nil_stk]

noncomputable def machine_outputsInTime
    (bridge : a.Γ a.k₁ ≃ b.Γ b.k₀) (seed : Option (a.Γ a.k₁))
    (hseed : seed = none → IsEmpty (a.Γ a.k₁))
    (input : List (a.Γ a.k₀)) (middle : List (a.Γ a.k₁)) (output : List (b.Γ b.k₁))
    (n₁ n₂ : ℕ) (h₁ : TM2OutputsInTime a input (some middle) n₁)
    (h₂ : TM2OutputsInTime b (middle.map bridge) (some output) n₂) :
    TM2OutputsInTime (machine a b bridge seed) input (some output)
      (n₁ + n₂ + 2 * middle.length + 2) := by
  let c := machine a b bridge seed
  have hfirst : EvalsToInTime c.step (initList c input)
      (some (firstCfg a b b.initialState none (fun _ => []) [] (haltList a middle))) n₁ :=
    { steps := h₁.steps
      evals_in_steps := by
        rw [initial_eq]
        exact first_run a b bridge seed b.initialState none (fun _ => []) []
          (initList a input) (haltList a middle) h₁.steps h₁.evals_in_steps
      steps_le_m := h₁.steps_le_m }
  have hlast : EvalsToInTime c.step
      (secondCfg a b a.initialState none (fun _ => []) [] (initList b (middle.map bridge)))
      (some (haltList c output)) n₂ :=
    { steps := h₂.steps
      evals_in_steps := by
        rw [← final_eq]
        exact second_run a b bridge seed a.initialState none (fun _ => []) []
          (initList b (middle.map bridge)) (haltList b output) h₂.steps h₂.evals_in_steps
      steps_le_m := h₂.steps_le_m }
  have hmiddle : EvalsToInTime c.step
      (firstCfg a b b.initialState none (fun _ => []) [] (haltList a middle))
      (some (secondCfg a b a.initialState none (fun _ => []) [] (initList b (middle.map bridge))))
      (2 * middle.length + 2) := by
    cases seed with
    | none =>
      have hempty : middle = [] := by
        cases middle with
        | nil => rfl
        | cons x xs => exact False.elim ((hseed rfl).false x)
      subst middle
      exact
        { steps := 1
          evals_in_steps := handoff_step_none a b bridge
          steps_le_m := by simp }
    | some x =>
      exact
        { steps := 2 * middle.length + 2
          evals_in_steps := handoff_run_some a b bridge x middle
          steps_le_m := le_rfl }
  let h12 := EvalsToInTime.trans c.step n₁ (2 * middle.length + 2) _ _ _ hfirst hmiddle
  let h := EvalsToInTime.trans c.step ((2 * middle.length + 2) + n₁) n₂ _ _ _ h12 hlast
  exact
    { steps := h.steps
      evals_in_steps := h.evals_in_steps
      steps_le_m := by have hb := h.steps_le_m; omega }

end ProteinFolding.TM2Composition

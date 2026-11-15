import ProteinFolding.Common.TM2Bounds

/-!
# Embedding a TM2 program in a larger machine

Active stacks occupy the left summand. The right stacks and the second state
component are preserved. A source halt can either halt the target or jump to
a specified continuation label. This supports sequential composition without
relaxing the frozen machine interface.
-/

namespace ProteinFolding.TM2Embedding

open Turing TM2

variable {K J Λ L σ τ : Type} {Γ : K → Type} {Δ : J → Type}

def joinStacks (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j)) :
    ∀ i : K ⊕ J, List (Sum.elim Γ Δ i)
  | .inl k => S k
  | .inr j => T j

theorem joinStacks_update [DecidableEq K] [DecidableEq J]
    (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j)) (k : K) (w : List (Γ k)) :
    Function.update (joinStacks S T) (.inl k) w =
      joinStacks (Function.update S k w) T := by
  funext i
  cases i with
  | inl i =>
    by_cases h : i = k
    · subst i; simp [joinStacks]
    · simp [joinStacks, Function.update_of_ne, h]
  | inr j => simp [joinStacks, Function.update_of_ne]

def embedCfg (labels : Λ → L) (finish : Option L) (t : τ)
    (T : ∀ j, List (Δ j)) (c : Cfg Γ Λ σ) : Cfg (Sum.elim Γ Δ) L (σ × τ) where
  l := c.l.elim finish (fun l => some (labels l))
  var := (c.var, t)
  stk := joinStacks c.stk T

def liftStmt (labels : Λ → L) (finish : Option L) :
    Stmt Γ Λ σ → Stmt (Sum.elim Γ Δ) L (σ × τ)
  | .push k f q => .push (.inl k) (fun s => f s.1) (liftStmt labels finish q)
  | .peek k f q => .peek (.inl k) (fun s o => (f s.1 o, s.2)) (liftStmt labels finish q)
  | .pop k f q => .pop (.inl k) (fun s o => (f s.1 o, s.2)) (liftStmt labels finish q)
  | .load f q => .load (fun s => (f s.1, s.2)) (liftStmt labels finish q)
  | .branch f q r => .branch (fun s => f s.1) (liftStmt labels finish q) (liftStmt labels finish r)
  | .goto f => .goto (fun s => labels (f s.1))
  | .halt => match finish with
    | none => .halt
    | some l => .goto (fun _ => l)

theorem stepAux_liftStmt [DecidableEq K] [DecidableEq J]
    (labels : Λ → L) (finish : Option L) (q : Stmt Γ Λ σ)
    (s : σ) (t : τ) (S : ∀ k, List (Γ k)) (T : ∀ j, List (Δ j)) :
    stepAux (liftStmt labels finish q) (s, t) (joinStacks S T) =
      embedCfg labels finish t T (stepAux q s S) := by
  induction q generalizing s S with
  | push k f q ih =>
    simpa only [liftStmt, stepAux, joinStacks, joinStacks_update] using
      ih s (Function.update S k (f s :: S k))
  | peek k f q ih =>
    exact ih (f s (S k).head?) S
  | pop k f q ih =>
    simpa only [liftStmt, stepAux, joinStacks, joinStacks_update] using
      ih (f s (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih (f s) S
  | branch f q r ihq ihr =>
    cases hf : f s
    · simpa [liftStmt, stepAux, hf, embedCfg] using ihr s S
    · simpa [liftStmt, stepAux, hf, embedCfg] using ihq s S
  | goto f => rfl
  | halt => cases finish <;> rfl

/-- A successful source step is simulated by exactly one target step.
Only labels in the active image need to have the lifted program. -/
theorem step_liftStmt [DecidableEq K] [DecidableEq J]
    (labels : Λ → L) (finish : Option L)
    (program : Λ → Stmt Γ Λ σ)
    (target : L → Stmt (Sum.elim Γ Δ) L (σ × τ))
    (hprogram : ∀ l, target (labels l) = liftStmt labels finish (program l))
    (t : τ) (T : ∀ j, List (Δ j)) (a b : Cfg Γ Λ σ)
    (hstep : step program a = some b) :
    step target (embedCfg labels finish t T a) =
      some (embedCfg labels finish t T b) := by
  obtain ⟨l, s, S⟩ := a
  cases l with
  | none => simp [step] at hstep
  | some l =>
    have hb : stepAux (program l) s S = b := by simpa [step] using hstep
    rw [← hb]
    simpa only [embedCfg, Option.elim, step, hprogram] using
      congrArg some (stepAux_liftStmt labels finish (program l) s t S T)

/-- Successful finite executions lift with the same number of steps. This
requires simulation of successful steps only, so a halt-to-continuation jump
does not incorrectly claim that further steps simulate a halted source. -/
theorem simulate_run {A B : Type*} (source : A → Option A) (target : B → Option B)
    (embed : A → B)
    (hstep : ∀ a b, source a = some b → target (embed a) = some (embed b))
    (n : ℕ) (a b : A)
    (hrun : (fun x : Option A => x.bind source)^[n] (some a) = some b) :
    (fun x : Option B => x.bind target)^[n] (some (embed a)) = some (embed b) := by
  induction n generalizing b with
  | zero =>
    have hab : a = b := by simpa using hrun
    subst b
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hrun ⊢
    cases hc : (fun x : Option A => x.bind source)^[n] (some a) with
    | none => simp [hc] at hrun
    | some c =>
      have hcb : source c = some b := by simpa [hc] using hrun
      rw [ih c hc]
      exact hstep c b hcb

end ProteinFolding.TM2Embedding

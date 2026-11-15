import ProteinFolding.Common.TM2Embedding

/-! Embed a program in a product state while keeping exactly the same stacks.
The passive component is preserved and source halt may enter a continuation. -/

namespace ProteinFolding.TM2StateExtension

open Turing TM2

variable {K Λ L σ τ : Type} {Γ : K → Type}

def liftStmt (labels : Λ → L) (finish : Option L) : Stmt Γ Λ σ → Stmt Γ L (σ × τ)
  | .push k f q => .push k (fun st => f st.1) (liftStmt labels finish q)
  | .peek k f q => .peek k (fun st o => (f st.1 o, st.2)) (liftStmt labels finish q)
  | .pop k f q => .pop k (fun st o => (f st.1 o, st.2)) (liftStmt labels finish q)
  | .load f q => .load (fun st => (f st.1, st.2)) (liftStmt labels finish q)
  | .branch f q r => .branch (fun st => f st.1) (liftStmt labels finish q) (liftStmt labels finish r)
  | .goto f => .goto (fun st => labels (f st.1))
  | .halt => match finish with
    | none => .halt
    | some l => .goto (fun _ => l)

def embedCfg (labels : Λ → L) (finish : Option L) (t : τ) (c : Cfg Γ Λ σ) :
    Cfg Γ L (σ × τ) where
  l := c.l.elim finish (fun l => some (labels l))
  var := (c.var, t)
  stk := c.stk

theorem stepAux_liftStmt [DecidableEq K] (labels : Λ → L) (finish : Option L)
    (q : Stmt Γ Λ σ) (s : σ) (t : τ) (S : ∀ k, List (Γ k)) :
    stepAux (liftStmt labels finish q) (s, t) S =
      embedCfg labels finish t (stepAux q s S) := by
  induction q generalizing s S with
  | push k f q ih => exact ih s (Function.update S k (f s :: S k))
  | peek k f q ih => exact ih (f s (S k).head?) S
  | pop k f q ih => exact ih (f s (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih (f s) S
  | branch f q r ihq ihr =>
    cases hf : f s
    · simpa [liftStmt, stepAux, hf, embedCfg] using ihr s S
    · simpa [liftStmt, stepAux, hf, embedCfg] using ihq s S
  | goto f => rfl
  | halt => cases finish <;> rfl

theorem step_liftStmt [DecidableEq K] (labels : Λ → L) (finish : Option L)
    (program : Λ → Stmt Γ Λ σ) (target : L → Stmt Γ L (σ × τ))
    (hprogram : ∀ l, target (labels l) = liftStmt labels finish (program l))
    (t : τ) (a b : Cfg Γ Λ σ) (h : step program a = some b) :
    step target (embedCfg labels finish t a) = some (embedCfg labels finish t b) := by
  obtain ⟨l, s, S⟩ := a
  cases l with
  | none => simp [step] at h
  | some l =>
    have hb : stepAux (program l) s S = b := by simpa [step] using h
    rw [← hb]
    simpa only [embedCfg, Option.elim, step, hprogram] using
      congrArg some (stepAux_liftStmt labels finish (program l) s t S)

theorem run_liftStmt [DecidableEq K] (labels : Λ → L) (finish : Option L)
    (program : Λ → Stmt Γ Λ σ) (target : L → Stmt Γ L (σ × τ))
    (hprogram : ∀ l, target (labels l) = liftStmt labels finish (program l))
    (t : τ) (n : ℕ) (a b : Cfg Γ Λ σ)
    (h : (fun x : Option (Cfg Γ Λ σ) => x.bind (step program))^[n] (some a) = some b) :
    (fun x : Option (Cfg Γ L (σ × τ)) => x.bind (step target))^[n]
      (some (embedCfg labels finish t a)) = some (embedCfg labels finish t b) :=
  TM2Embedding.simulate_run (step program) (step target) (embedCfg labels finish t)
    (step_liftStmt labels finish program target hprogram t) n a b h

end ProteinFolding.TM2StateExtension

import ProteinFolding.Common.TM2Embedding

/-! State equivalences for TM2 program assembly. The transformed program uses
the same stacks and labels, with every state operation conjugated by the given
equivalence. Both successful steps and successful runs are preserved exactly. -/

namespace ProteinFolding.TM2Renaming

open Turing TM2

variable {K Λ σ τ : Type} {Γ : K → Type}

def relabelStmt (e : σ ≃ τ) : Stmt Γ Λ σ → Stmt Γ Λ τ
  | .push k f q => .push k (fun t => f (e.symm t)) (relabelStmt e q)
  | .peek k f q => .peek k (fun t o => e (f (e.symm t) o)) (relabelStmt e q)
  | .pop k f q => .pop k (fun t o => e (f (e.symm t) o)) (relabelStmt e q)
  | .load f q => .load (fun t => e (f (e.symm t))) (relabelStmt e q)
  | .branch f q r => .branch (fun t => f (e.symm t)) (relabelStmt e q) (relabelStmt e r)
  | .goto f => .goto (fun t => f (e.symm t))
  | .halt => .halt

def mapCfg (e : σ ≃ τ) (c : Cfg Γ Λ σ) : Cfg Γ Λ τ where
  l := c.l
  var := e c.var
  stk := c.stk

theorem stepAux_relabelStmt [DecidableEq K] (e : σ ≃ τ)
    (q : Stmt Γ Λ σ) (s : σ) (S : ∀ k, List (Γ k)) :
    stepAux (relabelStmt e q) (e s) S = mapCfg e (stepAux q s S) := by
  induction q generalizing s S with
  | push k f q ih =>
    simpa only [relabelStmt, stepAux, Equiv.symm_apply_apply] using
      ih s (Function.update S k (f s :: S k))
  | peek k f q ih =>
    simpa only [relabelStmt, stepAux, Equiv.symm_apply_apply] using ih (f s (S k).head?) S
  | pop k f q ih =>
    simpa only [relabelStmt, stepAux, Equiv.symm_apply_apply] using
      ih (f s (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
    simpa only [relabelStmt, stepAux, Equiv.symm_apply_apply] using ih (f s) S
  | branch f q r ihq ihr =>
    cases hf : f s
    · simpa [relabelStmt, stepAux, hf, mapCfg] using ihr s S
    · simpa [relabelStmt, stepAux, hf, mapCfg] using ihq s S
  | goto f => simp [relabelStmt, stepAux, mapCfg]
  | halt => rfl

theorem step_relabelStmt [DecidableEq K] (e : σ ≃ τ)
    (program : Λ → Stmt Γ Λ σ) (a b : Cfg Γ Λ σ)
    (h : step program a = some b) :
    step (fun l => relabelStmt e (program l)) (mapCfg e a) = some (mapCfg e b) := by
  obtain ⟨l, s, S⟩ := a
  cases l with
  | none => simp [step] at h
  | some l =>
    have hb : stepAux (program l) s S = b := by simpa [step] using h
    rw [← hb]
    exact congrArg some (stepAux_relabelStmt e (program l) s S)

theorem run_relabelStmt [DecidableEq K] (e : σ ≃ τ)
    (program : Λ → Stmt Γ Λ σ) (n : ℕ) (a b : Cfg Γ Λ σ)
    (h : (fun x : Option (Cfg Γ Λ σ) => x.bind (step program))^[n] (some a) = some b) :
    (fun x : Option (Cfg Γ Λ τ) => x.bind (step (fun l => relabelStmt e (program l))))^[n]
      (some (mapCfg e a)) = some (mapCfg e b) :=
  TM2Embedding.simulate_run (step program) (step (fun l => relabelStmt e (program l)))
    (mapCfg e) (step_relabelStmt e program) n a b h

end ProteinFolding.TM2Renaming

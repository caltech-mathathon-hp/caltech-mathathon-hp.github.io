import ProteinFolding.Common.TM2Renaming

/-! Cancellation for the proved state-equivalence transformation. -/

namespace ProteinFolding.TM2Renaming

open Turing TM2

theorem relabelStmt_symm {K L σ τ : Type} {Γ : K → Type} (e : σ ≃ τ)
    (q : Stmt Γ L σ) : relabelStmt e.symm (relabelStmt e q) = q := by
  induction q with
  | push k f q ih => simp [relabelStmt, ih]
  | peek k f q ih => simp [relabelStmt, ih]
  | pop k f q ih => simp [relabelStmt, ih]
  | load f q ih => simp [relabelStmt, ih]
  | branch f q r ihq ihr => simp [relabelStmt, ihq, ihr]
  | goto f => simp [relabelStmt]
  | halt => rfl

end ProteinFolding.TM2Renaming

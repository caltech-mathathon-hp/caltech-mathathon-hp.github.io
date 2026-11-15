import ProteinFolding.Tetrahedral.ReductionTM2SignedArithmetic

namespace ProteinFolding.Tetrahedral.ReductionTM2.Arithmetic.SignedExpr

variable {n : ℕ}

def residue2 (a : SignedExpr n) : Expr n .natural :=
  Arithmetic.mod2 (.add a.positive a.negative)

def residue4 (a : SignedExpr n) : Expr n .natural :=
  Arithmetic.mod4 (.add a.positive (.mul (.nat 3) a.negative))

theorem natural_residue2 (a b : ℕ) : (((a + b) % 2 : ℕ) : ℤ) = ((a : ℤ) - b) % 2 := by omega

theorem natural_residue4 (a b : ℕ) : (((a + 3 * b) % 4 : ℕ) : ℤ) = ((a : ℤ) - b) % 4 := by omega

theorem eval_residue2 (ν : Fin n → ℕ) (a : SignedExpr n) :
    (Arithmetic.eval ν (residue2 a) : ℤ) = eval ν a % 2 := by
  simpa only [residue2, Arithmetic.eval_mod2, Arithmetic.eval, eval] using
    natural_residue2 (Arithmetic.eval ν a.positive) (Arithmetic.eval ν a.negative)

theorem eval_residue4 (ν : Fin n → ℕ) (a : SignedExpr n) :
    (Arithmetic.eval ν (residue4 a) : ℤ) = eval ν a % 4 := by
  simpa only [residue4, Arithmetic.eval_mod4, Arithmetic.eval, eval] using
    natural_residue4 (Arithmetic.eval ν a.positive) (Arithmetic.eval ν a.negative)

end ProteinFolding.Tetrahedral.ReductionTM2.Arithmetic.SignedExpr

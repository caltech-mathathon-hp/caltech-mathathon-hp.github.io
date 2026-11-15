import ProteinFolding.Tetrahedral.ReductionTM2Arithmetic

namespace ProteinFolding.Tetrahedral.ReductionTM2.Arithmetic

variable {n : ℕ}

theorem eval_and_true (ν : Fin n → ℕ) (a b : Expr n .boolean) :
    eval ν (.and a b) = true ↔ eval ν a = true ∧ eval ν b = true := by
  rw [eval, Bool.and_eq_true]

theorem eval_or_true (ν : Fin n → ℕ) (a b : Expr n .boolean) :
    eval ν (.or a b) = true ↔ eval ν a = true ∨ eval ν b = true := by
  rw [eval, Bool.or_eq_true]

theorem eval_bool_true (ν : Fin n → ℕ) (b : Bool) : eval ν (.bool b) = true ↔ b = true := Iff.rfl

theorem eval_nat_eq_true (ν : Fin n → ℕ) (a b : Expr n .natural) :
    eval ν (.eq a b) = true ↔ eval ν a = eval ν b := by
  rw [eval, decide_eq_true_eq]

theorem eval_nat_lt_true (ν : Fin n → ℕ) (a b : Expr n .natural) :
    eval ν (.lt a b) = true ↔ eval ν a < eval ν b := by
  rw [eval, decide_eq_true_eq]

theorem eval_nat_le_true (ν : Fin n → ℕ) (a b : Expr n .natural) :
    eval ν (.le a b) = true ↔ eval ν a ≤ eval ν b := by
  rw [eval, decide_eq_true_eq]

end ProteinFolding.Tetrahedral.ReductionTM2.Arithmetic

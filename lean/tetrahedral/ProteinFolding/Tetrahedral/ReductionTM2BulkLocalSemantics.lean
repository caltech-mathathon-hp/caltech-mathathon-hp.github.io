import ProteinFolding.Tetrahedral.ReductionTM2BulkSemantics
import ProteinFolding.Tetrahedral.ReductionTM2ArithmeticBoolean

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

open Arithmetic
variable {n : ℕ}

theorem eval_deleted (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) :
    Arithmetic.eval ν (deleted m p) = true ↔ bulkFastDeleted (Arithmetic.eval ν m) s := by
  have hr : octRadius (Arithmetic.eval ν m) - 1 = 2 * (Arithmetic.eval ν m : ℤ) - 3 := by
    unfold octRadius
    omega
  rw [deleted, Arithmetic.eval_and_true, eval_inside_site ν m p s hp]
  unfold bulkFastDeleted
  apply and_congr Iff.rfl
  rw [Arithmetic.eval_any]
  apply exists_congr
  intro k
  rw [Arithmetic.eval_any]
  apply exists_congr
  intro j
  rw [Arithmetic.eval_and_true, Arithmetic.eval_bool_true, decide_eq_true_eq]
  apply and_congr Iff.rfl
  rw [Arithmetic.eval_or_true]
  apply or_congr
  · rw [Arithmetic.eval_and_true, eval_inA ν p, hp]
    apply and_congr Iff.rfl
    rw [Arithmetic.eval_and_true, SignedExpr.eval_eq, SignedExpr.eval_eq,
      decide_eq_true_eq, decide_eq_true_eq]
    simp only [eval_tetra, eval_radius, SignedExpr.eval_neg, hp]
  · rw [Arithmetic.eval_and_true, eval_inB ν p, hp]
    apply and_congr Iff.rfl
    rw [Arithmetic.eval_and_true, SignedExpr.eval_eq, SignedExpr.eval_eq,
      decide_eq_true_eq, decide_eq_true_eq]
    simp only [eval_tetra, eval_lower, eval_radius, SignedExpr.eval_sub,
      SignedExpr.eval_constant, hp, hr]

theorem eval_interior (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) :
    Arithmetic.eval ν (interior m p) = true ↔ bulkFastInterior (Arithmetic.eval ν m) s := by
  rw [interior, Arithmetic.eval, Bool.and_eq_true, eval_inside_site ν m p s hp,
    eval_not_true, eval_deleted ν m p s hp]
  rfl

theorem eval_baseDirection (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) (d : Fin 4) :
    Arithmetic.eval ν (baseDirection m p d) = true ↔
      bulkFastInterior (Arithmetic.eval ν m) (step s d) ∧
        bulkRho (Arithmetic.eval ν m) s ≠ bulkRho (Arithmetic.eval ν m) (step s d) := by
  rw [baseDirection, Arithmetic.eval, Bool.and_eq_true,
    eval_interior ν m (stepPoint p d) (step s d) (eval_stepPoint ν p s hp d),
    eval_not_true, eval_rho_eq ν m p (stepPoint p d) s (step s d) hp (eval_stepPoint ν p s hp d)]

theorem eval_baseCount (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) :
    Arithmetic.eval ν (baseCount m p) = (bulkFastBaseDirections (Arithmetic.eval ν m) s).card := by
  rw [baseCount, Arithmetic.eval_count]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_baseDirection ν m p s hp,
    bulkFastBaseDirections, Finset.mem_filter, Finset.mem_univ, true_and]

theorem eval_danglingDirection (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) (d : Fin 4) :
    Arithmetic.eval ν (danglingDirection m p d) = true ↔ ¬InOctahedron (Arithmetic.eval ν m) (step s d) := by
  rw [danglingDirection, eval_not_true,
    eval_inside_site ν m (stepPoint p d) (step s d) (eval_stepPoint ν p s hp d)]

theorem eval_danglingCount (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) :
    Arithmetic.eval ν (danglingCount m p) = (bulkFastDanglingDirections (Arithmetic.eval ν m) s).card := by
  rw [danglingCount, Arithmetic.eval_count]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_danglingDirection ν m p s hp,
    bulkFastDanglingDirections, Finset.mem_filter, Finset.mem_univ, true_and]

theorem eval_damaged (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) :
    Arithmetic.eval ν (damaged m p) = true ↔ bulkFastDamaged (Arithmetic.eval ν m) s := by
  rw [damaged, Arithmetic.eval, Bool.and_eq_true, eval_interior ν m p s hp, Arithmetic.eval_any]
  apply and_congr Iff.rfl
  apply exists_congr
  intro d
  rw [Arithmetic.eval, Bool.and_eq_true,
    eval_deleted ν m (stepPoint p d) (step s d) (eval_stepPoint ν p s hp d),
    eval_not_true, eval_rho_eq ν m p (stepPoint p d) s (step s d) hp (eval_stepPoint ν p s hp d)]

end ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

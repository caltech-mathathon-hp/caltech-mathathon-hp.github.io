import ProteinFolding.Tetrahedral.ReductionTM2BulkLocalSemantics
import ProteinFolding.Tetrahedral.ReductionTM2BulkPatchSemantics
import ProteinFolding.Tetrahedral.ReductionTM2ArithmeticBoolean

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

open Arithmetic
variable {n : ℕ}

theorem eval_nonzero (ν : Fin n → ℕ) (e : SignedExpr n) :
    Arithmetic.eval ν (nonzero e) = true ↔ SignedExpr.eval ν e ≠ 0 := by
  rw [nonzero, eval_not_true, SignedExpr.eval_eq, decide_eq_true_eq, SignedExpr.eval_constant]

theorem eval_rule (ν : Fin n → ℕ) (m : Expr n .natural) (p q : PointExpr n) (s t : Site)
    (hp : evalPoint ν p = s.val) (hq : evalPoint ν q = t.val) :
    Arithmetic.eval ν (rule m p q) = true ↔ bulkRuleNeighbour (Arithmetic.eval ν m) s t := by
  rw [rule, Arithmetic.eval_and_true, eval_adjacent ν p q s t hp hq]
  unfold bulkRuleNeighbour
  apply and_congr Iff.rfl
  rw [Arithmetic.eval_or_true]
  apply or_congr
  · rw [Arithmetic.eval_and_true, eval_nonzero, eval_y ν m p s hp]
    apply and_congr Iff.rfl
    rw [Arithmetic.eval_and_true, eval_nonzero, eval_z ν p s hp]
    apply and_congr Iff.rfl
    rw [Arithmetic.eval_and_true, SignedExpr.eval_eq, SignedExpr.eval_eq,
      decide_eq_true_eq, decide_eq_true_eq]
    simp only [SignedExpr.eval_sub, SignedExpr.eval_neg, SignedExpr.eval_sign,
      eval_y ν m p s hp, eval_y ν m q t hq, eval_z ν p s hp, eval_z ν q t hq, bulkSign]
  · rw [Arithmetic.eval_and_true, SignedExpr.eval_eq, decide_eq_true_eq,
      eval_z ν p s hp, SignedExpr.eval_constant]
    apply and_congr Iff.rfl
    rw [Arithmetic.eval_and_true, eval_nonzero, eval_y ν m p s hp]
    apply and_congr Iff.rfl
    rw [Arithmetic.eval_and_true, SignedExpr.eval_eq, SignedExpr.eval_eq,
      decide_eq_true_eq, decide_eq_true_eq]
    simp only [SignedExpr.eval_sub, SignedExpr.eval_neg, SignedExpr.eval_sign, SignedExpr.eval_constant,
      eval_y ν m p s hp, eval_y ν m q t hq, eval_z ν p s hp, eval_z ν q t hq, bulkSign]

theorem eval_potential (ν : Fin n → ℕ) (m : Expr n .natural) (p q : PointExpr n) (s t : Site)
    (hp : evalPoint ν p = s.val) (hq : evalPoint ν q = t.val) :
    Arithmetic.eval ν (potential m p q) = true ↔ bulkFastPotential (Arithmetic.eval ν m) s t := by
  rw [potential, Arithmetic.eval_and_true, eval_interior ν m q t hq]
  rw [Arithmetic.eval_and_true, eval_rule ν m p q s t hp hq]
  rw [Arithmetic.eval_and_true, Arithmetic.eval_nat_le_true, Arithmetic.eval_nat_lt_true,
    eval_baseCount ν m q t hq, eval_danglingCount ν m q t hq]
  rfl

theorem eval_claimantDirection (ν : Fin n → ℕ) (m : Expr n .natural) (q : PointExpr n) (t : Site)
    (hq : evalPoint ν q = t.val) (d : Fin 4) :
    Arithmetic.eval ν (claimantDirection m q d) = true ↔
      bulkFastDamaged (Arithmetic.eval ν m) (step t d) ∧
        bulkFastPotential (Arithmetic.eval ν m) (step t d) t := by
  rw [claimantDirection, Arithmetic.eval_and_true,
    eval_damaged ν m (stepPoint q d) (step t d) (eval_stepPoint ν q t hq d),
    eval_potential ν m (stepPoint q d) q (step t d) t (eval_stepPoint ν q t hq d) hq]

theorem eval_claimantCount (ν : Fin n → ℕ) (m : Expr n .natural) (q : PointExpr n) (t : Site)
    (hq : evalPoint ν q = t.val) :
    Arithmetic.eval ν (claimantCount m q) = (bulkFastClaimantDirections (Arithmetic.eval ν m) t).card := by
  rw [claimantCount, Arithmetic.eval_count]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_claimantDirection ν m q t hq,
    bulkFastClaimantDirections, Finset.mem_filter, Finset.mem_univ, true_and]

theorem eval_merge (ν : Fin n → ℕ) (m : Expr n .natural) (p q : PointExpr n) (s t : Site)
    (hp : evalPoint ν p = s.val) (hq : evalPoint ν q = t.val) :
    Arithmetic.eval ν (merge m p q) = true ↔ bulkFastMerge (Arithmetic.eval ν m) s t := by
  rw [merge, Arithmetic.eval_and_true, eval_damaged ν m p s hp]
  rw [Arithmetic.eval_and_true, eval_potential ν m p q s t hp hq,
    Arithmetic.eval_nat_eq_true, eval_claimantCount ν m q t hq]
  rfl

theorem eval_rung (ν : Fin n → ℕ) (m : Expr n .natural) (p q : PointExpr n) (s t : Site)
    (hp : evalPoint ν p = s.val) (hq : evalPoint ν q = t.val) :
    Arithmetic.eval ν (rung m p q) = true ↔ (bulkRungGraph (Arithmetic.eval ν m)).Adj s t := by
  rw [rung, Arithmetic.eval_and_true, eval_adjacent ν p q s t hp hq,
    eval_not_true, eval_rho_eq ν m p q s t hp hq]
  rfl

theorem eval_cover (ν : Fin n → ℕ) (m : Expr n .natural) (p q : PointExpr n) (s t : Site)
    (hp : evalPoint ν p = s.val) (hq : evalPoint ν q = t.val) :
    Arithmetic.eval ν (cover m p q) = true ↔ bulkCoverBond (Arithmetic.eval ν m) s t := by
  rw [bulkCoverBond_fast_iff]
  rw [cover, Arithmetic.eval_and_true, eval_interior ν m p s hp]
  rw [Arithmetic.eval_and_true, eval_interior ν m q t hq]
  rw [Arithmetic.eval_or_true, eval_patchAdded ν m p q s t hp hq]
  rw [Arithmetic.eval_and_true, eval_not_true, eval_patchRemoved ν m p q s t hp hq]
  rw [Arithmetic.eval_or_true, eval_rung ν m p q s t hp hq]
  rw [Arithmetic.eval_or_true, eval_merge ν m p q s t hp hq, eval_merge ν m q p t s hq hp]
  rfl

theorem eval_guardedCover (ν : Fin n → ℕ) (m : Expr n .natural) (p q : PointExpr n) (s t : Site)
    (hp : evalPoint ν p = s.val) (hq : evalPoint ν q = t.val) :
    Arithmetic.eval ν (guardedCover m p q) = true ↔ bulkCoverBond (Arithmetic.eval ν m) s t := by
  rw [guardedCover, Arithmetic.eval_and_true, Arithmetic.eval_and_true,
    eval_site ν p, eval_site ν q, hp, hq, eval_cover ν m p q s t hp hq]
  simp only [s.property, t.property, true_and]

end ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

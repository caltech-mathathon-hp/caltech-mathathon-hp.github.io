import ProteinFolding.Tetrahedral.ReductionTM2BulkLocal

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

open Arithmetic
variable {n : ℕ}

theorem eval_choose (ν : Fin n → ℕ) (b : Expr n .boolean) (a c : SignedExpr n) :
    SignedExpr.eval ν (choose b a c) =
      if Arithmetic.eval ν b then SignedExpr.eval ν a else SignedExpr.eval ν c := by
  cases hb : Arithmetic.eval ν b <;> simp [choose, SignedExpr.eval, Arithmetic.eval, hb]

theorem eval_samePoint (ν : Fin n → ℕ) (p q : PointExpr n) :
    Arithmetic.eval ν (samePoint p q) = true ↔ evalPoint ν p = evalPoint ν q := by
  rw [samePoint, Arithmetic.eval_all]
  simp only [SignedExpr.eval_eq, decide_eq_true_eq]
  exact ⟨fun h => funext h, fun h k => congrFun h k⟩

theorem eval_stepPoint (ν : Fin n → ℕ) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) (d : Fin 4) :
    evalPoint ν (stepPoint p d) = (step s d).val := by
  funext k
  change SignedExpr.eval ν ((p k).add _) = (step s d).val k
  rw [SignedExpr.eval_add, eval_choose, SignedExpr.eval_constant, SignedExpr.eval_constant]
  change evalPoint ν p k + (if Arithmetic.eval ν (inA p) then bondVector d k else -bondVector d k) = _
  rw [hp]
  by_cases hs : InASublattice s.val
  · have he : Arithmetic.eval ν (inA p) = true := (eval_inA ν p).2 (by rw [hp]; exact hs)
    rw [he, if_pos (rfl : true = true), step_val_of_A s hs]
  · have he : Arithmetic.eval ν (inA p) = false := by
      cases hh : Arithmetic.eval ν (inA p)
      · rfl
      · exact False.elim (hs (by have h := (eval_inA ν p).1 hh; rwa [hp] at h))
    rw [he, if_neg (by decide : ¬(false = true)), step_val_of_B s ((inB_iff_not_inA s).2 hs)]
    change s.val k + -bondVector d k = s.val k - bondVector d k
    ring

theorem eval_adjacent (ν : Fin n → ℕ) (p q : PointExpr n) (s t : Site)
    (hp : evalPoint ν p = s.val) (hq : evalPoint ν q = t.val) :
    Arithmetic.eval ν (adjacent p q) = true ↔ tetrahedralLattice.Adj s t := by
  rw [adjacent, Arithmetic.eval_any, adj_iff_exists_step]
  apply exists_congr
  intro d
  rw [eval_samePoint, eval_stepPoint ν p s hp d, hq]
  exact Subtype.val_inj

theorem eval_inside_site (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) :
    Arithmetic.eval ν (inside m p) = true ↔ InOctahedron (Arithmetic.eval ν m) s := by
  simpa only [hp, InOctahedron] using eval_inside ν m p

theorem eval_y (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) :
    SignedExpr.eval ν (y m p) = bulkY (Arithmetic.eval ν m) s := by
  rw [y, SignedExpr.eval_sub, eval_radius]
  change evalPoint ν p 1 - _ = _
  rw [hp]
  rfl

theorem eval_z (ν : Fin n → ℕ) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) : SignedExpr.eval ν (z p) = bulkZ s := by
  rw [z, SignedExpr.eval_sub, SignedExpr.eval_constant]
  change evalPoint ν p 2 - _ = _
  rw [hp]
  rfl

theorem eval_rho_site (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) (s : Site)
    (hp : evalPoint ν p = s.val) :
    (Arithmetic.eval ν (rho m p) : ℤ) = bulkRho (Arithmetic.eval ν m) s := by
  simpa only [hp, bulkRho, bulkY, bulkZ] using eval_rho ν m p

theorem eval_rho_eq (ν : Fin n → ℕ) (m : Expr n .natural) (p q : PointExpr n) (s t : Site)
    (hp : evalPoint ν p = s.val) (hq : evalPoint ν q = t.val) :
    Arithmetic.eval ν (.eq (rho m p) (rho m q)) = true ↔
      bulkRho (Arithmetic.eval ν m) s = bulkRho (Arithmetic.eval ν m) t := by
  simp only [Arithmetic.eval, decide_eq_true_eq]
  have hs := eval_rho_site ν m p s hp
  have ht := eval_rho_site ν m q t hq
  constructor
  · intro he
    rw [← hs, ← ht, he]
  · intro he
    apply Int.ofNat_inj.mp
    rw [hs, ht, he]

theorem eval_not_true (ν : Fin n → ℕ) (e : Expr n .boolean) :
    Arithmetic.eval ν (.not e) = true ↔ ¬Arithmetic.eval ν e = true := by
  cases he : Arithmetic.eval ν e <;> simp [Arithmetic.eval, he]

end ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

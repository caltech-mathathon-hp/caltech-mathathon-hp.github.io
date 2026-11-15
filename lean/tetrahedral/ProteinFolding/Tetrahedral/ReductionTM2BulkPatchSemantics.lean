import ProteinFolding.Tetrahedral.ReductionTM2BulkSemantics

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

open Arithmetic
variable {n : ℕ}

theorem eval_constantPoint (ν : Fin n → ℕ) (p : Coordinates) : evalPoint ν (constantPoint p) = p := by
  funext k
  exact SignedExpr.eval_constant ν (p k)

theorem eval_patchVertex (ν : Fin n → ℕ) (m : Expr n .natural) (v : Fin 6) :
    evalPoint ν (patchVertex m v) = (bulkPatchVertex (Arithmetic.eval ν m) v).val := by
  fin_cases v <;> funext k <;> fin_cases k
  all_goals simp [evalPoint, patchVertex, eval_radius, bulkPatchVertex,
    octVertexSite, octVertexCoordinates, octCentre, octRadius]
  all_goals ring

theorem eval_relative (ν : Fin n → ℕ) (m : Expr n .natural) (v : Fin 6) (p : PointExpr n)
    (s : Site) (hp : evalPoint ν p = s.val) :
    evalPoint ν (relative m v p) = fun k => s.val k - (bulkPatchVertex (Arithmetic.eval ν m) v).val k := by
  funext k
  change SignedExpr.eval ν ((p k).sub (patchVertex m v k)) = _
  rw [SignedExpr.eval_sub]
  change evalPoint ν p k - evalPoint ν (patchVertex m v) k = _
  rw [hp, eval_patchVertex]

theorem eval_relativePair (ν : Fin n → ℕ) (m : Expr n .natural) (v : Fin 6)
    (p q : PointExpr n) (s t : Site) (hp : evalPoint ν p = s.val) (hq : evalPoint ν q = t.val) :
    (evalPoint ν (relative m v p), evalPoint ν (relative m v q)) =
      bulkPatchRelativePair (Arithmetic.eval ν m) v s t := by
  rw [eval_relative ν m v p s hp, eval_relative ν m v q t hq]
  rfl

theorem eval_patchMember (ν : Fin n → ℕ) (table : Finset (Coordinates × Coordinates))
    (p q : PointExpr n) :
    Arithmetic.eval ν (patchMember table p q) = true ↔ (evalPoint ν p, evalPoint ν q) ∈ table := by
  rw [patchMember, Arithmetic.eval_anyList]
  constructor
  · rintro ⟨eExpr, heExpr, ht⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp heExpr
    rw [Arithmetic.eval, Bool.and_eq_true, eval_samePoint, eval_samePoint,
      eval_constantPoint, eval_constantPoint] at ht
    have heq : e = (evalPoint ν p, evalPoint ν q) := Prod.ext ht.1.symm ht.2.symm
    simpa only [heq] using (Finset.mem_toList.mp he)
  · intro he
    refine ⟨.and (samePoint p (constantPoint (evalPoint ν p)))
      (samePoint q (constantPoint (evalPoint ν q))), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨(evalPoint ν p, evalPoint ν q), Finset.mem_toList.mpr he, rfl⟩
    · rw [Arithmetic.eval, Bool.and_eq_true, eval_samePoint, eval_samePoint,
        eval_constantPoint, eval_constantPoint]
      exact ⟨rfl, rfl⟩

theorem eval_patchAdded (ν : Fin n → ℕ) (m : Expr n .natural) (p q : PointExpr n) (s t : Site)
    (hp : evalPoint ν p = s.val) (hq : evalPoint ν q = t.val) :
    Arithmetic.eval ν (patchAdded m p q) = true ↔ bulkPatchAdded (Arithmetic.eval ν m) s t := by
  rw [patchAdded, Arithmetic.eval_any]
  apply exists_congr
  intro v
  rw [Arithmetic.eval, Bool.or_eq_true, eval_patchMember, eval_patchMember,
    eval_relativePair ν m v p q s t hp hq, eval_relativePair ν m v q p t s hq hp]

theorem eval_patchRemoved (ν : Fin n → ℕ) (m : Expr n .natural) (p q : PointExpr n) (s t : Site)
    (hp : evalPoint ν p = s.val) (hq : evalPoint ν q = t.val) :
    Arithmetic.eval ν (patchRemoved m p q) = true ↔ bulkPatchRemoved (Arithmetic.eval ν m) s t := by
  rw [patchRemoved, Arithmetic.eval_any]
  apply exists_congr
  intro v
  rw [Arithmetic.eval, Bool.or_eq_true, eval_patchMember, eval_patchMember,
    eval_relativePair ν m v p q s t hp hq, eval_relativePair ν m v q p t s hq hp]

end ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

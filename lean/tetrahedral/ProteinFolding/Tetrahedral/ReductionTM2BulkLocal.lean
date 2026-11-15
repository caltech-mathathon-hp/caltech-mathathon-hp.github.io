import ProteinFolding.Tetrahedral.ReductionTM2BulkArithmetic

/-! The actual canonical bulk-cover clause as a fixed finite arithmetic
expression. Quantifiers and cardinalities here range only over 3, 4 or 6
fixed entries or the frozen 51 patch pairs. No graph predicate is an opaque
primitive of the machine compiler. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

open Arithmetic
variable {n : ℕ}

def choose (b : Expr n .boolean) (a c : SignedExpr n) : SignedExpr n :=
  ⟨.ite b a.positive c.positive, .ite b a.negative c.negative⟩

def stepPoint (p : PointExpr n) (d : Fin 4) : PointExpr n := fun k =>
  (p k).add (choose (inA p) (SignedExpr.constant (bondVector d k))
    (SignedExpr.constant (-bondVector d k)))

def samePoint (p q : PointExpr n) : Expr n .boolean :=
  Arithmetic.all 3 (fun k => (p k).eq (q k))

def adjacent (p q : PointExpr n) : Expr n .boolean :=
  Arithmetic.any 4 (fun d => samePoint (stepPoint p d) q)

def deleted (m : Expr n .natural) (p : PointExpr n) : Expr n .boolean :=
  .and (inside m p) (Arithmetic.any 4 (fun k => Arithmetic.any 4 (fun j =>
    .and (.bool (decide (k ≠ j)))
      (.or (.and (inA p) (.and ((tetra m p k).eq (radius m)) ((tetra m p j).eq ((radius m).neg))))
        (.and (inB p) (.and ((tetra m p j).eq (lower m))
          ((tetra m p k).eq ((radius m).sub (SignedExpr.constant 1)))))))))

def interior (m : Expr n .natural) (p : PointExpr n) : Expr n .boolean :=
  .and (inside m p) (.not (deleted m p))

def baseDirection (m : Expr n .natural) (p : PointExpr n) (d : Fin 4) : Expr n .boolean :=
  .and (interior m (stepPoint p d)) (.not (.eq (rho m p) (rho m (stepPoint p d))))

def baseCount (m : Expr n .natural) (p : PointExpr n) : Expr n .natural :=
  Arithmetic.count 4 (baseDirection m p)

def danglingDirection (m : Expr n .natural) (p : PointExpr n) (d : Fin 4) : Expr n .boolean :=
  .not (inside m (stepPoint p d))

def danglingCount (m : Expr n .natural) (p : PointExpr n) : Expr n .natural :=
  Arithmetic.count 4 (danglingDirection m p)

def damaged (m : Expr n .natural) (p : PointExpr n) : Expr n .boolean :=
  .and (interior m p) (Arithmetic.any 4 (fun d =>
    .and (deleted m (stepPoint p d)) (.not (.eq (rho m p) (rho m (stepPoint p d))))))

def nonzero (e : SignedExpr n) : Expr n .boolean := .not (e.eq (SignedExpr.constant 0))

def rule (m : Expr n .natural) (p q : PointExpr n) : Expr n .boolean :=
  .and (adjacent p q)
    (.or
      (.and (nonzero (y m p)) (.and (nonzero (z p))
        (.and (((y m q).sub (y m p)).eq ((z p).sign))
          (((z q).sub (z p)).eq (((y m p).sign).neg)))))
      (.and ((z p).eq (SignedExpr.constant 0)) (.and (nonzero (y m p))
        (.and (((y m q).sub (y m p)).eq (((y m p).sign).neg))
          (((z q).sub (z p)).eq (SignedExpr.constant 1))))))

def potential (m : Expr n .natural) (p q : PointExpr n) : Expr n .boolean :=
  .and (interior m q) (.and (rule m p q)
    (.and (.le (baseCount m q) (.nat 1)) (.lt (.nat 0) (danglingCount m q))))

def claimantDirection (m : Expr n .natural) (q : PointExpr n) (d : Fin 4) : Expr n .boolean :=
  .and (damaged m (stepPoint q d)) (potential m (stepPoint q d) q)

def claimantCount (m : Expr n .natural) (q : PointExpr n) : Expr n .natural :=
  Arithmetic.count 4 (claimantDirection m q)

def merge (m : Expr n .natural) (p q : PointExpr n) : Expr n .boolean :=
  .and (damaged m p) (.and (potential m p q) (.eq (claimantCount m q) (.nat 1)))

def patchVertex (m : Expr n .natural) (v : Fin 6) : PointExpr n :=
  let r := radius m
  let o := SignedExpr.constant 0
  match v.val with
  | 0 => ![r.neg, r, o]
  | 1 => ![o, o, o]
  | 2 => ![o, r, r.neg]
  | 3 => ![o, r, r]
  | 4 => ![o, r.add r, o]
  | _ => ![r, r, o]

def relative (m : Expr n .natural) (v : Fin 6) (p : PointExpr n) : PointExpr n :=
  fun k => (p k).sub (patchVertex m v k)

def constantPoint (p : Coordinates) : PointExpr n := fun k => SignedExpr.constant (p k)

noncomputable def patchMember (table : Finset (Coordinates × Coordinates)) (p q : PointExpr n) : Expr n .boolean :=
  Arithmetic.anyList (table.toList.map (fun e =>
    .and (samePoint p (constantPoint e.1)) (samePoint q (constantPoint e.2))))

noncomputable def patchAdded (m : Expr n .natural) (p q : PointExpr n) : Expr n .boolean :=
  Arithmetic.any 6 (fun v => .or
    (patchMember (bulkPatchAdds v) (relative m v p) (relative m v q))
    (patchMember (bulkPatchAdds v) (relative m v q) (relative m v p)))

noncomputable def patchRemoved (m : Expr n .natural) (p q : PointExpr n) : Expr n .boolean :=
  Arithmetic.any 6 (fun v => .or
    (patchMember (bulkPatchRemoves v) (relative m v p) (relative m v q))
    (patchMember (bulkPatchRemoves v) (relative m v q) (relative m v p)))

def rung (m : Expr n .natural) (p q : PointExpr n) : Expr n .boolean :=
  .and (adjacent p q) (.not (.eq (rho m p) (rho m q)))

noncomputable def cover (m : Expr n .natural) (p q : PointExpr n) : Expr n .boolean :=
  .and (interior m p) (.and (interior m q)
    (.or (patchAdded m p q)
      (.and (.or (rung m p q) (.or (merge m p q) (merge m q p))) (.not (patchRemoved m p q)))))

noncomputable def guardedCover (m : Expr n .natural) (p q : PointExpr n) : Expr n .boolean :=
  .and (site p) (.and (site q) (cover m p q))

end ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

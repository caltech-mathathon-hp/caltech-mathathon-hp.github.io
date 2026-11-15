import ProteinFolding.Tetrahedral.ReductionTM2ArithmeticFinite
import ProteinFolding.Tetrahedral.ReductionTM2SignedResidues
import ProteinFolding.Tetrahedral.BulkFastLocal

/-! Fixed finite arithmetic expressions for lattice validity and octahedral
halfspaces. These expressions use only the checked arithmetic compiler. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

open Arithmetic

variable {n : ℕ}

abbrev PointExpr (n : ℕ) := Fin 3 → SignedExpr n

def evalPoint (ν : Fin n → ℕ) (p : PointExpr n) : Coordinates := fun k => SignedExpr.eval ν (p k)

def modulo2Eq (a : SignedExpr n) (r : ℕ) : Expr n .boolean := .eq (a.residue2) (.nat r)
def modulo4Eq (a : SignedExpr n) (r : ℕ) : Expr n .boolean := .eq (a.residue4) (.nat r)

theorem eval_modulo2Eq (ν : Fin n → ℕ) (a : SignedExpr n) (r : ℕ) :
    Arithmetic.eval ν (modulo2Eq a r) = true ↔ SignedExpr.eval ν a % 2 = (r : ℤ) := by
  simp only [modulo2Eq, Arithmetic.eval, decide_eq_true_eq]
  have h := SignedExpr.eval_residue2 ν a
  constructor
  · intro he
    rw [← h, he]
  · intro he
    apply Int.ofNat_inj.mp
    rw [h, he]

theorem eval_modulo4Eq (ν : Fin n → ℕ) (a : SignedExpr n) (r : ℕ) :
    Arithmetic.eval ν (modulo4Eq a r) = true ↔ SignedExpr.eval ν a % 4 = (r : ℤ) := by
  simp only [modulo4Eq, Arithmetic.eval, decide_eq_true_eq]
  have h := SignedExpr.eval_residue4 ν a
  constructor
  · intro he
    rw [← h, he]
  · intro he
    apply Int.ofNat_inj.mp
    rw [h, he]

def coordinateSumExpr (p : PointExpr n) : SignedExpr n :=
  (p 0).add (p 1) |>.add (p 2)

def inA (p : PointExpr n) : Expr n .boolean :=
  .and (Arithmetic.all 3 (fun k => modulo2Eq (p k) 0)) (modulo4Eq (coordinateSumExpr p) 0)

def inB (p : PointExpr n) : Expr n .boolean :=
  .and (Arithmetic.all 3 (fun k => modulo2Eq (p k) 1)) (modulo4Eq (coordinateSumExpr p) 3)

def site (p : PointExpr n) : Expr n .boolean := .or (inA p) (inB p)

theorem eval_coordinateSum (ν : Fin n → ℕ) (p : PointExpr n) :
    SignedExpr.eval ν (coordinateSumExpr p) = coordinateSum (evalPoint ν p) := by
  simp only [coordinateSumExpr, SignedExpr.eval_add, coordinateSum, evalPoint]

theorem eval_inA (ν : Fin n → ℕ) (p : PointExpr n) :
    Arithmetic.eval ν (inA p) = true ↔ InASublattice (evalPoint ν p) := by
  rw [inA, Arithmetic.eval, Bool.and_eq_true, Arithmetic.eval_all, eval_modulo4Eq]
  simp only [eval_coordinateSum]
  exact and_congr (forall_congr' (fun k => eval_modulo2Eq ν (p k) 0)) Iff.rfl

theorem eval_inB (ν : Fin n → ℕ) (p : PointExpr n) :
    Arithmetic.eval ν (inB p) = true ↔ InBSublattice (evalPoint ν p) := by
  rw [inB, Arithmetic.eval, Bool.and_eq_true, Arithmetic.eval_all, eval_modulo4Eq]
  simp only [eval_coordinateSum]
  exact and_congr (forall_congr' (fun k => eval_modulo2Eq ν (p k) 1)) Iff.rfl

theorem eval_site (ν : Fin n → ℕ) (p : PointExpr n) :
    Arithmetic.eval ν (site p) = true ↔ IsLatticeSite (evalPoint ν p) := by
  rw [site, Arithmetic.eval, Bool.or_eq_true, eval_inA ν p, eval_inB ν p]
  rfl

def radius (m : Expr n .natural) : SignedExpr n :=
  (SignedExpr.ofNat (.mul (.nat 2) m)).sub (SignedExpr.constant 2)

def lower (m : Expr n .natural) : SignedExpr n :=
  ((SignedExpr.ofNat (.mul (.nat 2) m)).sub (SignedExpr.constant 1)).neg

def tetra (m : Expr n .natural) (p : PointExpr n) (d : Fin 4) : SignedExpr n :=
  let y := (p 1).sub (radius m)
  if d = 0 then ((p 0).add y).add (p 2)
  else if d = 1 then ((p 0).sub y).sub (p 2)
  else if d = 2 then (((p 0).neg).add y).sub (p 2)
  else (((p 0).neg).sub y).add (p 2)

theorem eval_radius (ν : Fin n → ℕ) (m : Expr n .natural) :
    SignedExpr.eval ν (radius m) = octRadius (Arithmetic.eval ν m) := by
  simp [radius, Arithmetic.eval, octRadius]

theorem eval_lower (ν : Fin n → ℕ) (m : Expr n .natural) :
    SignedExpr.eval ν (lower m) = -(2 * (Arithmetic.eval ν m : ℤ) - 1) := by
  simp [lower, Arithmetic.eval]

theorem eval_tetra (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) (d : Fin 4) :
    SignedExpr.eval ν (tetra m p d) =
      tetraCoordinate (Arithmetic.eval ν m) (evalPoint ν p) d := by
  fin_cases d <;> simp [tetra, tetraCoordinate, eval_radius, evalPoint]

def inside (m : Expr n .natural) (p : PointExpr n) : Expr n .boolean :=
  Arithmetic.all 4 (fun d => .and ((lower m).le (tetra m p d)) ((tetra m p d).le (radius m)))

theorem eval_inside (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) :
    Arithmetic.eval ν (inside m p) = true ↔
      ∀ d : Fin 4, -(2 * (Arithmetic.eval ν m : ℤ) - 1) ≤
        tetraCoordinate (Arithmetic.eval ν m) (evalPoint ν p) d ∧
        tetraCoordinate (Arithmetic.eval ν m) (evalPoint ν p) d ≤ octRadius (Arithmetic.eval ν m) := by
  rw [inside, Arithmetic.eval_all]
  apply forall_congr'
  intro d
  rw [Arithmetic.eval, Bool.and_eq_true, SignedExpr.eval_le, SignedExpr.eval_le]
  simp only [decide_eq_true_eq]
  rw [eval_lower ν m, eval_radius ν m, eval_tetra ν m p d]

def y (m : Expr n .natural) (p : PointExpr n) : SignedExpr n := (p 1).sub (radius m)
def z (p : PointExpr n) : SignedExpr n := (p 2).sub (SignedExpr.constant 1)
def rho (m : Expr n .natural) (p : PointExpr n) : Expr n .natural :=
  .add (SignedExpr.absNat (y m p)) (SignedExpr.absNat (z p))

theorem eval_rho (ν : Fin n → ℕ) (m : Expr n .natural) (p : PointExpr n) :
    (Arithmetic.eval ν (rho m p) : ℤ) =
      |evalPoint ν p 1 - octRadius (Arithmetic.eval ν m)| + |evalPoint ν p 2 - 1| := by
  simp only [rho, Arithmetic.eval, Nat.cast_add, SignedExpr.eval_absNat, y, z,
    SignedExpr.eval_sub, eval_radius, SignedExpr.eval_constant, evalPoint]

end ProteinFolding.Tetrahedral.ReductionTM2.BulkArithmetic

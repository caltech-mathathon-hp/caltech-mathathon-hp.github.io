import ProteinFolding.Tetrahedral.ReductionTM2BulkLocal
import ProteinFolding.Tetrahedral.ReductionTM2Grid

/-! Compile the fixed canonical bulk clause on two unary grid indices.
This machine has no supplied adjacency oracle: its only inputs are the side
parameter and two natural indices, and all local geometry is arithmetic AST. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkPredicate

open Computability Turing TM2CompositionPoly TM2ProductMap Arithmetic BulkArithmetic

abbrev Input := ℕ × (ℕ × ℕ)

def inputEncoding : FinEncoding Input :=
  pairEncoding unaryFinEncodingNat (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)

def fields (x : Input) : Fin 7 → ℕ :=
  ![x.1, Grid.digits (Grid.base x.1) x.2.1 0,
    Grid.digits (Grid.base x.1) x.2.1 1, Grid.digits (Grid.base x.1) x.2.1 2,
    Grid.digits (Grid.base x.1) x.2.2 0, Grid.digits (Grid.base x.1) x.2.2 1,
    Grid.digits (Grid.base x.1) x.2.2 2]

noncomputable def mComputable : TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => x.1) :=
  TM2PairProjections.fstComputable unaryFinEncodingNat Division.inputEncoding

noncomputable def indicesComputable :
    TM2ComputableInPolyTime inputEncoding Division.inputEncoding (fun x : Input => x.2) :=
  TM2PairProjections.sndComputable unaryFinEncodingNat Division.inputEncoding

noncomputable def leftComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => x.2.1) :=
  compose indicesComputable (TM2PairProjections.fstComputable unaryFinEncodingNat unaryFinEncodingNat)

noncomputable def rightComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => x.2.2) :=
  compose indicesComputable (TM2PairProjections.sndComputable unaryFinEncodingNat unaryFinEncodingNat)

noncomputable def fieldComputable : (k : Fin 7) →
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => fields x k)
  | ⟨0, _⟩ => changeFunction mComputable (fun x => rfl)
  | ⟨1, _⟩ => changeFunction (compose (pairComputable mComputable leftComputable) (Grid.digitComputable 0)) (fun x => rfl)
  | ⟨2, _⟩ => changeFunction (compose (pairComputable mComputable leftComputable) (Grid.digitComputable 1)) (fun x => rfl)
  | ⟨3, _⟩ => changeFunction (compose (pairComputable mComputable leftComputable) (Grid.digitComputable 2)) (fun x => rfl)
  | ⟨4, _⟩ => changeFunction (compose (pairComputable mComputable rightComputable) (Grid.digitComputable 0)) (fun x => rfl)
  | ⟨5, _⟩ => changeFunction (compose (pairComputable mComputable rightComputable) (Grid.digitComputable 1)) (fun x => rfl)
  | ⟨6, _⟩ => changeFunction (compose (pairComputable mComputable rightComputable) (Grid.digitComputable 2)) (fun x => rfl)
  | ⟨k + 7, hk⟩ => False.elim (by omega)

def coordinatePoint (a b c : Expr 7 .natural) : PointExpr 7 :=
  let shift := SignedExpr.ofNat (.add (.mul (.nat 2) (.field 0)) (.nat 1))
  ![(SignedExpr.ofNat a).sub shift, (SignedExpr.ofNat b).sub (SignedExpr.constant 3),
    (SignedExpr.ofNat c).sub shift]

def leftPoint : PointExpr 7 := coordinatePoint (.field 1) (.field 2) (.field 3)
def rightPoint : PointExpr 7 := coordinatePoint (.field 4) (.field 5) (.field 6)

theorem eval_leftPoint (x : Input) : evalPoint (fields x) leftPoint = Grid.point x.1 x.2.1 := by
  funext k
  fin_cases k <;> simp [evalPoint, leftPoint, coordinatePoint, fields, Arithmetic.eval,
    Grid.point, Grid.digits]

theorem eval_rightPoint (x : Input) : evalPoint (fields x) rightPoint = Grid.point x.1 x.2.2 := by
  funext k
  fin_cases k <;> simp [evalPoint, rightPoint, coordinatePoint, fields, Arithmetic.eval,
    Grid.point, Grid.digits]

noncomputable def clause : Expr 7 .boolean := guardedCover (.field 0) leftPoint rightPoint

noncomputable def predicate (x : Input) : Bool := Arithmetic.eval (fields x) clause

/-- The actual adjacency-test machine used by the bounded graph walker. -/
noncomputable def computable :
    TM2ComputableInPolyTime inputEncoding finEncodingBoolBool predicate :=
  Arithmetic.computable inputEncoding fields fieldComputable clause

noncomputable def endpointSyntax : Expr 7 .boolean :=
  .and (site leftPoint) (.eq (Arithmetic.count 4 (fun d => cover (.field 0) leftPoint (stepPoint leftPoint d))) (.nat 1))

noncomputable def endpoint (x : Input) : Bool := Arithmetic.eval (fields x) endpointSyntax

noncomputable def endpointComputable : TM2ComputableInPolyTime inputEncoding finEncodingBoolBool endpoint :=
  Arithmetic.computable inputEncoding fields fieldComputable endpointSyntax

def colour (x : Input) : Bool := Arithmetic.eval (fields x) (inA leftPoint)

noncomputable def colourComputable : TM2ComputableInPolyTime inputEncoding finEncodingBoolBool colour :=
  Arithmetic.computable inputEncoding fields fieldComputable (inA leftPoint)

end ProteinFolding.Tetrahedral.ReductionTM2.BulkPredicate

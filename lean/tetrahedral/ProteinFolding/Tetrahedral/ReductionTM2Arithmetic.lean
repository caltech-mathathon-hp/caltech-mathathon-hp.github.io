import ProteinFolding.Tetrahedral.ReductionTM2Basics
import ProteinFolding.Common.TM2Conditional
import ProteinFolding.Common.TM2UnaryComparison
import ProteinFolding.Cubic.Proofs.VerifierPerfectEquality

/-! A finite arithmetic expression compiler for the local bulk predicates.
Expressions are fixed finite syntax; their inputs are unary natural fields.
Structural compilation constructs actual finite TM2 machines and polynomial
runtime bounds, using no evaluator or arithmetic oracle. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Arithmetic

open Computability Turing TM2CompositionPoly TM2ProductMap

inductive Kind where
  | natural | boolean

abbrev Value : Kind → Type
  | .natural => ℕ
  | .boolean => Bool

abbrev encoding : (k : Kind) → FinEncoding (Value k)
  | .natural => unaryFinEncodingNat
  | .boolean => finEncodingBoolBool

inductive Expr (n : ℕ) : Kind → Type
  | field : Fin n → Expr n .natural
  | nat : ℕ → Expr n .natural
  | bool : Bool → Expr n .boolean
  | add : Expr n .natural → Expr n .natural → Expr n .natural
  | mul : Expr n .natural → Expr n .natural → Expr n .natural
  | sub : Expr n .natural → Expr n .natural → Expr n .natural
  | half : Expr n .natural → Expr n .natural
  | eq : Expr n .natural → Expr n .natural → Expr n .boolean
  | lt : Expr n .natural → Expr n .natural → Expr n .boolean
  | le : Expr n .natural → Expr n .natural → Expr n .boolean
  | and : Expr n .boolean → Expr n .boolean → Expr n .boolean
  | or : Expr n .boolean → Expr n .boolean → Expr n .boolean
  | not : Expr n .boolean → Expr n .boolean
  | ite {k : Kind} : Expr n .boolean → Expr n k → Expr n k → Expr n k

def eval {n : ℕ} (ν : Fin n → ℕ) : {k : Kind} → Expr n k → Value k
  | _, .field i => ν i
  | _, .nat c => c
  | _, .bool b => b
  | _, .add a b => eval ν a + eval ν b
  | _, .mul a b => eval ν a * eval ν b
  | _, .sub a b => eval ν a - eval ν b
  | _, .half a => eval ν a / 2
  | _, .eq a b => decide (eval ν a = eval ν b)
  | _, .lt a b => decide (eval ν a < eval ν b)
  | _, .le a b => decide (eval ν a ≤ eval ν b)
  | _, .and a b => eval ν a && eval ν b
  | _, .or a b => eval ν a || eval ν b
  | _, .not a => !eval ν a
  | _, .ite a b c => if eval ν a then eval ν b else eval ν c

variable {X : Type} {n : ℕ} (ex : FinEncoding X) (ν : X → Fin n → ℕ)

/-- Compile each fixed finite arithmetic/Boolean expression from actual field
projection machines. The returned runtime polynomial is built by composition. -/
noncomputable def computable
    (hν : ∀ i, TM2ComputableInPolyTime ex unaryFinEncodingNat (fun x => ν x i)) :
    {k : Kind} → (e : Expr n k) →
      TM2ComputableInPolyTime ex (encoding k) (fun x => eval (ν x) e)
  | _, .field i => hν i
  | _, .nat c => natConstant ex c
  | _, .bool b => TM2Constants.constantComputable ex finEncodingBoolBool b
  | _, .add a b => ReductionTM2.add (computable hν a) (computable hν b)
  | _, .mul a b => ReductionTM2.mul (computable hν a) (computable hν b)
  | _, .sub a b => ReductionTM2.sub (computable hν a) (computable hν b)
  | _, .half a => compose (computable hν a) CubicPacking.UnaryHalf.computable
  | _, .eq a b => compose (pairComputable (computable hν a) (computable hν b))
      PerfectUnaryEquality.unaryEqualityComputable
  | _, .lt a b => compose (pairComputable (computable hν a) (computable hν b))
      TM2UnaryComparison.ltComputable
  | _, .le a b => compose (pairComputable (computable hν a) (computable hν b))
      TM2UnaryComparison.leComputable
  | _, .and a b => compose (pairComputable (computable hν a) (computable hν b))
      TM2Boolean.andComputable
  | _, .or a b => compose (pairComputable (computable hν a) (computable hν b))
      (TM2Boolean.binaryComputable Bool.or)
  | _, .not a => compose (computable hν a) TM2Boolean.notComputable
  | _, .ite a b c => TM2Conditional.iteComputable (computable hν a)
      (computable hν b) (computable hν c)

def mod2 (e : Expr n .natural) : Expr n .natural :=
  .sub e (.mul (.nat 2) (.half e))

def mod4 (e : Expr n .natural) : Expr n .natural :=
  .sub e (.mul (.nat 4) (.half (.half e)))

theorem eval_mod2 (e : Expr n .natural) (u : Fin n → ℕ) :
    eval u (mod2 e) = eval u e % 2 := by
  simp only [mod2, eval]
  rw [Nat.mod_eq_sub_mul_div]

theorem eval_mod4 (e : Expr n .natural) (u : Fin n → ℕ) :
    eval u (mod4 e) = eval u e % 4 := by
  simp only [mod4, eval, Nat.div_div_eq_div_mul]
  rw [Nat.mod_eq_sub_mul_div]

end ProteinFolding.Tetrahedral.ReductionTM2.Arithmetic

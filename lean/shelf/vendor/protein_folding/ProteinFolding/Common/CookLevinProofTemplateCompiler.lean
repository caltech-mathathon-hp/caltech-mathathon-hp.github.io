import ProteinFolding.Common.CookLevinProofFiniteFamilyCompiler
import ProteinFolding.Common.CookLevinProofCNFCompiler

namespace ProteinFolding.SAT.CookLevinTemplateCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap
open CookLevinFiniteFamilyCompiler CookLevinCNFCompiler

def indexedClause {X : Type} (q : ℕ) (indices : Fin q → X → ℕ)
    (positive : Fin q → X → Bool) (x : X) : Clause :=
  (List.finRange q).map (fun i => ⟨indices i x, positive i x⟩)

theorem indexedClause_length {X : Type} (q : ℕ) (indices : Fin q → X → ℕ)
    (positive : Fin q → X → Bool) (x : X) : (indexedClause q indices positive x).length = q := by
  simp [indexedClause]

theorem indexedClause_code {X : Type} (q : ℕ) (indices : Fin q → X → ℕ)
    (positive : Fin q → X → Bool) (x : X) :
    cnfEncoding.encode [indexedClause q indices positive x] =
      (List.finRange q).flatMap (fun i => encodeLit ⟨indices i x, positive i x⟩ ++ [Sym.endLit]) ++ [Sym.endClause] := by
  simp [cnfEncoding, encodeClause, encTerminated, indexedClause, List.flatMap_map]

noncomputable def fixedClauseCompiler {X : Type} {ex : FinEncoding X} (q : ℕ)
    (indices : Fin q → X → ℕ) (positive : Fin q → X → Bool)
    (hi : ∀ i, TM2ComputableInPolyTime ex unaryFinEncodingNat (indices i))
    (hp : ∀ i, TM2ComputableInPolyTime ex finEncodingBoolBool (positive i)) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => [indexedClause q indices positive x]) := by
  let literals := fun i : Fin q => fun x : X => encodeLit ⟨indices i x, positive i x⟩ ++ [Sym.endLit]
  let hl : ∀ i, TM2ComputableInPolyTime ex (wordEncoding Sym) (literals i) :=
    fun i => compose (pairComputable (hi i) (hp i)) terminatedLiteralCompiler
  let hs := fixedWordSequenceCompiler q literals hl
  let ht := appendConstantCompiler hs [Sym.endClause]
  exact
    { toTM2ComputableAux := ht.toTM2ComputableAux
      time := ht.time
      outputsFun x := by
        have hx := ht.outputsFun x
        simpa only [indexedClause_code] using hx }

def skeletonFormula {X : Type} (r : ℕ) (arity : Fin r → ℕ)
    (indices : ∀ j, Fin (arity j) → X → ℕ) (positive : ∀ j, Fin (arity j) → X → Bool) (x : X) : CNF :=
  (List.finRange r).flatMap (fun j => [indexedClause (arity j) (indices j) (positive j) x])

noncomputable def fixedSkeletonCompiler {X : Type} {ex : FinEncoding X} (r : ℕ) (arity : Fin r → ℕ)
    (indices : ∀ j, Fin (arity j) → X → ℕ) (positive : ∀ j, Fin (arity j) → X → Bool)
    (hi : ∀ j i, TM2ComputableInPolyTime ex unaryFinEncodingNat (indices j i))
    (hp : ∀ j i, TM2ComputableInPolyTime ex finEncodingBoolBool (positive j i)) :
    TM2ComputableInPolyTime ex cnfEncoding (skeletonFormula r arity indices positive) :=
  fixedCNFSequenceCompiler r (fun j x => [indexedClause (arity j) (indices j) (positive j) x])
    (fun j => fixedClauseCompiler (arity j) (indices j) (positive j) (hi j) (hp j))

theorem skeletonFormula_width {X : Type} (r : ℕ) (arity : Fin r → ℕ)
    (indices : ∀ j, Fin (arity j) → X → ℕ) (positive : ∀ j, Fin (arity j) → X → Bool)
    (q : ℕ) (hq : ∀ j, arity j ≤ q) (x : X) :
    ∀ c ∈ skeletonFormula r arity indices positive x, c.length ≤ q := by
  intro c hc
  obtain ⟨j, _, hc⟩ := List.mem_flatMap.mp hc
  have he := List.mem_singleton.mp hc
  subst c
  rw [indexedClause_length]
  exact hq j

end ProteinFolding.SAT.CookLevinTemplateCompiler

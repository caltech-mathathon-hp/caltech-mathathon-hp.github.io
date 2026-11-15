import ProteinFolding.Common.CookLevinProofWidthThreeCompilerCorrectness
import ProteinFolding.Common.CookLevinProofVerifierCompilerBounds

namespace ProteinFolding.SAT.CookLevinUniversalWidthThree

open Computability Turing TM2CompositionPoly TM2ProductMap CookLevinVerifierCompiler
  CookLevinVerifierCompilerBounds CookLevinNPFormula CookLevinNPFormulaSize CookLevinVerifierBridge
  CookLevinSize

section Verifier

variable {A C : Type} {ea : FinEncoding A} {ec : FinEncoding C} {f : A × C → Bool}
  (h : TM2ComputableInPolyTime (pairEncoding ea ec) finEncodingBoolBool f)

noncomputable def formula (p : Polynomial ℕ) (x : A) : CNF :=
  CookLevinWidthThreeCompiler.formula (3 * domainBound h.tm + 1)
    (arithmeticVerifierFormula h p x,
      (variableBoundPolynomial h p).eval (ea.encode x).length)

noncomputable def computable (p : Polynomial ℕ) :
    TM2ComputableInPolyTime ea cnfEncoding (formula h p) := by
  simpa only [Function.comp_def, formula] using compose
    (pairComputable (CookLevinVerifierCompiler.computable h p) (variableBoundCompiler h p))
    (CookLevinWidthThreeCompiler.computable (3 * domainBound h.tm + 1))

theorem formula_satisfiable_iff (p : Polynomial ℕ) (x : A) :
    Satisfiable (formula h p x) ↔ Satisfiable (arithmeticVerifierFormula h p x) :=
  CookLevinWidthThreeCompilerCorrectness.formula_equisatisfiable (3 * domainBound h.tm + 1)
    (arithmeticVerifierFormula h p x) ((variableBoundPolynomial h p).eval (ea.encode x).length)
    (arithmeticVerifierFormula_width h p x) (arithmeticVerifierFormula_vars_lt h p x)

theorem formula_width (p : Polynomial ℕ) (x : A) : ThreeCNF.WidthAtMostThree (formula h p x) :=
  CookLevinWidthThreeCompiler.formula_width (3 * domainBound h.tm + 1) _

end Verifier

theorem inNP_karp (A : Type) (ea : FinEncoding A) (L : A → Prop) (hnp : InNP ea L) :
    KarpReduces ea cnfEncoding L (fun φ => ThreeCNF.WidthAtMostThree φ ∧ Satisfiable φ) := by
  obtain ⟨C, ec, p, f, h, _, hL⟩ := inNP_word_verifier ea L hnp
  refine ⟨formula h p, ⟨computable h p⟩, ?_⟩
  intro x
  have hs : Satisfiable (formula h p x) ↔ L x :=
    ((formula_satisfiable_iff h p x).trans (arithmeticVerifierFormula_satisfiable h p x)).trans
      ((verifierFormula_words_iff h p x).trans (hL x).symm)
  exact ⟨fun hx => ⟨formula_width h p x, hs.mpr hx⟩, fun hx => hs.mp hx.2⟩

theorem npHard : NPHard cnfEncoding (fun φ => ThreeCNF.WidthAtMostThree φ ∧ Satisfiable φ) := by
  intro A ea L hnp
  exact inNP_karp A ea L hnp

end ProteinFolding.SAT.CookLevinUniversalWidthThree

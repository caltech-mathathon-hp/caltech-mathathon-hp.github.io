import ProteinFolding.Common.CookLevinProofVerifierCompiler

namespace ProteinFolding.SAT.CookLevinVerifierCompilerBounds

open Computability Turing CookLevinRows CookLevinRowRename CookLevinNPFormula
  CookLevinNPFormulaSize CookLevinVerifierCompiler CookLevinVerifierBridge CookLevinSize
  CookLevinArithmeticCompiler

variable {A C : Type} {ea : FinEncoding A} {ec : FinEncoding C} {f : A × C → Bool}
  (h : TM2ComputableInPolyTime (pairEncoding ea ec) finEncodingBoolBool f)

theorem arithmeticVerifierFormula_width (p : Polynomial ℕ) (x : A) :
    ∀ c ∈ arithmeticVerifierFormula h p x, c.length ≤ 3 * domainBound h.tm + 1 := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa only [renameClause, List.length_map] using verifierFormula_width h p x d hd

theorem arithmeticVerifierFormula_vars_lt (p : Polynomial ℕ) (x : A) :
    ∀ c ∈ arithmeticVerifierFormula h p x, ∀ l ∈ c,
      l.var < (variableBoundPolynomial h p).eval (ea.encode x).length := by
  intro c hc l hl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
  have ho := verifierFormula_vars_lt h p x d hd v hv
  rw [variableBoundPolynomial_eval] at ho ⊢
  exact (renameIndex_lt_iff h.tm (stackBound h p x) (uniformTime h p x + 1) v.var).mpr ho

noncomputable def variableBoundCompiler (p : Polynomial ℕ) :
    TM2ComputableInPolyTime ea unaryFinEncodingNat
      (fun x => (variableBoundPolynomial h p).eval (ea.encode x).length) :=
  encodedPolynomialComputable ea (variableBoundPolynomial h p)

end ProteinFolding.SAT.CookLevinVerifierCompilerBounds

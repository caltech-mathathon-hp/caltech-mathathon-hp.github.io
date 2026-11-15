import ProteinFolding.Common.CookLevinProofCertificateSize
import ProteinFolding.Common.CookLevinProofNPFormula

/-! Actual binary encoding, index and fixed clause-width bounds for the CNF
of every original polynomial-time verifier, including its variable certificate
boundary. These are size bounds, not a substitute for the emitter runtime. -/

namespace ProteinFolding.SAT.CookLevinNPFormulaSize

open Computability Turing TM2 Polynomial CookLevinRows CookLevinSize CookLevinCertificateSize
open CookLevinNPFormula CookLevinVerifierBridge CookLevinBoundedRunCNF

variable {A C : Type} {ea : FinEncoding A} {ec : FinEncoding C} {f : A × C → Bool}
  (h : TM2ComputableInPolyTime (pairEncoding ea ec) finEncodingBoolBool f)

noncomputable def uniformTimePolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  h.time.comp (X + p + Polynomial.C 1)

theorem uniformTimePolynomial_eval (p : Polynomial ℕ) (x : A) :
    (uniformTimePolynomial h p).eval (ea.encode x).length = uniformTime h p x := by
  simp only [uniformTimePolynomial, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, uniformTime]

noncomputable def stackBoundPolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  X + Polynomial.C 1 + p + uniformTimePolynomial h p * Polynomial.C (TM2Bounds.machinePushBound h.tm)

theorem stackBoundPolynomial_eval (p : Polynomial ℕ) (x : A) :
    (stackBoundPolynomial h p).eval (ea.encode x).length = stackBound h p x := by
  simp only [stackBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, uniformTimePolynomial_eval, stackBound]

noncomputable def variableBoundPolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  (uniformTimePolynomial h p + Polynomial.C 1) *
    (Polynomial.C (widthBase h.tm) + stackBoundPolynomial h p * Polynomial.C (widthSlope h.tm))

theorem variableBoundPolynomial_eval (p : Polynomial ℕ) (x : A) :
    (variableBoundPolynomial h p).eval (ea.encode x).length =
      (uniformTime h p x + 1) * width h.tm (stackBound h p x) := by
  simp only [variableBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    uniformTimePolynomial_eval, stackBoundPolynomial_eval, width_linear]

theorem verifierFormula_vars_lt (p : Polynomial ℕ) (x : A) :
    ∀ c ∈ verifierFormula h p x, ∀ l ∈ c,
      l.var < (variableBoundPolynomial h p).eval (ea.encode x).length := by
  classical
  rw [variableBoundPolynomial_eval]
  unfold verifierFormula
  split
  · exact boundedRunCNF_vars_lt h.tm _ _ _ _ _ _ _ _
  · simp

theorem verifierFormula_width (p : Polynomial ℕ) (x : A) :
    ∀ c ∈ verifierFormula h p x, c.length ≤ 3 * domainBound h.tm + 1 := by
  classical
  unfold verifierFormula
  split
  · exact boundedRunCNF_width h.tm _ _ _ _ _ _ _ _
  · simp

noncomputable def encodedBoundPolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  boundedRunBoundPolynomial h.tm (stackBoundPolynomial h p) (uniformTimePolynomial h p) + Polynomial.C 1

theorem verifierFormula_encoded_bound (p : Polynomial ℕ) (x : A) :
    (cnfEncoding.encode (verifierFormula h p x)).length ≤
      (encodedBoundPolynomial h p).eval (ea.encode x).length := by
  classical
  simp only [encodedBoundPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    boundedRunBoundPolynomial_eval, stackBoundPolynomial_eval, uniformTimePolynomial_eval]
  unfold verifierFormula
  split
  · exact (boundedRunCNF_encoded_bound h.tm _ _ _ _ _ _ _ _).trans (Nat.le_add_right _ _)
  · have he : (cnfEncoding.encode ([[]] : CNF)).length = 1 := rfl
    rw [he]
    omega

theorem verifierFormula_encoded_polynomial (p : Polynomial ℕ) :
    ∃ q : Polynomial ℕ, ∀ x : A,
      (cnfEncoding.encode (verifierFormula h p x)).length ≤ q.eval (ea.encode x).length :=
  ⟨encodedBoundPolynomial h p, verifierFormula_encoded_bound h p⟩

/-- Every original NP language has this exact semantic CNF family with proved
polynomial binary encoding and index bounds and constant clause width. The
actual uniform frontend machine remains a separate obligation. -/
theorem inNP_formula_bounded {A : Type} (ea : FinEncoding A) (L : A → Prop) (hnp : InNP ea L) :
    ∃ (F : A → CNF) (q v : Polynomial ℕ) (Q : ℕ), ∀ x,
      (L x ↔ Satisfiable (F x)) ∧
      (cnfEncoding.encode (F x)).length ≤ q.eval (ea.encode x).length ∧
      (∀ c ∈ F x, c.length ≤ Q) ∧
      ∀ c ∈ F x, ∀ l ∈ c, l.var < v.eval (ea.encode x).length := by
  obtain ⟨C, ec, p, f, h, _, hL⟩ := inNP_word_verifier ea L hnp
  refine ⟨verifierFormula h p, encodedBoundPolynomial h p, variableBoundPolynomial h p,
    3 * domainBound h.tm + 1, fun x => ?_⟩
  exact ⟨(hL x).trans (verifierFormula_words_iff h p x).symm,
    verifierFormula_encoded_bound h p x, verifierFormula_width h p x, verifierFormula_vars_lt h p x⟩

end ProteinFolding.SAT.CookLevinNPFormulaSize

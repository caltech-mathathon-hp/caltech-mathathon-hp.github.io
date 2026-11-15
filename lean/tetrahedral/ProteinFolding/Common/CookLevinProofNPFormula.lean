import ProteinFolding.Common.CookLevinProofBoundedRunCNF
import ProteinFolding.Common.CookLevinProofVerifierBridge

/-! A concrete CNF for every input of every original InNP verifier. The
certificate remains a variable word over its original finite alphabet. The
accepting configuration's support is checked once for the fixed machine; an
unreachable accepting symbol gives the fixed unsatisfiable formula.
Polynomial-time generation of these concrete clauses is a separate compiler
obligation; it is not assumed in the proved semantic equivalence below.
-/

namespace ProteinFolding.SAT.CookLevinNPFormula

open Computability Turing TM2 CookLevinAlphabet CookLevinPadded CookLevinCertificateCells
open CookLevinVerifierBridge CookLevinBoundedRunCNF

variable {A C : Type} {ea : FinEncoding A} {ec : FinEncoding C} {f : A × C → Bool}
  (h : TM2ComputableInPolyTime (pairEncoding ea ec) finEncodingBoolBool f)

noncomputable def headerSymbols (x : A) : List (Symbol h.tm h.tm.k₀) :=
  (inputHeader h x).map (inputSymbol h.tm)

noncomputable def certificateSymbol (b : ec.Γ) : Symbol h.tm h.tm.k₀ :=
  inputSymbol h.tm (certificateLetter h b)

theorem headerSymbols_length (x : A) : (headerSymbols h x).length = (ea.encode x).length + 1 := by
  simp [headerSymbols, inputHeader]

theorem symbolicInput_eq (x : A) (w : List ec.Γ) :
    ((headerSymbols h x ++ w.map (certificateSymbol h)).map Subtype.val) = verifierInput h x w := by
  simp only [headerSymbols, certificateSymbol, List.map_append, List.map_map, Function.comp_def,
    inputSymbol, verifierInput]
  change (inputHeader h x).map id ++ w.map (certificateLetter h) = _
  rw [List.map_id]

noncomputable def stackBound (p : Polynomial ℕ) (x : A) : ℕ :=
  (ea.encode x).length + 1 + p.eval (ea.encode x).length +
    uniformTime h p x * TM2Bounds.machinePushBound h.tm

theorem headerBound (p : Polynomial ℕ) (x : A) :
    (headerSymbols h x).length + p.eval (ea.encode x).length ≤ stackBound h p x := by
  rw [headerSymbols_length]
  exact Nat.le_add_right _ _

theorem stackBound_pos (p : Polynomial ℕ) (x : A) : 1 ≤ stackBound h p x := by
  unfold stackBound
  omega

theorem acceptedConfig_stack_length (k : h.tm.K) :
    ((acceptedConfig h).stk k).length ≤ 1 := by
  by_cases hk : k = h.tm.k₁
  · subst k; simp [acceptedConfig, haltList]
  · simp [acceptedConfig, haltList, hk]

noncomputable def verifierFormula (p : Polynomial ℕ) (x : A) : CNF := by
  classical
  exact if hs : StacksIn (machineSymbols h.tm) (acceptedConfig h).stk then
    boundedRunCNF h.tm (stackBound h p x) (uniformTime h p x) (certificateSymbol h)
      (headerSymbols h x) (p.eval (ea.encode x).length) (headerBound h p x) (acceptedConfig h) hs
    else [[]]

/-- This concrete CNF is satisfiable exactly when some bounded certificate
word makes the actual verifier machine accept at the uniform horizon. -/
theorem verifierFormula_words_iff (p : Polynomial ℕ) (x : A) :
    Satisfiable (verifierFormula h p x) ↔
      ∃ w : List ec.Γ, w.length ≤ p.eval (ea.encode x).length ∧
        (paddedStep h.tm)^[uniformTime h p x] (initList h.tm (verifierInput h x w)) = acceptedConfig h := by
  classical
  unfold verifierFormula
  split
  · rename_i hs
    rw [boundedRunCNF_satisfiable_iff h.tm (stackBound h p x) (uniformTime h p x)
      (certificateSymbol h) (headerSymbols h x) (p.eval (ea.encode x).length) (headerBound h p x)
      (acceptedConfig h) hs (by rw [headerSymbols_length]; exact le_rfl)
      (fun k => (acceptedConfig_stack_length h k).trans (stackBound_pos h p x))]
    simp only [symbolicInput_eq]
  · rename_i hs
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨l, hl, _⟩ := ha [] (List.mem_singleton_self _)
      simp at hl
    · rintro ⟨w, _, hr⟩
      have hsrun := paddedRun_stacksIn h.tm (verifierInput h x w) (uniformTime h p x)
      rw [hr] at hsrun
      exact False.elim (hs hsrun)

theorem verifierFormula_iff (p : Polynomial ℕ) (hs : Function.Surjective ec.encode) (x : A) :
    Satisfiable (verifierFormula h p x) ↔
      ∃ c : C, (ec.encode c).length ≤ p.eval (ea.encode x).length ∧ f (x, c) = true := by
  rw [verifierFormula_words_iff, ← verifier_words_iff h p hs x]

/-- Every unchanged InNP source has the explicitly constructed CNF family
with exact yes/no semantics. The machine-generation proof is still separate. -/
theorem inNP_formula_semantics {A : Type} (ea : FinEncoding A) (L : A → Prop) (hnp : InNP ea L) :
    ∃ F : A → CNF, ∀ x, L x ↔ Satisfiable (F x) := by
  obtain ⟨C, ec, p, f, h, _, hL⟩ := inNP_word_verifier ea L hnp
  exact ⟨verifierFormula h p, fun x => (hL x).trans (verifierFormula_words_iff h p x).symm⟩

end ProteinFolding.SAT.CookLevinNPFormula

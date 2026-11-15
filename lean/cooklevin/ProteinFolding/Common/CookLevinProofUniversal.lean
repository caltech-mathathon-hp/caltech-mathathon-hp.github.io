import ProteinFolding.Common.CookLevinProofVerifierCompiler

/-! Unconditional Cook--Levin for the original universal finite-TM2 definition
of NP-hardness. The complete emitter is an actual polynomial-time machine;
the source's certificate encoding and required surjectivity are preserved. -/

namespace ProteinFolding.SAT.CookLevinUniversal

open Computability Turing CookLevinVerifierBridge CookLevinNPFormula CookLevinVerifierCompiler

theorem inNP_karp (A : Type) (ea : FinEncoding A) (L : A → Prop) (hnp : InNP ea L) :
    KarpReduces ea cnfEncoding L Satisfiable := by
  obtain ⟨C, ec, p, f, h, _, hL⟩ := inNP_word_verifier ea L hnp
  refine ⟨arithmeticVerifierFormula h p, ⟨computable h p⟩, ?_⟩
  intro x
  rw [arithmeticVerifierFormula_satisfiable]
  exact (hL x).trans (verifierFormula_words_iff h p x).symm

theorem cookLevin : CookLevin := by
  intro A ea L hnp
  exact inNP_karp A ea L hnp

end ProteinFolding.SAT.CookLevinUniversal

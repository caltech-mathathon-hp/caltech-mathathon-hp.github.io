import ProteinFolding.Common.CookLevinProofVerifierBoundaryCompiler

open ProteinFolding.SAT Turing
open CookLevinAlphabet CookLevinBoundaryCompiler CookLevinCertificateFactorCompiler

example (tm : FinTM2) (M H : ℕ) : noHoleFactorsCNF tm M H 0 = [] := rfl

example (tm : FinTM2) (M H : ℕ) : noHoleFactorsCNF tm M H 1 = [] := by
  simp [noHoleFactorsCNF, List.range_succ]

example (tm : FinTM2) (M H : ℕ) :
    noHoleFactorsCNF tm M H 2 = noHoleCNF tm M H 0 1 := by
  simp [noHoleFactorsCNF, List.range_succ]

example {C : Type} (tm : FinTM2) (M H : ℕ) (e : C → Symbol tm tm.k₀) :
    certificateFactorsCNF tm M e H 0 = [] := rfl

example (tm : FinTM2) (M : ℕ) : headerPins tm M [] = [] := rfl

example (tm : FinTM2) (H B : ℕ) : suffixPins tm 0 H B = [] := rfl

import ProteinFolding.Common.CookLevinProofGlobalCompiler
import ProteinFolding.Common.CookLevinProofFinalCompiler
import ProteinFolding.Common.CookLevinProofVerifierBoundaryCompiler

/-! The actual complete CNF emitter for every original polynomial verifier.
The emitted formula is a bijective variable renaming of the unchanged semantic
verifierFormula. All certificate, boundary, row and transition machines are
instantiated with their proved polynomial numeric and header compilers. -/

namespace ProteinFolding.SAT.CookLevinVerifierCompiler

open Computability Turing TM2 CookLevinAlphabet CookLevinNPFormula CookLevinVerifierBridge
  CookLevinRowRename CookLevinGlobalCNF CookLevinBoundedRunCNF CookLevinFactorThree
  CookLevinVerifierBoundaryCompiler

variable {A C : Type} {ea : FinEncoding A} {ec : FinEncoding C} {f : A × C → Bool}
  (h : TM2ComputableInPolyTime (pairEncoding ea ec) finEncodingBoolBool f)

noncomputable def arithmeticVerifierFormula (p : Polynomial ℕ) (x : A) : CNF :=
  renameCNF (renameIndex h.tm (stackBound h p x)) (verifierFormula h p x)

noncomputable def computable (p : Polynomial ℕ) :
    TM2ComputableInPolyTime ea cnfEncoding (arithmeticVerifierFormula h p) := by
  classical
  by_cases hs : StacksIn (machineSymbols h.tm) (acceptedConfig h).stk
  · let hc := verifierCertificateCNFCompiler h p
    let hg := CookLevinGlobalCompiler.arithmeticGlobalCNFCompiler h.tm
      (stackBound h p) (uniformTime h p) (stackBoundCompiler h p) (uniformTimeCompiler h p)
    let hf := CookLevinFinalCompiler.finalBindingsCompiler h.tm
      (stackBound h p) (uniformTime h p) (acceptedConfig h) hs
      (stackBoundCompiler h p) (uniformTimeCompiler h p)
    let hm := appendCompiler (appendCompiler hc hg) hf
    have he : arithmeticVerifierFormula h p =
        (fun x => renameCNF (renameIndex h.tm (stackBound h p x))
          (CookLevinCertificateCNF.certificateCNF h.tm (stackBound h p x) (certificateSymbol h)
            (headerSymbols h x) (p.eval (ea.encode x).length) (headerBound h p x)) ++
          arithmeticGlobalCNF h.tm (stackBound h p x) (uniformTime h p x) ++
          renameCNF (renameIndex h.tm (stackBound h p x))
            (CookLevinCircuit.pins (boundaryBindings h.tm (stackBound h p x)
              (uniformTime h p x) (acceptedConfig h) hs))) := by
      funext x
      simp only [arithmeticVerifierFormula, verifierFormula, dif_pos hs, boundedRunCNF,
        CookLevinGlobalCompiler.rename_append, arithmeticGlobalCNF]
    rw [he]
    exact hm
  · have he : arithmeticVerifierFormula h p = (fun _ => ([[]] : CNF)) := by
      funext x
      simp only [arithmeticVerifierFormula, verifierFormula, dif_neg hs, renameCNF,
        renameClause, List.map_cons, List.map_nil]
    rw [he]
    exact TM2Constants.constantComputable ea cnfEncoding [[]]

theorem arithmeticVerifierFormula_satisfiable (p : Polynomial ℕ) (x : A) :
    Satisfiable (arithmeticVerifierFormula h p x) ↔ Satisfiable (verifierFormula h p x) :=
  renameCNF_satisfiable (renameIndex h.tm (stackBound h p x)) (verifierFormula h p x)

end ProteinFolding.SAT.CookLevinVerifierCompiler

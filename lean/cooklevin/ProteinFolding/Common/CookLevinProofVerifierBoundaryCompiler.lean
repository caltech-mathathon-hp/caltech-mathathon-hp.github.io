import ProteinFolding.Common.CookLevinProofBoundaryCompiler
import ProteinFolding.Common.CookLevinProofNPFormulaSize
import ProteinFolding.Common.CookLevinProofCertificateFactorCompiler

/-! Actual polynomial machines for the original verifier's concrete header,
certificate bound, stack bound and common horizon. Header letters are mapped
from the original encoding and the pair separator is appended explicitly. -/

namespace ProteinFolding.SAT.CookLevinVerifierBoundaryCompiler

open Computability Turing Polynomial TM2CompositionPoly TM2ProductMap
open CookLevinAlphabet CookLevinNPFormula CookLevinNPFormulaSize CookLevinVerifierBridge
open CookLevinCertificateCells
open CookLevinArithmeticCompiler CookLevinBoundaryCompiler
open CookLevinCertificateFactorCompiler CookLevinRowRename CookLevinCertificateCNF

variable {A C : Type} {ea : FinEncoding A} {ec : FinEncoding C} {f : A × C → Bool}
  (h : TM2ComputableInPolyTime (pairEncoding ea ec) finEncodingBoolBool f)

noncomputable def headerSymbolsCompiler :
    TM2ComputableInPolyTime ea (wordEncoding (Symbol h.tm h.tm.k₀)) (headerSymbols h) := by
  letI := ea.ΓFin
  let hm := TM2WordMap.mapComputable (fun b : ea.Γ =>
    inputSymbol h.tm (h.inputAlphabet.symm (.left b)))
  let hp := compose (TM2EncodingWords.encodeComputable ea) hm
  let hs := TM2Constants.constantComputable ea (wordEncoding (Symbol h.tm h.tm.k₀))
    [inputSymbol h.tm (h.inputAlphabet.symm .sep)]
  let hc := compose (pairComputable hp hs) (TM2PairProjections.concatComputable (Symbol h.tm h.tm.k₀))
  change TM2ComputableInPolyTime ea (wordEncoding (Symbol h.tm h.tm.k₀)) (fun x => headerSymbols h x)
  simpa only [Function.comp_def, headerSymbols, inputHeader, List.map_append, List.map_map,
    List.map_cons, List.map_nil] using hc

noncomputable def stackBoundCompiler (p : Polynomial ℕ) :
    TM2ComputableInPolyTime ea unaryFinEncodingNat (stackBound h p) := by
  simpa only [stackBoundPolynomial_eval] using encodedPolynomialComputable ea (stackBoundPolynomial h p)

noncomputable def uniformTimeCompiler (p : Polynomial ℕ) :
    TM2ComputableInPolyTime ea unaryFinEncodingNat (uniformTime h p) := by
  simpa only [uniformTimePolynomial_eval] using encodedPolynomialComputable ea (uniformTimePolynomial h p)

noncomputable def certificateBoundCompiler (p : Polynomial ℕ) :
    TM2ComputableInPolyTime ea unaryFinEncodingNat (fun x => p.eval (ea.encode x).length) :=
  encodedPolynomialComputable ea p

noncomputable def headerLengthCompiler :
    TM2ComputableInPolyTime ea unaryFinEncodingNat (fun x => (headerSymbols h x).length) := by
  let hl := compose (headerSymbolsCompiler h)
    (lengthComputable (wordEncoding (Symbol h.tm h.tm.k₀)))
  exact hl

noncomputable def verifierCertificatePinsCompiler (p : Polynomial ℕ) :
    TM2ComputableInPolyTime ea cnfEncoding (fun x => certificatePins h.tm (stackBound h p x)
      (headerSymbols h x) (p.eval (ea.encode x).length)) :=
  certificatePinsCompiler h.tm (stackBound h p) (fun x => p.eval (ea.encode x).length)
    (headerSymbols h) (stackBoundCompiler h p) (certificateBoundCompiler p) (headerSymbolsCompiler h)

noncomputable def verifierCertificateCNFCompiler (p : Polynomial ℕ) :
    TM2ComputableInPolyTime ea cnfEncoding (fun x => renameCNF (renameIndex h.tm (stackBound h p x))
      (certificateCNF h.tm (stackBound h p x) (certificateSymbol h) (headerSymbols h x)
        (p.eval (ea.encode x).length) (headerBound h p x))) :=
  certificateCNFCompiler h.tm (stackBound h p) (fun x => p.eval (ea.encode x).length)
    (headerSymbols h) (certificateSymbol h) (headerBound h p) (stackBoundCompiler h p)
    (certificateBoundCompiler p) (headerSymbolsCompiler h)

end ProteinFolding.SAT.CookLevinVerifierBoundaryCompiler

import ProteinFolding.Common.CookLevinProofRangeCompiler
import ProteinFolding.Common.CookLevinProofFiniteFamilyCompiler

/-! Actual finite TM2 compilation of bounded natural-index CNF loops and
fixed finite-domain loops, preserving a common encoded parameter. -/

namespace ProteinFolding.SAT.CookLevinRangeCNFCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap CookLevinMapCompiler
  CookLevinFiniteFamilyCompiler

noncomputable def rangeCNFCompiler {X : Type} {ex : FinEncoding X} (bound : X → ℕ)
    (f : X × ℕ → CNF) (hb : TM2ComputableInPolyTime ex unaryFinEncodingNat bound)
    (hf : TM2ComputableInPolyTime (pairEncoding ex unaryFinEncodingNat) cnfEncoding f) :
    TM2ComputableInPolyTime ex cnfEncoding
      (fun x => (List.range (bound x)).flatMap (fun i => f (x, i))) := by
  let hr := compose hb CookLevinRangeCompiler.computable
  let hp := pairComputable (idComputableInPolyTime ex) hr
  exact compose (f := fun x => (x, List.range (bound x)))
    (g := fun p : X × List ℕ => p.2.flatMap (fun i => f (p.1, i)))
    hp (parameterizedCNFCompiler hf)

noncomputable def fixedListCNFCompiler {X I : Type} [Fintype I] {ex : FinEncoding X}
    (xs : List I) (f : I → X → CNF)
    (hf : ∀ i, TM2ComputableInPolyTime ex cnfEncoding (f i)) :
    TM2ComputableInPolyTime ex cnfEncoding (fun x => xs.flatMap (fun i => f i x)) := by
  let hc := finiteFamilyComputable ex (symbolEncoding I) cnfEncoding f hf
  let hl := parameterizedCNFCompiler hc
  let hp := pairComputable (idComputableInPolyTime ex)
    (TM2Constants.constantComputable ex (TM2ListMap.listEncoding (symbolEncoding I)) xs)
  exact compose (f := fun x : X => (x, xs))
    (g := fun p : X × List I => p.2.flatMap (fun i => f i p.1)) hp hl

end ProteinFolding.SAT.CookLevinRangeCNFCompiler

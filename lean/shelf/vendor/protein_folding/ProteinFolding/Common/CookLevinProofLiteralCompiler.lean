import ProteinFolding.Common.CookLevinProofMapCompiler
import ProteinFolding.Common.TM2UnaryToBinary
import ProteinFolding.Common.TM2WordSubstitution
import ProteinFolding.Common.TM2WordMap
import ProteinFolding.Common.TM2ProductMap

/-! Actual polynomial TM2 code emission for binary-indexed CNF literals.
Indices are supplied in unary by the bounded tableau loops. The emitted index
is the frozen canonical binary encodeNat, followed by the exact CNF delimiters.
-/

namespace ProteinFolding.SAT.CookLevinLiteralCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap

def unaryLiteralEncoding : FinEncoding (ℕ × Bool) := pairEncoding unaryFinEncodingNat finEncodingBoolBool

noncomputable def binaryDigitsComputable :
    TM2ComputableInPolyTime finEncodingNatBool (wordEncoding Sym)
      (fun n => (encodeNat n).map Sym.bit) := by
  let hm := TM2WordMap.mapComputable Sym.bit
  exact
    { toTM2ComputableAux := hm.toTM2ComputableAux
      time := hm.time
      outputsFun n := hm.outputsFun (encodeNat n) }

noncomputable def unaryDigitsComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat (wordEncoding Sym)
      (fun n => (encodeNat n).map Sym.bit) :=
  compose (f := (id : ℕ → ℕ)) (g := fun n : ℕ => (encodeNat n).map Sym.bit)
    TM2UnaryToBinary.unaryToBinaryComputable binaryDigitsComputable

noncomputable def negativePrefixComputable :
    TM2ComputableInPolyTime finEncodingBoolBool (wordEncoding Sym)
      (fun b => if b then [] else [Sym.neg]) := by
  letI : Inhabited Sym := ⟨.endLit⟩
  let hs := TM2WordSubstitution.flatMapComputable
    (fun b : Bool => if b then [] else [Sym.neg]) 1 (by intro b; cases b <;> simp)
  exact
    { toTM2ComputableAux := hs.toTM2ComputableAux
      time := hs.time
      outputsFun b := by
        simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hs.outputsFun [b] }

noncomputable def literalCodeComputable :
    TM2ComputableInPolyTime unaryLiteralEncoding (wordEncoding Sym)
      (fun nb => encodeLit ⟨nb.1, nb.2⟩) := by
  let hp := compose (TM2PairProjections.sndComputable unaryFinEncodingNat finEncodingBoolBool)
    negativePrefixComputable
  let hd := compose (TM2PairProjections.fstComputable unaryFinEncodingNat finEncodingBoolBool)
    unaryDigitsComputable
  exact compose (pairComputable hp hd) (TM2PairProjections.concatComputable Sym)

theorem singletonCNF_code (n : ℕ) (b : Bool) :
    cnfEncoding.encode [[⟨n, b⟩]] = encodeLit ⟨n, b⟩ ++ [Sym.endLit, Sym.endClause] := by
  simp [cnfEncoding, encodeClause, encTerminated, List.append_assoc]

noncomputable def singletonWordComputable :
    TM2ComputableInPolyTime unaryLiteralEncoding (wordEncoding Sym)
      (fun nb => cnfEncoding.encode [[⟨nb.1, nb.2⟩]]) := by
  let ht := TM2Constants.constantComputable unaryLiteralEncoding (wordEncoding Sym) [Sym.endLit, Sym.endClause]
  let hm := compose (pairComputable literalCodeComputable ht) (TM2PairProjections.concatComputable Sym)
  have he : (fun nb : ℕ × Bool => encodeLit ⟨nb.1, nb.2⟩ ++ [Sym.endLit, Sym.endClause]) =
      (fun nb : ℕ × Bool => cnfEncoding.encode [[⟨nb.1, nb.2⟩]]) := by
    funext nb
    exact (singletonCNF_code nb.1 nb.2).symm
  rw [← he]
  exact hm

/-- This is an actual machine and polynomial time witness for a CNF fragment,
not a computability assumption about the literal encoder. -/
noncomputable def singletonCNFComputable :
    TM2ComputableInPolyTime unaryLiteralEncoding cnfEncoding
      (fun nb => [[⟨nb.1, nb.2⟩]]) where
  toTM2ComputableAux := singletonWordComputable.toTM2ComputableAux
  time := singletonWordComputable.time
  outputsFun nb := singletonWordComputable.outputsFun nb

end ProteinFolding.SAT.CookLevinLiteralCompiler

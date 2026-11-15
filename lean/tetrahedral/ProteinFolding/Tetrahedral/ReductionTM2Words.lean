import ProteinFolding.Tetrahedral.ReductionTM2Parameters
import ProteinFolding.Common.TM2UnaryRange
import ProteinFolding.Common.TM2ListMap

namespace ProteinFolding.Tetrahedral.ReductionTM2

open Computability Turing TM2CompositionPoly TM2ProductMap

namespace Raw

def framePart1 (p : Parameters) : Sequence :=
  [.H] ++ List.replicate 6 .P ++ List.replicate 3 .H ++
    repeatWord (List.replicate 6 .P ++ List.replicate 4 .H) p.1 ++
    List.replicate 6 .P ++ List.replicate (frameTail1 p) .H ++ List.replicate 3 .P ++ [.H]
def framePart2 (p : Parameters) : Sequence :=
  List.replicate 3 .P ++ List.replicate (frameTail2 p) .H ++
    repeatWord (List.replicate 10 .P ++ List.replicate 4 .H) (p.1 + 1) ++ List.replicate 3 .P ++ [.H]
def frameBody (p : Parameters) : Sequence := framePart1 p ++ framePart2 p
def separatorWord (p : Parameters) (k : ℕ) : Sequence :=
  dimerChain 1 ++ List.replicate (entryTether p k) .P ++ dimerChain 2 ++
    List.replicate (exitTether p k) .P ++ dimerChain 3
def separatorBodies (p : Parameters) : List Sequence := (List.range (p.1 + 1)).map (separatorWord p)
def itemBody (p : Parameters) (s : ℕ) : Sequence := dimerChain (itemDimers p s)
def ringBody (p : Parameters) : Sequence := dimerChain (3 * (side p - 2))

@[simp] theorem frameBody_parameters (p : ConstructionParameters) :
    frameBody (p.bins, p.capacity) = p.framePart1 ++ p.framePart2 := rfl
@[simp] theorem separatorWord_parameters (p : ConstructionParameters) (k : ℕ) :
    separatorWord (p.bins, p.capacity) k = p.separatorWord k := rfl
@[simp] theorem itemBody_parameters (p : ConstructionParameters) (s : ℕ) :
    itemBody (p.bins, p.capacity) s = dimerChain (p.itemDimers s) := rfl
@[simp] theorem ringBody_parameters (p : ConstructionParameters) :
    ringBody (p.bins, p.capacity) = dimerChain (3 * (p.side - 2)) := rfl

end Raw

noncomputable def framePart1Computable : TM2ComputableInPolyTime parameterEncoding sequenceEncoding Raw.framePart1 :=
  concat (concat (concat (concat (concat (concat (concat
    (wordConstant _ [.H]) (wordConstant _ (List.replicate 6 .P)))
    (wordConstant _ (List.replicate 3 .H)))
    (repeatSequence (wordConstant _ (List.replicate 6 .P ++ List.replicate 4 .H)) binsComputable))
    (wordConstant _ (List.replicate 6 .P))) (compose frameTail1Computable (residuePower .H)))
    (wordConstant _ (List.replicate 3 .P))) (wordConstant _ [.H])

noncomputable def framePart2Computable : TM2ComputableInPolyTime parameterEncoding sequenceEncoding Raw.framePart2 :=
  concat (concat (concat (concat (wordConstant _ (List.replicate 3 .P))
    (compose frameTail2Computable (residuePower .H)))
    (repeatSequence (wordConstant _ (List.replicate 10 .P ++ List.replicate 4 .H))
      (add binsComputable (natConstant _ 1)))) (wordConstant _ (List.replicate 3 .P))) (wordConstant _ [.H])

noncomputable def frameBodyComputable : TM2ComputableInPolyTime parameterEncoding sequenceEncoding Raw.frameBody :=
  concat framePart1Computable framePart2Computable

noncomputable def frameWordComputable : TM2ComputableInPolyTime parameterEncoding sequenceEncoding (fun p => capWord (Raw.frameBody p)) :=
  compose (g := capWord) frameBodyComputable capComputable

noncomputable def separatorWordComputable : TM2ComputableInPolyTime indexedEncoding sequenceEncoding (fun p => Raw.separatorWord p.1 p.2) :=
  concat (concat (concat (concat (wordConstant _ (dimerChain 1))
    (compose (g := fun n => List.replicate n Residue.P) entryTetherComputable (residuePower .P))) (wordConstant _ (dimerChain 2)))
    (compose (g := fun n => List.replicate n Residue.P) exitTetherComputable (residuePower .P))) (wordConstant _ (dimerChain 3))

noncomputable def itemBodyComputable : TM2ComputableInPolyTime indexedEncoding sequenceEncoding (fun p => Raw.itemBody p.1 p.2) :=
  compose (g := dimerChain) itemDimersComputable dimerComputable
noncomputable def leftFillerBodyComputable : TM2ComputableInPolyTime parameterEncoding sequenceEncoding (fun p => dimerChain (Raw.leftFiller p)) :=
  compose (g := dimerChain) leftFillerComputable dimerComputable
noncomputable def rightFillerBodyComputable : TM2ComputableInPolyTime parameterEncoding sequenceEncoding (fun p => dimerChain (Raw.rightFiller p)) :=
  compose (g := dimerChain) rightFillerComputable dimerComputable
noncomputable def ringBodyComputable : TM2ComputableInPolyTime parameterEncoding sequenceEncoding Raw.ringBody :=
  compose (g := dimerChain) (mul (natConstant _ 3) (sub sideComputable (natConstant _ 2))) dimerComputable

noncomputable def separatorIndicesComputable :
    TM2ComputableInPolyTime parameterEncoding (TM2ListMap.listEncoding unaryFinEncodingNat) (fun p : Parameters => List.range (p.1 + 1)) :=
  compose (add binsComputable (natConstant _ 1)) TM2UnaryRange.rangeComputable

/-- Generate all K+1 literal separator bodies, in their canonical order,
using the concrete finite range and parameter-preserving list-map machines. -/
noncomputable def separatorBodiesComputable :
    TM2ComputableInPolyTime parameterEncoding (TM2ListMap.listEncoding sequenceEncoding) Raw.separatorBodies :=
  compose (pairComputable (idComputableInPolyTime parameterEncoding) separatorIndicesComputable)
    (TM2ListMap.mapComputable sequenceEncoding separatorWordComputable)

noncomputable def itemBodiesComputable :
    TM2ComputableInPolyTime (pairEncoding parameterEncoding (TM2ListMap.listEncoding unaryFinEncodingNat))
      (TM2ListMap.listEncoding sequenceEncoding) (fun p : Parameters × List ℕ => p.2.map (Raw.itemBody p.1)) :=
  TM2ListMap.mapComputable sequenceEncoding itemBodyComputable

end ProteinFolding.Tetrahedral.ReductionTM2

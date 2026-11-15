import ProteinFolding.Tetrahedral.ReductionTM2Basics
import ProteinFolding.Tetrahedral.FrameWord
import ProteinFolding.Cubic.Proofs.PackingBalanceComputable

namespace ProteinFolding.Tetrahedral.ReductionTM2

open Computability Turing TM2CompositionPoly TM2ProductMap

abbrev Parameters := ℕ × ℕ
def parameterEncoding : FinEncoding Parameters := pairEncoding unaryFinEncodingNat unaryFinEncodingNat
def indexedEncoding : FinEncoding (Parameters × ℕ) := pairEncoding parameterEncoding unaryFinEncodingNat

namespace Raw

def sigma (p : Parameters) := 18 * p.1 + 40
def scale (p : Parameters) := sigma p + 8
def binDimers (p : Parameters) := scale p * p.2
def leftFiller (p : Parameters) := binDimers p + scale p
def rightFiller (p : Parameters) := leftFiller p + 1
def separatorIndex (p : Parameters) (k : ℕ) := leftFiller p + k * (binDimers p + 2)
def side (p : Parameters) := separatorIndex p p.1 + rightFiller p + 3
def itemDimers (p : Parameters) (s : ℕ) := scale p * s
def entrySlack (_p : Parameters) (k : ℕ) := 10 * k + 12
def exitSlack (p : Parameters) (k : ℕ) := 14 * p.1 + 16 - 6 * k
def entryTether (p : Parameters) (k : ℕ) := 2 * separatorIndex p k + 3 + entrySlack p k
def exitTether (p : Parameters) (k : ℕ) := 2 * (side p - 2 - separatorIndex p k) + 3 + exitSlack p k
def frameTail1 (p : Parameters) := 2 * side p - (6 * p.1 + 11)
def frameTail2 (p : Parameters) := 2 * side p - (10 * p.1 + 15)
def baseLinkerLength (p : Parameters) (w : ℕ) := 1000 * (side p + w + 1) + 6

@[simp] theorem scale_parameters (p : ConstructionParameters) : scale (p.bins, p.capacity) = p.scale := rfl
@[simp] theorem side_parameters (p : ConstructionParameters) : side (p.bins, p.capacity) = p.side := rfl
@[simp] theorem leftFiller_parameters (p : ConstructionParameters) : leftFiller (p.bins, p.capacity) = p.leftFiller := rfl
@[simp] theorem rightFiller_parameters (p : ConstructionParameters) : rightFiller (p.bins, p.capacity) = p.rightFiller := rfl
@[simp] theorem itemDimers_parameters (p : ConstructionParameters) (s : ℕ) : itemDimers (p.bins, p.capacity) s = p.itemDimers s := rfl
@[simp] theorem entryTether_parameters (p : ConstructionParameters) (k : ℕ) : entryTether (p.bins, p.capacity) k = p.entryTether k := rfl
@[simp] theorem exitTether_parameters (p : ConstructionParameters) (k : ℕ) : exitTether (p.bins, p.capacity) k = p.exitTether k := rfl
@[simp] theorem frameTail1_parameters (p : ConstructionParameters) : frameTail1 (p.bins, p.capacity) = p.frameTail1 := rfl
@[simp] theorem frameTail2_parameters (p : ConstructionParameters) : frameTail2 (p.bins, p.capacity) = p.frameTail2 := rfl

end Raw

noncomputable def binsComputable : TM2ComputableInPolyTime parameterEncoding unaryFinEncodingNat Prod.fst :=
  TM2PairProjections.fstComputable _ _
noncomputable def capacityComputable : TM2ComputableInPolyTime parameterEncoding unaryFinEncodingNat Prod.snd :=
  TM2PairProjections.sndComputable _ _
noncomputable def sigmaComputable : TM2ComputableInPolyTime parameterEncoding unaryFinEncodingNat Raw.sigma :=
  add (mul (natConstant _ 18) binsComputable) (natConstant _ 40)
noncomputable def scaleComputable : TM2ComputableInPolyTime parameterEncoding unaryFinEncodingNat Raw.scale :=
  add sigmaComputable (natConstant _ 8)
noncomputable def binDimersComputable : TM2ComputableInPolyTime parameterEncoding unaryFinEncodingNat Raw.binDimers :=
  mul scaleComputable capacityComputable
noncomputable def leftFillerComputable : TM2ComputableInPolyTime parameterEncoding unaryFinEncodingNat Raw.leftFiller :=
  add binDimersComputable scaleComputable
noncomputable def rightFillerComputable : TM2ComputableInPolyTime parameterEncoding unaryFinEncodingNat Raw.rightFiller :=
  add leftFillerComputable (natConstant _ 1)
noncomputable def sideComputable : TM2ComputableInPolyTime parameterEncoding unaryFinEncodingNat Raw.side :=
  add (add (add leftFillerComputable (mul binsComputable (add binDimersComputable (natConstant _ 2))))
    rightFillerComputable) (natConstant _ 3)
noncomputable def frameTail1Computable : TM2ComputableInPolyTime parameterEncoding unaryFinEncodingNat Raw.frameTail1 :=
  sub (mul (natConstant _ 2) sideComputable) (add (mul (natConstant _ 6) binsComputable) (natConstant _ 11))
noncomputable def frameTail2Computable : TM2ComputableInPolyTime parameterEncoding unaryFinEncodingNat Raw.frameTail2 :=
  sub (mul (natConstant _ 2) sideComputable) (add (mul (natConstant _ 10) binsComputable) (natConstant _ 15))

noncomputable def parametersComputable : TM2ComputableInPolyTime indexedEncoding parameterEncoding Prod.fst :=
  TM2PairProjections.fstComputable _ _
noncomputable def indexComputable : TM2ComputableInPolyTime indexedEncoding unaryFinEncodingNat Prod.snd :=
  TM2PairProjections.sndComputable _ _
noncomputable def indexedBinsComputable : TM2ComputableInPolyTime indexedEncoding unaryFinEncodingNat (fun p : Parameters × ℕ => p.1.1) :=
  compose parametersComputable binsComputable
noncomputable def indexedScaleComputable : TM2ComputableInPolyTime indexedEncoding unaryFinEncodingNat (fun p => Raw.scale p.1) :=
  compose (g := Raw.scale) parametersComputable scaleComputable
noncomputable def indexedSideComputable : TM2ComputableInPolyTime indexedEncoding unaryFinEncodingNat (fun p => Raw.side p.1) :=
  compose (g := Raw.side) parametersComputable sideComputable
noncomputable def separatorIndexComputable : TM2ComputableInPolyTime indexedEncoding unaryFinEncodingNat (fun p => Raw.separatorIndex p.1 p.2) :=
  add (compose (g := Raw.leftFiller) parametersComputable leftFillerComputable)
    (mul indexComputable (add (compose (g := Raw.binDimers) parametersComputable binDimersComputable) (natConstant _ 2)))
noncomputable def itemDimersComputable : TM2ComputableInPolyTime indexedEncoding unaryFinEncodingNat (fun p => Raw.itemDimers p.1 p.2) :=
  mul indexedScaleComputable indexComputable
noncomputable def entrySlackComputable : TM2ComputableInPolyTime indexedEncoding unaryFinEncodingNat (fun p => Raw.entrySlack p.1 p.2) :=
  add (mul (natConstant _ 10) indexComputable) (natConstant _ 12)
noncomputable def exitSlackComputable : TM2ComputableInPolyTime indexedEncoding unaryFinEncodingNat (fun p => Raw.exitSlack p.1 p.2) :=
  sub (add (mul (natConstant _ 14) indexedBinsComputable) (natConstant _ 16)) (mul (natConstant _ 6) indexComputable)
noncomputable def entryTetherComputable : TM2ComputableInPolyTime indexedEncoding unaryFinEncodingNat (fun p => Raw.entryTether p.1 p.2) :=
  add (add (mul (natConstant _ 2) separatorIndexComputable) (natConstant _ 3)) entrySlackComputable
noncomputable def exitTetherComputable : TM2ComputableInPolyTime indexedEncoding unaryFinEncodingNat (fun p => Raw.exitTether p.1 p.2) :=
  add (add (mul (natConstant _ 2) (sub (sub indexedSideComputable (natConstant _ 2)) separatorIndexComputable))
    (natConstant _ 3)) exitSlackComputable
noncomputable def baseLinkerLengthComputable : TM2ComputableInPolyTime indexedEncoding unaryFinEncodingNat (fun p => Raw.baseLinkerLength p.1 p.2) :=
  add (mul (natConstant _ 1000) (add (add indexedSideComputable indexComputable) (natConstant _ 1))) (natConstant _ 6)

/-- Extract the actual unary source fields. No geometric computation or
output-size assertion is being used as a substitute for these machines. -/
noncomputable def sourceParametersComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding parameterEncoding
      (fun I : Packing.Instance => (I.bins, I.capacity)) :=
  pairComputable Packing.binsComputable Packing.capacityComputable

end ProteinFolding.Tetrahedral.ReductionTM2

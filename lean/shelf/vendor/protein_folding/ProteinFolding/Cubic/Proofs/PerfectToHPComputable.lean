import ProteinFolding.Cubic.Proofs.PerfectToHP
import ProteinFolding.Cubic.Proofs.VerifierPerfectInputGuards
import ProteinFolding.Common.TM2UnarySuccessor
import ProteinFolding.Common.TM2UnarySigned
import ProteinFolding.Common.TM2Conditional
import ProteinFolding.Common.ComplexityComposition

/-! Actual polynomial-time implementation of the total threshold reduction.
The binary side is only compared to unary indices below the explicit sequence
length bound. All subsequent arithmetic therefore has polynomial-size unary
arguments, and the result is converted to economical signed binary. -/

namespace ProteinFolding.CubicThresholdReduction

open Computability Turing TM2CompositionPoly TM2ProductMap TM2PairProjections
open CubicCertificates PerfectVerifierArithmetic

theorem length_word (S : Sequence) : S.map (fun _ => true) = unaryEncodeNat S.length := by
  induction S with
  | nil => rfl
  | cons r S ih => simpa only [List.map_cons, List.length_cons, unaryEncodeNat] using congrArg (true :: ·) ih

noncomputable def lengthComputable :
    TM2ComputableInPolyTime sequenceEncoding unaryFinEncodingNat List.length := by
  let h := TM2WordMap.mapComputable (fun _ : Residue => true)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun S => by
        simpa only [wordEncoding, sequenceEncoding, unaryFinEncodingNat, length_word] using h.outputsFun S }

noncomputable def sequenceComputable :
    TM2ComputableInPolyTime perfectEncoding sequenceEncoding (fun I : PerfectInput => I.1) :=
  fstComputable sequenceEncoding finEncodingNatBool

noncomputable def binarySideComputable :
    TM2ComputableInPolyTime perfectEncoding finEncodingNatBool (fun I : PerfectInput => I.2) :=
  sndComputable sequenceEncoding finEncodingNatBool

def searchEncoding : FinEncoding (PerfectInput × ℕ) := pairEncoding perfectEncoding unaryFinEncodingNat

noncomputable def testBinarySideComputable :
    TM2ComputableInPolyTime searchEncoding finEncodingNatBool (fun x : PerfectInput × ℕ => x.1.2) :=
  compose (fstComputable perfectEncoding unaryFinEncodingNat) binarySideComputable

noncomputable def sideTestComputable :
    TM2ComputableInPolyTime searchEncoding finEncodingBoolBool sideTest :=
  compose
    (pairComputable testBinarySideComputable (sndComputable perfectEncoding unaryFinEncodingNat))
    TM2Arithmetic.Equality.natUnaryComputable

noncomputable def sideBoundComputable :
    TM2ComputableInPolyTime perfectEncoding unaryFinEncodingNat sideBound :=
  compose (compose sequenceComputable lengthComputable) TM2UnarySuccessor.successorComputable

/-- The actual bounded-search controller simulates the proved binary/unary
equality machine at each index; it never expands the untrusted binary side. -/
noncomputable def recoveredSideComputable :
    TM2ComputableInPolyTime perfectEncoding unaryFinEncodingNat recoveredSide :=
  compose (pairComputable (idComputableInPolyTime perfectEncoding) sideBoundComputable)
    (TM2BoundedSearch.boundedSearchComputable sideTestComputable)

noncomputable def sideEqualityComputable :
    TM2ComputableInPolyTime perfectEncoding finEncodingBoolBool
      (fun I : PerfectInput => decide (I.2 = recoveredSide I)) :=
  compose (pairComputable binarySideComputable recoveredSideComputable)
    TM2Arithmetic.Equality.natUnaryComputable

noncomputable def hCountComputable :
    TM2ComputableInPolyTime perfectEncoding unaryFinEncodingNat (fun I : PerfectInput => hydrophobicCount I.1) :=
  compose sequenceComputable hydrophobicCountComputable

noncomputable def sideCubeComputable :
    TM2ComputableInPolyTime perfectEncoding unaryFinEncodingNat (fun I => recoveredSide I ^ 3) :=
  compose recoveredSideComputable unaryCubeComputable

noncomputable def volumeEqualityComputable :
    TM2ComputableInPolyTime perfectEncoding finEncodingBoolBool
      (fun I : PerfectInput => decide (hydrophobicCount I.1 = recoveredSide I ^ 3)) :=
  compose (pairComputable hCountComputable sideCubeComputable) PerfectUnaryEquality.unaryEqualityComputable

noncomputable def inputValidComputable :
    TM2ComputableInPolyTime perfectEncoding finEncodingBoolBool inputValid :=
  compose (pairComputable sideEqualityComputable volumeEqualityComputable) TM2Boolean.andComputable

noncomputable def thresholdComputable :
    TM2ComputableInPolyTime perfectEncoding signedEncoding
      (fun I : PerfectInput => cubeBondThreshold (recoveredSide I)) :=
  compose (compose recoveredSideComputable unaryThresholdComputable) TM2UnarySigned.nonnegativeComputable

noncomputable def candidateComputable :
    TM2ComputableInPolyTime perfectEncoding hpEncoding
      (fun I : PerfectInput => (⟨I.1, cubeBondThreshold (recoveredSide I)⟩ : HPInstance)) := by
  let h := pairComputable sequenceComputable thresholdComputable
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := h.outputsFun }

/-- The total actual TM2 threshold reduction, including rejection of every
malformed H count and side field. Its polynomial runtime is composed from the
proved primitive machines, and all output encodings remain canonical binary. -/
noncomputable def reductionComputable :
    TM2ComputableInPolyTime perfectEncoding hpEncoding reduction :=
  TM2Conditional.iteComputable inputValidComputable candidateComputable
    (TM2Constants.constantComputable perfectEncoding hpEncoding noInstance)

end ProteinFolding.CubicThresholdReduction

namespace ProteinFolding

/-- Theorem 3.2 yields an actual Karp reduction on all raw perfect inputs.
The wrong-H-count cases map to a fixed HP no-instance. -/
theorem perfect_karpReduces_hp :
    KarpReduces perfectEncoding hpEncoding
      (fun I : PerfectInput => PerfectHPStringFold I.1 I.2) (fun I : HPInstance => I.Accepts) :=
  ⟨CubicThresholdReduction.reduction, ⟨CubicThresholdReduction.reductionComputable⟩,
    CubicThresholdReduction.reduction_correct⟩

theorem hpNPHard_of_perfectNPHard
    (h : NPHard perfectEncoding (fun I : PerfectInput => PerfectHPStringFold I.1 I.2)) :
    NPHard hpEncoding (fun I : HPInstance => I.Accepts) :=
  npHard_of_karpReduces h perfect_karpReduces_hp

end ProteinFolding

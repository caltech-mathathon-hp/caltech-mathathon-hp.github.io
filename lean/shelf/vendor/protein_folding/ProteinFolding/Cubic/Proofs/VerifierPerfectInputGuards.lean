import ProteinFolding.Cubic.Proofs.ThresholdCertificateParser
import ProteinFolding.Cubic.Proofs.VerifierPerfectArithmetic
import ProteinFolding.Common.TM2ArithmeticEquality
import ProteinFolding.Common.TM2Boolean

/-! Actual polynomial-time guards for perfect certificate input data. Geometry
validity and the bond-score equality are intentionally separate computations;
the input guard alone is not an HP membership result. -/

namespace ProteinFolding.PerfectVerifierInputGuards

open Computability Turing TM2CompositionPoly TM2ProductMap TM2PairProjections
open PerfectCertificateParser PerfectVerifierArithmetic CubicCertificates PerfectUnaryEquality

abbrev Input := PerfectInput × List Bool

def inputEncoding : FinEncoding Input := pairEncoding perfectEncoding (wordEncoding Bool)

noncomputable def sequenceComputable : TM2ComputableInPolyTime inputEncoding sequenceEncoding
    (fun input : Input => input.1.1) :=
  compose (fstComputable perfectEncoding (wordEncoding Bool))
    (fstComputable sequenceEncoding finEncodingNatBool)

noncomputable def sideInputComputable : TM2ComputableInPolyTime inputEncoding finEncodingNatBool
    (fun input : Input => input.1.2) :=
  compose (fstComputable perfectEncoding (wordEncoding Bool))
    (sndComputable sequenceEncoding finEncodingNatBool)

noncomputable def parsedComputable : TM2ComputableInPolyTime inputEncoding resultEncoding
    (fun input : Input => parseSide input.2) :=
  compose (sndComputable perfectEncoding (wordEncoding Bool)) parserComputable

noncomputable def foundComputable : TM2ComputableInPolyTime inputEncoding finEncodingBoolBool
    (fun input : Input => (parseSide input.2).1) :=
  compose parsedComputable
    (fstComputable finEncodingBoolBool (pairEncoding unaryFinEncodingNat (wordEncoding Bool)))

noncomputable def parsedTailComputable : TM2ComputableInPolyTime inputEncoding
    (pairEncoding unaryFinEncodingNat (wordEncoding Bool))
    (fun input : Input => (parseSide input.2).2) :=
  compose parsedComputable
    (sndComputable finEncodingBoolBool (pairEncoding unaryFinEncodingNat (wordEncoding Bool)))

noncomputable def sideComputable : TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat
    (fun input : Input => (parseSide input.2).2.1) :=
  compose parsedTailComputable (fstComputable unaryFinEncodingNat (wordEncoding Bool))

noncomputable def geometryBitsComputable : TM2ComputableInPolyTime inputEncoding (wordEncoding Bool)
    (fun input : Input => (parseSide input.2).2.2) :=
  compose parsedTailComputable (sndComputable unaryFinEncodingNat (wordEncoding Bool))

noncomputable def sideEqualityComputable : TM2ComputableInPolyTime inputEncoding finEncodingBoolBool
    (fun input : Input => decide (input.1.2 = (parseSide input.2).2.1)) :=
  compose (pairComputable sideInputComputable sideComputable) TM2Arithmetic.Equality.natUnaryComputable

noncomputable def hCountComputable : TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat
    (fun input : Input => hydrophobicCount input.1.1) :=
  compose sequenceComputable hydrophobicCountComputable

noncomputable def sideCubeComputable : TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat
    (fun input : Input => (parseSide input.2).2.1 ^ 3) :=
  compose sideComputable unaryCubeComputable

noncomputable def volumeEqualityComputable : TM2ComputableInPolyTime inputEncoding finEncodingBoolBool
    (fun input : Input => decide (hydrophobicCount input.1.1 = (parseSide input.2).2.1 ^ 3)) :=
  compose (pairComputable hCountComputable sideCubeComputable) unaryEqualityComputable

def inputGuard (input : Input) : Bool :=
  ((parseSide input.2).1 && decide (input.1.2 = (parseSide input.2).2.1)) &&
    decide (hydrophobicCount input.1.1 = (parseSide input.2).2.1 ^ 3)

/-- A concrete composition of the frame scanner, field projections, H counter,
unary cube machine, exact comparators, and finite Boolean conjunction machines. -/
noncomputable def inputGuardComputable :
    TM2ComputableInPolyTime inputEncoding finEncodingBoolBool inputGuard :=
  compose
    (pairComputable
      (compose (pairComputable foundComputable sideEqualityComputable) TM2Boolean.andComputable)
      volumeEqualityComputable)
    TM2Boolean.andComputable

theorem inputGuard_spec (input : Input) : inputGuard input = true ↔
    (parseSide input.2).1 = true ∧ input.1.2 = (parseSide input.2).2.1 ∧
      hydrophobicCount input.1.1 = (parseSide input.2).2.1 ^ 3 := by
  simp [inputGuard, Bool.and_eq_true, and_assoc]

theorem inputGuard_side_bound (input : Input) (h : inputGuard input = true) :
    (parseSide input.2).2.1 ≤ input.1.1.length := by
  obtain ⟨_, hside, hvolume⟩ := (inputGuard_spec input).mp h
  have hcount : hydrophobicCount input.1.1 = input.1.2 ^ 3 := by simpa [hside] using hvolume
  have hbound := side_le_sequence_length_of_count input.1 hcount
  simpa [hside] using hbound

end ProteinFolding.PerfectVerifierInputGuards

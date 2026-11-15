import ProteinFolding.Cubic.Proofs.VerifierPerfectInputGuards
import ProteinFolding.Cubic.Proofs.VerifierHPFields

/-! Label comparison for the framed perfect certificate. The geometry payload
uses the same four-bit incoming-direction records as the HP verifier. -/

namespace ProteinFolding.PerfectVerifierLabels

open Computability Turing TM2CompositionPoly TM2ProductMap
open PerfectCertificateParser PerfectVerifierInputGuards

noncomputable def decodedLabelsComputable : TM2ComputableInPolyTime inputEncoding sequenceEncoding
    (fun input : Input => CubicHPVerifier.decodedLabels (parseSide input.2).2.2) :=
  compose (f := fun input : Input => (parseSide input.2).2.2)
    (g := CubicHPVerifier.decodedLabels) geometryBitsComputable CubicHPVerifier.decodedLabelsComputable

def labelCheck (input : Input) : Bool :=
  decide (input.1.1 = CubicHPVerifier.decodedLabels (parseSide input.2).2.2)

noncomputable def labelCheckComputable :
    TM2ComputableInPolyTime inputEncoding finEncodingBoolBool labelCheck :=
  compose (pairComputable sequenceComputable decodedLabelsComputable)
    (TM2WordEquality.wordEqualityComputable Residue)

theorem labelCheck_spec (input : Input) : labelCheck input = true ↔
    input.1.1 = CubicHPVerifier.decodedLabels (parseSide input.2).2.2 := by
  simp [labelCheck]

end ProteinFolding.PerfectVerifierLabels

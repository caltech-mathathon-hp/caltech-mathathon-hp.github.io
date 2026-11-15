import ProteinFolding.Cubic.Proofs.VerifierPerfectLabels
import ProteinFolding.Cubic.Proofs.VerifierPerfectSemantics

/-! Assembly of the perfect-folding verifier. All framing, input, label and
unary arithmetic machines are closed constructions. The actual all-pairs
geometry machine is an explicit data parameter until its construction is
available; no unconditional NP result is asserted without it. -/

namespace ProteinFolding.PerfectVerifier

open Computability Turing CubicVerifier CubicRecordDecoder CubicCertificates
open TM2CompositionPoly TM2ProductMap TM2PairProjections
open PerfectCertificateParser PerfectVerifierInputGuards PerfectVerifierArithmetic

def verify (input : Input) : Bool :=
  inputGuard input && (PerfectVerifierLabels.labelCheck input &&
    (geometryValid (stream (parseSide input.2).2.2) &&
      decide (3 * (parseSide input.2).2.1 ^ 2 * ((parseSide input.2).2.1 - 1) =
        bondCountRecords (stream (parseSide input.2).2.2))))

noncomputable def decodedInputComputable : TM2ComputableInPolyTime inputEncoding
    (wordEncoding (Option Record)) (fun input : Input => stream (parseSide input.2).2.2) :=
  compose (f := fun input : Input => (parseSide input.2).2.2) (g := stream)
    geometryBitsComputable decoderComputable

/-- The resulting verifier includes actual finite machines for every stage;
the geometric witness is the sole remaining input to this constructor. -/
noncomputable def verifyComputable
    (hGeometry : TM2ComputableInPolyTime (wordEncoding (Option Record))
      CubicHPVerifier.geometryEncoding CubicHPVerifier.geometryData) :
    TM2ComputableInPolyTime inputEncoding finEncodingBoolBool verify := by
  let hgeo := compose decodedInputComputable hGeometry
  let hvalid := compose hgeo (fstComputable finEncodingBoolBool unaryFinEncodingNat)
  let hscore := compose hgeo (sndComputable finEncodingBoolBool unaryFinEncodingNat)
  let hequality := compose (pairComputable sideComputable hscore) thresholdScoreComputable
  let hvalidScore := compose (pairComputable hvalid hequality) TM2Boolean.andComputable
  let hlabelGeometry := compose
    (pairComputable PerfectVerifierLabels.labelCheckComputable hvalidScore) TM2Boolean.andComputable
  exact compose (pairComputable inputGuardComputable hlabelGeometry) TM2Boolean.andComputable

theorem verify_spec (input : Input) : verify input = true ↔
    inputGuard input = true ∧
      input.1.1 = CubicHPVerifier.decodedLabels (parseSide input.2).2.2 ∧
        geometryValid (stream (parseSide input.2).2.2) = true ∧
          3 * (parseSide input.2).2.1 ^ 2 * ((parseSide input.2).2.1 - 1) =
            bondCountRecords (stream (parseSide input.2).2.2) := by
  simp [verify, PerfectVerifierLabels.labelCheck, Bool.and_eq_true]

theorem verify_iff_framed (input : Input) :
    verify input = true ↔ FramedPerfectRecordBitsAccept input := by
  rw [verify_spec]
  constructor
  · rintro ⟨hguard, hlabels, hvalid, hscore⟩
    obtain ⟨_, hside, hc⟩ := (inputGuard_spec input).mp hguard
    refine ⟨hguard, (perfectRecordBitsAccept_iff_geometry input.1 _).mpr ?_⟩
    refine ⟨?_, hlabels, hvalid, ?_⟩
    · simpa only [hside] using hc
    · simpa only [hside] using hscore.symm
  · rintro ⟨hguard, hrecords⟩
    obtain ⟨_, hlabels, hvalid, hscore⟩ :=
      (perfectRecordBitsAccept_iff_geometry input.1 _).mp hrecords
    obtain ⟨_, hside, _⟩ := (inputGuard_spec input).mp hguard
    refine ⟨hguard, hlabels, hvalid, ?_⟩
    simpa only [hside] using hscore.symm

theorem verify_polyTimeDecidable
    (hGeometry : TM2ComputableInPolyTime (wordEncoding (Option Record))
      CubicHPVerifier.geometryEncoding CubicHPVerifier.geometryData) :
    PolyTimeDecidable inputEncoding FramedPerfectRecordBitsAccept :=
  ⟨verify, ⟨verifyComputable hGeometry⟩, verify_iff_framed⟩

/-- Unconditional once instantiated with the actual geometric machine data.
Its certificate bound is the explicit linear polynomial 5N+1. -/
theorem perfect_inNP_of_geometry_computable
    (hGeometry : TM2ComputableInPolyTime (wordEncoding (Option Record))
      CubicHPVerifier.geometryEncoding CubicHPVerifier.geometryData) :
    InNP perfectEncoding (fun I => PerfectHPStringFold I.1 I.2) :=
  perfect_inNP_of_framed_record_verifier_polyTime (verify_polyTimeDecidable hGeometry)

end ProteinFolding.PerfectVerifier

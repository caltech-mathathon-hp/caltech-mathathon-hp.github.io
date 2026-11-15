import ProteinFolding.Cubic.Proofs.VerifierHPFields
import ProteinFolding.Cubic.Proofs.VerifierGeometry

/-! Assembly of the cubic HP certificate verifier. Every non-geometric stage
is closed and explicitly polynomial-time. The assembly constructor currently
takes the actual geometric machine as an explicit data argument; it does not
assert unconditional NP membership in the absence of that machine. -/

namespace ProteinFolding.CubicHPVerifier

open Computability Turing CubicVerifier CubicRecordDecoder

def geometryEncoding : FinEncoding (Bool × ℕ) :=
  pairEncoding finEncodingBoolBool unaryFinEncodingNat

def geometryData (rs : List (Option Record)) : Bool × ℕ :=
  (geometryValid rs, bondCountRecords rs)

def verify (x : Input) : Bool :=
  labelCheck x && (geometryValid (stream x.2) &&
    decide (x.1.minBonds ≤ (bondCountRecords (stream x.2) : ℤ)))

noncomputable def decodedInputComputable :
    TM2ComputableInPolyTime inputEncoding (wordEncoding (Option Record))
      (fun x : Input => stream x.2) :=
  TM2CompositionPoly.compose (f := fun x : Input => x.2) (g := stream)
    certificateComputable decoderComputable

noncomputable def verifyComputable
    (hGeometry : TM2ComputableInPolyTime (wordEncoding (Option Record)) geometryEncoding geometryData) :
    TM2ComputableInPolyTime inputEncoding finEncodingBoolBool verify := by
  let hgeo := TM2CompositionPoly.compose decodedInputComputable hGeometry
  let hvalid := TM2CompositionPoly.compose hgeo
    (TM2PairProjections.fstComputable finEncodingBoolBool unaryFinEncodingNat)
  let hscore := TM2CompositionPoly.compose hgeo
    (TM2PairProjections.sndComputable finEncodingBoolBool unaryFinEncodingNat)
  let hthreshold := TM2CompositionPoly.compose
    (TM2ProductMap.pairComputable inputMinBondsComputable hscore)
    TM2Arithmetic.Comparator.signedUnaryComputable
  let hgeoThreshold := TM2CompositionPoly.compose
    (TM2ProductMap.pairComputable hvalid hthreshold) TM2Boolean.andComputable
  exact TM2CompositionPoly.compose (TM2ProductMap.pairComputable labelCheckComputable hgeoThreshold)
    TM2Boolean.andComputable

theorem verify_correct (x : Input) : verify x = true ↔
    x.1.sequence = decodedLabels x.2 ∧ geometryValid (stream x.2) = true ∧
      x.1.minBonds ≤ (bondCountRecords (stream x.2) : ℤ) := by
  simp [verify, labelCheck, Bool.and_eq_true]

theorem verify_polyTimeDecidable
    (hGeometry : TM2ComputableInPolyTime (wordEncoding (Option Record)) geometryEncoding geometryData) :
    PolyTimeDecidable inputEncoding (fun x => verify x = true) :=
  ⟨verify, ⟨verifyComputable hGeometry⟩, fun _ => Iff.rfl⟩

theorem sequence_length_le_input (I : HPInstance) : I.sequence.length ≤ (hpEncoding.encode I).length := by
  simp [hpEncoding, pairEncoding, sequenceEncoding, wordEncoding]

theorem encoded_records_bound (I : HPInstance) (rs : List Record)
    (hlen : rs.length = I.sequence.length) :
    ((wordEncoding Bool).encode (encodeRecords rs)).length ≤
      (Polynomial.C 4 * Polynomial.X : Polynomial ℕ).eval (hpEncoding.encode I).length := by
  simp only [wordEncoding, id_eq, encodeRecords_length, hlen,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  exact Nat.mul_le_mul_left 4 (sequence_length_le_input I)

theorem bounded_record_certificate (I : HPInstance) (hI : I.Accepts) :
    ∃ rs : List Record,
      (encodeRecords rs).length ≤
        (Polynomial.C 4 * Polynomial.X : Polynomial ℕ).eval (hpEncoding.encode I).length ∧
      labelCheck (I, encodeRecords rs) = true ∧ RecordsAccept (I, rs) := by
  obtain ⟨rs, hlen, hacc⟩ := (hp_records_certificate_iff I).mp hI
  exact ⟨rs, encoded_records_bound I rs hlen, labelCheck_encodeRecords I rs hacc, hacc⟩

end ProteinFolding.CubicHPVerifier

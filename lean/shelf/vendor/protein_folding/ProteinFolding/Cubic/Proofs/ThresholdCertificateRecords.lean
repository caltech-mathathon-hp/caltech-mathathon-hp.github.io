import ProteinFolding.Cubic.Proofs.VerifierPerfectInputGuards
import ProteinFolding.Cubic.Proofs.VerifierRecordDecoder
import ProteinFolding.Cubic.Proofs.GeometryScore

/-! Perfect certificates with a unary side prefix and four-bit labelled
incoming directions. This file proves the exact mathematical certificate
relation and its linear completeness bound; the all-pairs machine is supplied
separately. The original input and problem definitions are unchanged. -/

namespace ProteinFolding.CubicCertificates

open Computability Turing CubicVerifier CubicRecordDecoder PerfectCertificateParser

/-- Failure tokens emitted by the total decoder are retained as rejection. -/
def collectRecords : List (Option Record) → Option (List Record)
  | [] => some []
  | none :: _ => none
  | some r :: rs => (collectRecords rs).map (r :: ·)

theorem collectRecords_map_some (rs : List Record) :
    collectRecords (rs.map some) = some rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [collectRecords, ih]

theorem collectRecords_eq_some_iff (tokens : List (Option Record)) (rs : List Record) :
    collectRecords tokens = some rs ↔ tokens = rs.map some := by
  induction tokens generalizing rs with
  | nil => cases rs <;> simp [collectRecords]
  | cons token tokens ih =>
    cases token with
    | none => cases rs <;> simp [collectRecords]
    | some r =>
      cases rs with
      | nil => cases h : collectRecords tokens <;> simp [collectRecords, h]
      | cons s rs =>
        cases h : collectRecords tokens with
        | none =>
          simp only [collectRecords, h, Option.map_none, reduceCtorEq, false_iff,
            List.map_cons, List.cons.injEq, Option.some.injEq]
          rintro ⟨_, ht⟩
          have := (ih rs).mpr ht
          simp [h] at this
        | some tail =>
          have he : tail = rs ↔ tokens = rs.map some := by
            simpa only [h, Option.some.injEq] using ih rs
          simp only [collectRecords, h, Option.map_some, Option.some.injEq,
            List.cons.injEq, List.map_cons]
          exact and_congr Iff.rfl he

def decodeRecords (w : List Bool) : Option (List Record) := collectRecords (stream w)

theorem decodeRecords_encodeRecords (rs : List Record) :
    decodeRecords (encodeRecords rs) = some rs := by
  rw [decodeRecords, stream_encodeRecords, collectRecords_map_some]

/-- With the correct H count, the proved score bound lets the verifier check
exact natural-number equality with the cube's score. -/
def PerfectRecordsAccept (input : PerfectInput × List Record) : Prop :=
  hydrophobicCount input.1.1 = input.1.2 ^ 3 ∧
    match recordFold input.1.1 input.2 with
    | none => False
    | some f => bondCount input.1.1 f = 3 * input.1.2 ^ 2 * (input.1.2 - 1)

instance (input : PerfectInput × List Record) : Decidable (PerfectRecordsAccept input) := by
  unfold PerfectRecordsAccept
  split <;> infer_instance

theorem perfectRecordsAccept_sound (I : PerfectInput) (rs : List Record)
    (h : PerfectRecordsAccept (I, rs)) : PerfectHPStringFold I.1 I.2 := by
  obtain ⟨hc, hscore⟩ := h
  unfold PerfectHPStringFold
  refine ⟨hc, ?_⟩
  cases hf : recordFold I.1 rs with
  | none => simp [hf] at hscore
  | some f =>
    simp only [hf] at hscore
    refine ⟨f, (CubicGeometry.packsCube_iff_bond_threshold I.1 f I.2 hc).mpr ?_⟩
    rw [hscore]
    exact le_rfl

theorem perfect_records_certificate_iff (I : PerfectInput) :
    PerfectHPStringFold I.1 I.2 ↔ ∃ rs : List Record,
      rs.length = I.1.length ∧ PerfectRecordsAccept (I, rs) := by
  constructor
  · rintro ⟨hc, f, hp⟩
    obtain ⟨g, hg, hscore⟩ := recordFold_complete f
    refine ⟨recordsOfDirections I.1 (foldDirections f), recordsOfDirections_length _ _, hc, ?_⟩
    rw [hg]
    change bondCount I.1 g = 3 * I.2 ^ 2 * (I.2 - 1)
    rw [hscore]
    exact CubicGeometry.packsCube_bondCount I.1 f I.2 hp
  · rintro ⟨rs, _, hr⟩
    exact perfectRecordsAccept_sound I rs hr

def PerfectRecordBitsAccept (input : PerfectInput × List Bool) : Prop :=
  match decodeRecords input.2 with
  | none => False
  | some rs => PerfectRecordsAccept (input.1, rs)

instance (input : PerfectInput × List Bool) : Decidable (PerfectRecordBitsAccept input) := by
  unfold PerfectRecordBitsAccept
  split <;> infer_instance

theorem perfectRecordBitsAccept_sound (I : PerfectInput) (w : List Bool)
    (h : PerfectRecordBitsAccept (I, w)) : PerfectHPStringFold I.1 I.2 := by
  unfold PerfectRecordBitsAccept at h
  split at h
  · exact False.elim h
  · exact perfectRecordsAccept_sound I _ h

def FramedPerfectRecordBitsAccept (input : PerfectInput × List Bool) : Prop :=
  PerfectVerifierInputGuards.inputGuard input = true ∧
    PerfectRecordBitsAccept (input.1, (parseSide input.2).2.2)

instance (input : PerfectInput × List Bool) : Decidable (FramedPerfectRecordBitsAccept input) := by
  unfold FramedPerfectRecordBitsAccept
  infer_instance

theorem framedPerfectRecordBitsAccept_sound (I : PerfectInput) (w : List Bool)
    (h : FramedPerfectRecordBitsAccept (I, w)) : PerfectHPStringFold I.1 I.2 :=
  perfectRecordBitsAccept_sound I _ h.2

/-- The delimiter and unary side cost at most N+1 bits, and the redundant
labelled geometry records cost exactly 4N bits. -/
theorem perfect_framed_record_certificate_iff (I : PerfectInput) :
    PerfectHPStringFold I.1 I.2 ↔ ∃ w : List Bool,
      w.length ≤ 5 * I.1.length + 1 ∧ FramedPerfectRecordBitsAccept (I, w) := by
  constructor
  · intro hI
    obtain ⟨rs, hlen, hr⟩ := (perfect_records_certificate_iff I).mp hI
    have hn := side_le_sequence_length_of_count I hI.1
    refine ⟨frameUnarySide I.2 (encodeRecords rs), ?_, ?_⟩
    · rw [frameUnarySide_length, encodeRecords_length, hlen]
      omega
    · constructor
      · apply (PerfectVerifierInputGuards.inputGuard_spec _).mpr
        simp only [parseSide_frame]
        exact ⟨True.intro, True.intro, hI.1⟩
      · simpa only [parseSide_frame, PerfectRecordBitsAccept, decodeRecords_encodeRecords] using hr
  · rintro ⟨w, _, hw⟩
    exact framedPerfectRecordBitsAccept_sound I w hw

/-- The only remaining assumption here is the actual all-pairs classifier;
this conditional transfer does not assert unconditional NP membership. -/
theorem perfect_inNP_of_framed_record_verifier_polyTime
    (h : PolyTimeDecidable (pairEncoding perfectEncoding (wordEncoding Bool))
      FramedPerfectRecordBitsAccept) :
    InNP perfectEncoding (fun I => PerfectHPStringFold I.1 I.2) := by
  refine ⟨List Bool, wordEncoding Bool, fun w => ⟨w, rfl⟩,
    Polynomial.C 5 * Polynomial.X + Polynomial.C 1, FramedPerfectRecordBitsAccept, h, ?_⟩
  intro I
  constructor
  · intro hI
    obtain ⟨w, hlen, hw⟩ := (perfect_framed_record_certificate_iff I).mp hI
    refine ⟨w, ?_, hw⟩
    have hN := sequence_length_le_perfectEncoding I
    simpa [wordEncoding] using hlen.trans (by omega :
      5 * I.1.length + 1 ≤ 5 * (perfectEncoding.encode I).length + 1)
  · rintro ⟨w, _, hw⟩
    exact framedPerfectRecordBitsAccept_sound I w hw

end ProteinFolding.CubicCertificates

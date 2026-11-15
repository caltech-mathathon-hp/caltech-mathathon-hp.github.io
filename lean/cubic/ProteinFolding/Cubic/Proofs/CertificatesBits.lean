import ProteinFolding.Cubic.Proofs.CertificatesDirections

/-! Three-bit direction codes. Codes six and seven and incomplete trailing
triples are rejected. The certificate alphabet is Bool with identity encoding,
so every certificate word is represented, as required by frozen `InNP`. -/

namespace ProteinFolding.CubicCertificates

def encodeDirection : Fin 6 → List Bool
  | 0 => [false, false, false]
  | 1 => [true, false, false]
  | 2 => [false, true, false]
  | 3 => [true, true, false]
  | 4 => [false, false, true]
  | 5 => [true, false, true]

def bitsValue (a b c : Bool) : ℕ := a.toNat + 2 * b.toNat + 4 * c.toNat

def decodeDirections : List Bool → Option DirectionWord
  | [] => some []
  | a :: b :: c :: w =>
    if h : bitsValue a b c < 6 then
      (decodeDirections w).map (⟨bitsValue a b c, h⟩ :: ·)
    else none
  | _ => none

def encodeDirections (ds : DirectionWord) : List Bool := ds.flatMap encodeDirection

theorem decode_encodeDirections (ds : DirectionWord) :
    decodeDirections (encodeDirections ds) = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    match d with
    | 0 => simpa [encodeDirections, encodeDirection, decodeDirections, bitsValue] using ih
    | 1 => simpa [encodeDirections, encodeDirection, decodeDirections, bitsValue] using ih
    | 2 => simpa [encodeDirections, encodeDirection, decodeDirections, bitsValue] using ih
    | 3 => simpa [encodeDirections, encodeDirection, decodeDirections, bitsValue] using ih
    | 4 => simpa [encodeDirections, encodeDirection, decodeDirections, bitsValue] using ih
    | 5 => simpa [encodeDirections, encodeDirection, decodeDirections, bitsValue] using ih

theorem encodeDirections_length (ds : DirectionWord) :
    (encodeDirections ds).length = 3 * ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    match d with
    | 0 => simpa [encodeDirections, encodeDirection, Nat.mul_succ] using ih
    | 1 => simpa [encodeDirections, encodeDirection, Nat.mul_succ] using ih
    | 2 => simpa [encodeDirections, encodeDirection, Nat.mul_succ] using ih
    | 3 => simpa [encodeDirections, encodeDirection, Nat.mul_succ] using ih
    | 4 => simpa [encodeDirections, encodeDirection, Nat.mul_succ] using ih
    | 5 => simpa [encodeDirections, encodeDirection, Nat.mul_succ] using ih

theorem decodeDirections_length (w : List Bool) (ds : DirectionWord)
    (h : decodeDirections w = some ds) : w.length = 3 * ds.length := by
  cases w with
  | nil => simp only [decodeDirections, Option.some.injEq] at h; subst ds; rfl
  | cons a w =>
    cases w with
    | nil => simp [decodeDirections] at h
    | cons b w =>
      cases w with
      | nil => simp [decodeDirections] at h
      | cons c w =>
        by_cases hcode : bitsValue a b c < 6
        · cases ht : decodeDirections w with
          | none => simp [decodeDirections, hcode, ht] at h
          | some tail =>
            have hds : ds = ⟨bitsValue a b c, hcode⟩ :: tail := by
              simpa [decodeDirections, hcode, ht] using h.symm
            subst ds
            have ih := decodeDirections_length w tail ht
            simp only [List.length_cons]
            omega
        · simp [decodeDirections, hcode] at h
termination_by w.length

def BitsAccepts (input : HPInstance × List Bool) : Prop :=
  match decodeDirections input.2 with
  | none => False
  | some ds => DirectionAccepts (input.1, ds)

instance (input : HPInstance × List Bool) : Decidable (BitsAccepts input) := by
  unfold BitsAccepts
  split <;> infer_instance

def bitsVerifier (input : HPInstance × List Bool) : Bool := decide (BitsAccepts input)

theorem bitsVerifier_spec (input : HPInstance × List Bool) :
    bitsVerifier input = true ↔ BitsAccepts input := by simp [bitsVerifier]

theorem bitsAccepts_sound (I : HPInstance) (w : List Bool) (h : BitsAccepts (I, w)) :
    I.Accepts := by
  unfold BitsAccepts at h
  split at h
  · exact False.elim h
  · exact directionAccepts_sound I _ h

theorem bitsAccepts_length (I : HPInstance) (w : List Bool) (h : BitsAccepts (I, w)) :
    w.length = 3 * I.sequence.length := by
  unfold BitsAccepts at h
  cases hd : decodeDirections w with
  | none => simp [hd] at h
  | some ds =>
    simp only [hd] at h
    rw [decodeDirections_length w ds hd, directionAccepts_length I ds h]

theorem hp_bits_certificate_iff (I : HPInstance) :
    I.Accepts ↔ ∃ w : List Bool, w.length = 3 * I.sequence.length ∧ BitsAccepts (I, w) := by
  constructor
  · intro hI
    obtain ⟨ds, hlen, hd⟩ := (hp_direction_certificate_iff I).1 hI
    refine ⟨encodeDirections ds, ?_, ?_⟩
    · rw [encodeDirections_length, hlen]
    · simpa only [BitsAccepts, decode_encodeDirections] using hd
  · rintro ⟨w, _, hw⟩
    exact bitsAccepts_sound I w hw

theorem sequence_length_le_hpEncoding (I : HPInstance) :
    I.sequence.length ≤ (hpEncoding.encode I).length := by
  simp [hpEncoding, pairEncoding, sequenceEncoding, wordEncoding]

/-- The outstanding machine-level obligation, not an assertion that the
executable Boolean checker automatically supplies that machine. -/
def HPBitsVerifierPolyTime : Prop :=
  PolyTimeDecidable (pairEncoding hpEncoding (wordEncoding Bool)) BitsAccepts

theorem hp_inNP_of_bits_verifier_polyTime (h : HPBitsVerifierPolyTime) :
    InNP hpEncoding HPInstance.Accepts := by
  refine ⟨List Bool, wordEncoding Bool, ?_, Polynomial.C 3 * Polynomial.X, BitsAccepts, h, ?_⟩
  · exact fun w => ⟨w, rfl⟩
  · intro I
    constructor
    · intro hI
      obtain ⟨w, hlen, hw⟩ := (hp_bits_certificate_iff I).1 hI
      refine ⟨w, ?_, hw⟩
      simpa [wordEncoding, hlen] using Nat.mul_le_mul_left 3 (sequence_length_le_hpEncoding I)
    · rintro ⟨w, _, hw⟩
      exact bitsAccepts_sound I w hw

example : decodeDirections [false] = none := rfl
example : decodeDirections [false, true, true] = none := rfl
example : decodeDirections [true, true, true] = none := rfl
example : decodeDirections [true, false, true] = some [5] := rfl

end ProteinFolding.CubicCertificates


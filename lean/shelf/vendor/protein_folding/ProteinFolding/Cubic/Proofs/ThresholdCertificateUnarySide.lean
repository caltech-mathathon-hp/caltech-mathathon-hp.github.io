import ProteinFolding.Cubic.Proofs.VerifierPerfectUnary
import ProteinFolding.Common.TM2Fanout

/-! Bounded unary side witnesses for perfect folding. The certificate is still
an arbitrary flat Bool word under the surjective identity encoding. A prefix
`true^n ++ [false]` carries the side length; the remaining bits carry the same
direction certificate as the HP verifier. No binary side length is expanded by
the verifier before its correspondence with this explicit prefix is checked. -/

namespace ProteinFolding.CubicCertificates

open Computability Turing

def splitUnarySide : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: w => some (0, w)
  | true :: w => (splitUnarySide w).map (fun p => (p.1 + 1, p.2))

def frameUnarySide (n : ℕ) (w : List Bool) : List Bool := unaryEncodeNat n ++ false :: w

theorem split_frameUnarySide (n : ℕ) (w : List Bool) :
    splitUnarySide (frameUnarySide n w) = some (n, w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [frameUnarySide, unaryEncodeNat, splitUnarySide] using
      (congrArg (Option.map (fun p : ℕ × List Bool => (p.1 + 1, p.2))) ih)

theorem frameUnarySide_length (n : ℕ) (w : List Bool) :
    (frameUnarySide n w).length = n + 1 + w.length := by
  simp [frameUnarySide, PerfectUnaryMultiplication.unary_length, Nat.add_comm,
    Nat.add_left_comm]

theorem splitUnarySide_length (c : List Bool) (n : ℕ) (w : List Bool)
    (h : splitUnarySide c = some (n, w)) : c.length = n + 1 + w.length := by
  induction c generalizing n w with
  | nil => simp [splitUnarySide] at h
  | cons bit c ih =>
    cases bit with
    | false =>
      have heq : n = 0 ∧ w = c := by simpa [splitUnarySide] using h.symm
      obtain ⟨rfl, rfl⟩ := heq
      simp [Nat.add_comm]
    | true =>
      cases ht : splitUnarySide c with
      | none => simp [splitUnarySide, ht] at h
      | some p =>
        obtain ⟨k, v⟩ := p
        have heq : n = k + 1 ∧ w = v := by simpa [splitUnarySide, ht] using h.symm
        have hl := ih k v ht
        obtain ⟨rfl, rfl⟩ := heq
        simp only [List.length_cons]
        omega

theorem hydrophobicCount_le_sequence_length (S : Sequence) : hydrophobicCount S ≤ S.length := by
  have h := Finset.card_le_card (Finset.filter_subset (fun i : Fin S.length => S.get i = Residue.H)
    Finset.univ)
  simpa only [hydrophobicCount, hydrophobicIndices, Finset.card_univ, Fintype.card_fin] using h

theorem side_le_sequence_length_of_count (I : PerfectInput)
    (hc : hydrophobicCount I.1 = I.2 ^ 3) : I.2 ≤ I.1.length := by
  have hn : I.2 ≤ I.2 ^ 3 := by
    by_cases hzero : I.2 = 0
    · simp [hzero]
    · have hpos : 1 ≤ I.2 := by omega
      have hsquare : I.2 ≤ I.2 * I.2 := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left I.2 hpos
      have hcube : I.2 * I.2 ≤ I.2 ^ 3 := by
        simpa only [pow_succ, pow_zero, Nat.mul_one, Nat.one_mul] using
          Nat.mul_le_mul_left (I.2 * I.2) hpos
      exact hsquare.trans hcube
  rw [← hc] at hn
  exact hn.trans (hydrophobicCount_le_sequence_length I.1)

def UnarySideBitsAccepts (input : PerfectInput × List Bool) : Prop :=
  match splitUnarySide input.2 with
  | none => False
  | some (side, geometry) =>
      side = input.1.2 ∧ side ≤ input.1.1.length ∧ ThresholdBitsAccepts (input.1, geometry)

instance (input : PerfectInput × List Bool) : Decidable (UnarySideBitsAccepts input) := by
  unfold UnarySideBitsAccepts
  split <;> infer_instance

theorem unarySideBitsAccepts_sound (I : PerfectInput) (c : List Bool)
    (h : UnarySideBitsAccepts (I, c)) : PerfectHPStringFold I.1 I.2 := by
  unfold UnarySideBitsAccepts at h
  split at h
  · exact False.elim h
  · exact perfectBitsAccepts_sound I _ ((perfectBitsAccepts_iff_threshold _).mpr h.2.2)

theorem unarySideBitsAccepts_length (I : PerfectInput) (c : List Bool)
    (h : UnarySideBitsAccepts (I, c)) : c.length ≤ 4 * I.1.length + 1 := by
  unfold UnarySideBitsAccepts at h
  cases hd : splitUnarySide c with
  | none => simp [hd] at h
  | some p =>
    obtain ⟨n, w⟩ := p
    simp only [hd] at h
    have hlen := splitUnarySide_length c n w hd
    have hw := bitsAccepts_length (thresholdInstance I) w h.2.2.2
    change w.length = 3 * I.1.length at hw
    omega

theorem perfect_unarySide_certificate_iff (I : PerfectInput) :
    PerfectHPStringFold I.1 I.2 ↔ ∃ c : List Bool,
      c.length ≤ 4 * I.1.length + 1 ∧ UnarySideBitsAccepts (I, c) := by
  constructor
  · intro hI
    obtain ⟨w, hlen, hw⟩ := (perfect_threshold_certificate_iff I).mp hI
    have hn := side_le_sequence_length_of_count I hw.1
    refine ⟨frameUnarySide I.2 w, ?_, ?_⟩
    · rw [frameUnarySide_length, hlen]
      omega
    · simp only [UnarySideBitsAccepts, split_frameUnarySide]
      exact ⟨True.intro, hn, hw⟩
  · rintro ⟨c, _, hc⟩
    exact unarySideBitsAccepts_sound I c hc

/-- The unary-side relation gives the frozen membership statement once its
actual polynomial-time verifier has been assembled. -/
theorem perfect_inNP_of_unarySide_verifier_polyTime
    (h : PolyTimeDecidable (pairEncoding perfectEncoding (wordEncoding Bool)) UnarySideBitsAccepts) :
    InNP perfectEncoding (fun I => PerfectHPStringFold I.1 I.2) := by
  refine ⟨List Bool, wordEncoding Bool, fun w => ⟨w, rfl⟩,
    Polynomial.C 4 * Polynomial.X + Polynomial.C 1, UnarySideBitsAccepts, h, ?_⟩
  intro I
  constructor
  · intro hI
    obtain ⟨c, hlen, hc⟩ := (perfect_unarySide_certificate_iff I).mp hI
    refine ⟨c, ?_, hc⟩
    have hN := sequence_length_le_perfectEncoding I
    simpa [wordEncoding] using hlen.trans (by omega :
      4 * I.1.length + 1 ≤ 4 * (perfectEncoding.encode I).length + 1)
  · rintro ⟨c, _, hc⟩
    exact unarySideBitsAccepts_sound I c hc

/-- Squaring uses the actual copying machine followed by the unary multiplier. -/
noncomputable def unarySquareComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat (fun n : ℕ => n ^ 2) := by
  let h := TM2CompositionPoly.compose (TM2Fanout.diagonalComputable unaryFinEncodingNat)
    PerfectUnaryMultiplication.unaryMulComputable
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun n => by simpa only [Function.comp_apply, pow_two] using h.outputsFun n }

end ProteinFolding.CubicCertificates

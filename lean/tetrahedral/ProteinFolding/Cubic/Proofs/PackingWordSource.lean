import ProteinFolding.Cubic.Proofs.PackingWords
import ProteinFolding.Cubic.Proofs.PackingScaling
import ProteinFolding.Cubic.Proofs.PackingPadding
import ProteinFolding.Cubic.Proofs.ThresholdCertificateUnarySide

/-! Connecting unary packing inputs to the literal cubic-frame word. One
full-capacity item is added first, so every well-formed source has at least
two bins. A common even scale makes the capacity 4Q with Q greater than the
bin count. This file proves normalization arithmetic and an output-encoding
length bound. The packing/folding equivalence and the actual TM2 reduction
remain separate obligations; no hardness is assumed here. -/

namespace ProteinFolding.CubicPacking

open Computability

def sourceBins (I : Packing.Instance) : ℕ := I.bins + 1
def sourceQ (I : Packing.Instance) : ℕ := (sourceBins I + 1) * I.capacity
def sourceScale (I : Packing.Instance) : ℕ := 4 * (sourceBins I + 1)
def sourceWidths (I : Packing.Instance) : List ℕ :=
  (I.capacity :: I.sizes).map (sourceScale I * ·)
def sourceWord (I : Packing.Instance) : Sequence := frameWord (sourceBins I) (sourceQ I) (sourceWidths I)
def sourceSide (I : Packing.Instance) : ℕ := side (sourceBins I) (sourceQ I)

def normalizedPacking (I : Packing.Instance) : Packing.Instance :=
  ⟨sourceWidths I, 4 * sourceQ I, sourceBins I⟩

theorem normalizedPacking_eq_scale_pad (I : Packing.Instance) :
    normalizedPacking I = Packing.scale (sourceScale I) (Packing.pad I) := by
  cases I
  dsimp [normalizedPacking, Packing.scale, Packing.pad, sourceWidths, sourceScale, sourceQ, sourceBins]
  congr 1
  ring

theorem normalizedPacking_exact_iff (I : Packing.Instance) (h : Packing.WellFormed I) :
    (∃ parts, Packing.Exact (normalizedPacking I) parts) ↔ ∃ parts, Packing.Exact I parts := by
  rw [normalizedPacking_eq_scale_pad]
  exact (Packing.exists_exact_scale_iff (sourceScale I)
    (by dsimp [sourceScale]; omega) (Packing.pad I)).trans
    (Packing.exists_exact_pad_iff I h.1 h.2.2)

theorem sourceBins_two_le (I : Packing.Instance) (h : Packing.WellFormed I) :
    2 ≤ sourceBins I := by
  have := h.2.1
  dsimp [sourceBins]
  omega

theorem sourceQ_gt_bins (I : Packing.Instance) (h : Packing.WellFormed I) :
    sourceBins I < sourceQ I := by
  have hB : 1 ≤ I.capacity := by have := h.1; omega
  have hm := Nat.mul_le_mul_left (sourceBins I + 1) hB
  dsimp [sourceQ]
  nlinarith

theorem sourceScale_pos (I : Packing.Instance) : 0 < sourceScale I := by
  dsimp [sourceScale]
  omega

theorem sourceWidths_positive (I : Packing.Instance) (h : Packing.WellFormed I) :
    ∀ a ∈ sourceWidths I, 0 < a := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  apply Nat.mul_pos (sourceScale_pos I)
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h.1
  · exact h.2.2 b hb

theorem sourceWidths_even (I : Packing.Instance) : ∀ a ∈ sourceWidths I, Even a := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  refine ⟨2 * (sourceBins I + 1) * b, ?_⟩
  dsimp [sourceScale]
  ring

theorem sourceWidths_sum (I : Packing.Instance)
    (ht : I.sizes.sum = I.capacity * I.bins) :
    (sourceWidths I).sum = sourceBins I * (4 * sourceQ I) := by
  rw [sourceWidths, Packing.sum_scale, List.sum_cons, ht]
  dsimp [sourceScale, sourceBins, sourceQ]
  ring

/-- The normalized chain has the frozen perfect problem's exact H count. -/
theorem sourceWord_count (I : Packing.Instance) (h : Packing.WellFormed I)
    (ht : I.sizes.sum = I.capacity * I.bins) :
    hydrophobicCount (sourceWord I) = sourceSide I ^ 3 :=
  frameWord_count _ _ _ (by have := sourceBins_two_le I h; omega) (sourceWidths_sum I ht)

def sourcePerfectInstance (I : Packing.Instance) (h : Packing.WellFormed I)
    (ht : I.sizes.sum = I.capacity * I.bins) : PerfectInstance where
  side := sourceSide I
  sequence := sourceWord I
  count_eq := sourceWord_count I h ht

theorem sourceSide_encoding_bound (I : Packing.Instance) :
    sourceSide I ≤ 8 * (Packing.instanceEncoding.encode I).length ^ 3 := by
  let L := (Packing.instanceEncoding.encode I).length
  have hL : 2 ≤ L := by dsimp [L]; rw [Packing.instanceEncoding_length]; omega
  have hq : sourceBins I ≤ L := by
    dsimp [sourceBins, L]
    rw [Packing.instanceEncoding_length]
    omega
  have hq' : sourceBins I + 1 ≤ L := by
    dsimp [sourceBins, L]
    rw [Packing.instanceEncoding_length]
    omega
  have hB : I.capacity ≤ L := by dsimp [L]; rw [Packing.instanceEncoding_length]; omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul hq hq') hB
  have hcube : L ≤ L ^ 3 := Nat.le_pow (by decide : 0 < 3)
  change sourceSide I ≤ 8 * L ^ 3
  dsimp [sourceSide, side, depth, beta, sourceQ]
  nlinarith

/-- The literal output has degree-nine size in the actual unary input length.
The exponent is a coarse bound; no binary numeric value is used as input size. -/
theorem sourceWord_encoding_bound (I : Packing.Instance) (h : Packing.WellFormed I)
    (ht : I.sizes.sum = I.capacity * I.bins) :
    (sourceWord I).length ≤ 51200 * (Packing.instanceEncoding.encode I).length ^ 9 := by
  have hw := frameWord_length_le (sourceBins I) (sourceQ I) (sourceWidths I)
    (by have := sourceBins_two_le I h; omega) (sourceWidths_sum I ht) (sourceWidths_positive I h)
  have hs := Nat.pow_le_pow_left (sourceSide_encoding_bound I) 3
  calc
    _ ≤ 100 * sourceSide I ^ 3 := hw
    _ ≤ 100 * (8 * (Packing.instanceEncoding.encode I).length ^ 3) ^ 3 :=
      Nat.mul_le_mul_left 100 hs
    _ = _ := by ring

def sourceGuard (I : Packing.Instance) : Bool :=
  decide (0 < I.capacity ∧ 0 < I.bins ∧
    (∀ a ∈ I.sizes, 0 < a ∧ Even a) ∧ I.sizes.sum = I.capacity * I.bins)

theorem sourceGuard_spec (I : Packing.Instance) : sourceGuard I = true ↔
    Packing.WellFormed I ∧ (∀ a ∈ I.sizes, Even a) ∧ I.sizes.sum = I.capacity * I.bins := by
  simp only [sourceGuard, decide_eq_true_eq, Packing.WellFormed]
  constructor
  · rintro ⟨hB, hK, ha, ht⟩
    exact ⟨⟨hB, hK, fun a ha' => (ha a ha').1⟩, fun a ha' => (ha a ha').2, ht⟩
  · rintro ⟨⟨hB, hK, hp⟩, he, ht⟩
    exact ⟨hB, hK, fun a ha => ⟨hp a ha, he a ha⟩, ht⟩

/-- Adding a full bin and scaling do not change the source's exact packability.
All original modified-packing side conditions remain explicit in the guard. -/
theorem modified_iff_guard_normalized (I : Packing.Instance) :
    Packing.ModifiedAccepts I ↔ sourceGuard I = true ∧
      ∃ parts, Packing.Exact (normalizedPacking I) parts := by
  constructor
  · rintro ⟨hw, he, ht, hp⟩
    exact ⟨(sourceGuard_spec I).mpr ⟨hw, he, ht⟩, (normalizedPacking_exact_iff I hw).mpr hp⟩
  · rintro ⟨hg, hp⟩
    obtain ⟨hw, he, ht⟩ := (sourceGuard_spec I).mp hg
    exact ⟨hw, he, ht, (normalizedPacking_exact_iff I hw).mp hp⟩

/-- A total candidate reduction. Inputs violating the source side conditions
go to a fixed no-instance. The geometric equivalence is not asserted here. -/
def packingToPerfect (I : Packing.Instance) : PerfectInput :=
  if sourceGuard I then (sourceWord I, sourceSide I) else ([], 1)

theorem packingToPerfect_of_guard (I : Packing.Instance) (h : sourceGuard I = true) :
    packingToPerfect I = (sourceWord I, sourceSide I) := by simp [packingToPerfect, h]

theorem packingToPerfect_rejects_invalid (I : Packing.Instance) (h : sourceGuard I = false) :
    ¬ PerfectHPStringFold (packingToPerfect I).1 (packingToPerfect I).2 := by
  have he : packingToPerfect I = ([], 1) := by simp [packingToPerfect, h]
  rw [he]
  intro hfold
  exact (by decide : hydrophobicCount [] ≠ 1) hfold.1

theorem binaryPos_length_le (n : PosNum) : (encodePosNum n).length ≤ (n : ℕ) := by
  induction n with
  | one => decide
  | bit0 n ih =>
    have hp := PosNum.to_nat_pos n
    simp only [encodePosNum, List.length_cons, PosNum.cast_bit0]
    omega
  | bit1 n ih =>
    simp only [encodePosNum, List.length_cons, PosNum.cast_bit1]
    omega

theorem binaryNat_length_le (n : ℕ) : (encodeNat n).length ≤ n := by
  have hn : ∀ m : Num, (encodeNum m).length ≤ (m : ℕ) := by
    intro m
    cases m with
    | zero => decide
    | pos m => exact binaryPos_length_le m
  simpa [encodeNat] using hn (n : Num)

theorem perfectEncoding_length (S : Sequence) (n : ℕ) :
    (perfectEncoding.encode (S, n)).length = S.length + 1 + (encodeNat n).length := by
  simp [perfectEncoding, pairEncoding, sequenceEncoding, wordEncoding,
    finEncodingNatBool, encodingNatBool]
  omega

/-- The entire candidate output, including its unchanged binary side field,
has polynomial encoding length on every source input, valid or invalid. -/
theorem packingToPerfect_encoding_bound (I : Packing.Instance) :
    (perfectEncoding.encode (packingToPerfect I)).length ≤
      102401 * (Packing.instanceEncoding.encode I).length ^ 9 := by
  let L := (Packing.instanceEncoding.encode I).length
  have hL : 1 ≤ L := by dsimp [L]; rw [Packing.instanceEncoding_length]; omega
  have hpow : 1 ≤ L ^ 9 := by nlinarith [Nat.le_pow (a := L) (by decide : 0 < 9)]
  cases hg : sourceGuard I with
  | false =>
    have he : packingToPerfect I = ([], 1) := by simp [packingToPerfect, hg]
    rw [he]
    have hlength : (perfectEncoding.encode ([], 1)).length = 2 := by
      rw [perfectEncoding_length]
      change 1 + (encodeNat 1).length = 2
      rw [show (1 : ℕ) = ((1 : Num) : ℕ) from rfl]
      simp only [encodeNat, Num.of_to_nat]
      rfl
    rw [hlength]
    change 2 ≤ 102401 * L ^ 9
    omega
  | true =>
    obtain ⟨hw, _, ht⟩ := (sourceGuard_spec I).mp hg
    rw [packingToPerfect_of_guard I hg]
    have hlength := sourceWord_encoding_bound I hw ht
    have hs := CubicCertificates.side_le_sequence_length_of_count (sourceWord I, sourceSide I)
      (sourceWord_count I hw ht)
    have hb := binaryNat_length_le (sourceSide I)
    rw [perfectEncoding_length]
    change (sourceWord I).length + 1 + (encodeNat (sourceSide I)).length ≤ 102401 * L ^ 9
    change (sourceWord I).length ≤ 51200 * L ^ 9 at hlength
    dsimp only [Prod.fst, Prod.snd] at hs
    omega

end ProteinFolding.CubicPacking

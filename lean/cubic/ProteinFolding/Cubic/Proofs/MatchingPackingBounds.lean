import ProteinFolding.Cubic.Proofs.MatchingPackingReduction

/-! Unary output-size bound for the matching-to-packing reduction. Its
polynomial degree is constant: five radix digits and one leading offset are
used independently of the number of vertices. This is a size proof; an actual
TM2 runtime witness remains a separate obligation. -/

namespace ProteinFolding.MatchingPacking

open Computability ThreeDimensionalMatching NumericPacking

theorem tripleEncoding_length (t : Triple) :
    (encodeTriple t).length = t.1 + t.2.1 + t.2.2 + 2 := by
  simp [encodeTriple, tripleFieldsEncoding, pairEncoding, unaryFinEncodingNat, Packing.unary_length]
  omega

theorem triplesEncoding_length (ts : List Triple) :
    (triplesEncoding.encode ts).length = (ts.map (fun t => t.1 + t.2.1 + t.2.2 + 3)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [triplesEncoding, SAT.encTerminated, List.flatMap_cons, List.length_append,
      tripleEncoding_length, List.length_cons, List.length_nil, List.map_cons, List.sum_cons] at *
    omega

theorem matchingEncoding_length (I : ThreeDimensionalMatching.Instance) :
    (ThreeDimensionalMatching.instanceEncoding.encode I).length =
      I.size + 1 + (I.triples.map (fun t => t.1 + t.2.1 + t.2.2 + 3)).sum := by
  simp [ThreeDimensionalMatching.instanceEncoding, ThreeDimensionalMatching.fieldsEncoding,
    pairEncoding, unaryFinEncodingNat, Packing.unary_length, triplesEncoding_length]
  omega

theorem input_size_bounds (I : ThreeDimensionalMatching.Instance) :
    1 ≤ (ThreeDimensionalMatching.instanceEncoding.encode I).length ∧
      I.size ≤ (ThreeDimensionalMatching.instanceEncoding.encode I).length ∧
        I.triples.length ≤ (ThreeDimensionalMatching.instanceEncoding.encode I).length := by
  rw [matchingEncoding_length]
  have hm := sum_lower_bound (I.triples.map (fun t => t.1 + t.2.1 + t.2.2 + 3)) 1 (by
    intro v hv
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hv
    omega)
  simp only [List.length_map, Nat.mul_one] at hm
  omega

theorem coordinateTokens_length_le (make : ℕ → Bool → Token) (n : ℕ) (xs : List ℕ) :
    (coordinateTokens make n xs).length ≤ n + xs.length := by
  have hd := (List.diff_sublist xs (List.range n)).length_le
  simpa only [coordinateTokens, List.length_append, List.length_map, List.length_range] using
    Nat.add_le_add_left hd n

theorem tokens_length_le (I : ThreeDimensionalMatching.Instance) :
    (tokens I).length ≤ 4 * I.triples.length + 3 * I.size := by
  have hx := coordinateTokens_length_le Token.x I.size (xCoordinates I)
  have hy := coordinateTokens_length_le Token.y I.size (yCoordinates I)
  have hz := coordinateTokens_length_le Token.z I.size (zCoordinates I)
  simp only [xCoordinates, yCoordinates, zCoordinates, List.length_map] at hx hy hz
  simp only [tokens, List.length_append, List.length_map, xCoordinates, yCoordinates, zCoordinates]
  omega

theorem raw_sum_bound (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I) :
    (rawInstance I).sizes.sum ≤ (tokens I).length * (2 * offset I.size) := by
  have hs := sum_upper_bound ((tokens I).map (Token.value I.size)) (2 * offset I.size) (by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    have hv := Token.value_polynomial_bound I.size t (tokens_valid I hw t ht)
    exact hv.le)
  simpa only [rawInstance, List.length_map] using hs

theorem doubledEncoding_length (I : ThreeDimensionalMatching.Instance) :
    (Packing.instanceEncoding.encode (Packing.scale 2 (rawInstance I))).length =
      2 * (rawInstance I).sizes.sum + (tokens I).length +
        2 * NumericPacking.capacity I.size + I.triples.length + 2 := by
  rw [Packing.instanceEncoding_length]
  simp only [Packing.scale, List.length_map, Packing.sum_scale, rawInstance]

theorem doubled_encoding_bound (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I) :
    (Packing.instanceEncoding.encode (Packing.scale 2 (rawInstance I))).length ≤
      100 * (72 * (ThreeDimensionalMatching.instanceEncoding.encode I).length) ^ 7 := by
  let L := (ThreeDimensionalMatching.instanceEncoding.encode I).length
  obtain ⟨hL, hn, hm⟩ := input_size_bounds I
  change 1 ≤ L at hL
  change I.size ≤ L at hn
  change I.triples.length ≤ L at hm
  have ht : (tokens I).length ≤ 7 * L := by have := tokens_length_le I; omega
  have hs := raw_sum_bound I hw
  have hc := capacity_lt_five_offsets I.size
  have ho : 1 ≤ offset I.size := offset_pos I.size
  have hb : base I.size ≤ 72 * L := by dsimp [base]; omega
  have hpow : offset I.size ≤ (72 * L) ^ 6 := Nat.pow_le_pow_left hb 6
  have hs' : (rawInstance I).sizes.sum ≤ 14 * (offset I.size * L) := by
    have ht' := Nat.mul_le_mul_right (2 * offset I.size) ht
    nlinarith
  have hprod : offset I.size * L ≤ (72 * L) ^ 7 := by
    have hmul := Nat.mul_le_mul_right L hpow
    have hmul' := Nat.mul_le_mul_left ((72 * L) ^ 6) (by omega : L ≤ 72 * L)
    calc
      offset I.size * L ≤ (72 * L) ^ 6 * L := hmul
      _ ≤ (72 * L) ^ 6 * (72 * L) := hmul'
      _ = (72 * L) ^ 7 := rfl
  have hoL : offset I.size ≤ offset I.size * L := by nlinarith
  have hLo : L ≤ offset I.size * L := by nlinarith
  have hprodpos : 1 ≤ offset I.size * L := by nlinarith
  rw [doubledEncoding_length]
  change 2 * (rawInstance I).sizes.sum + (tokens I).length +
    2 * NumericPacking.capacity I.size + I.triples.length + 2 ≤ 100 * (72 * L) ^ 7
  nlinarith

/-- The reduction has polynomial output length in the actual unary source
encoding on every raw input, including the two explicit boundary branches. -/
theorem toModified_encoding_bound (I : ThreeDimensionalMatching.Instance) :
    (Packing.instanceEncoding.encode (toModified I)).length ≤
      100 * (72 * (ThreeDimensionalMatching.instanceEncoding.encode I).length) ^ 7 := by
  obtain ⟨hL, _, _⟩ := input_size_bounds I
  have hp : 1 ≤ (72 * (ThreeDimensionalMatching.instanceEncoding.encode I).length) ^ 7 := by
    have hb : 0 < 72 * (ThreeDimensionalMatching.instanceEncoding.encode I).length := by omega
    exact Nat.pow_pos hb
  by_cases hw : WellFormed I
  · by_cases hn : I.size = 0
    · simp only [toModified, if_pos hw, if_pos hn]
      rw [Packing.instanceEncoding_length]
      change 8 ≤ _
      omega
    · simpa only [toModified, if_pos hw, if_neg hn] using doubled_encoding_bound I hw
  · simp only [toModified, if_neg hw]
    rw [Packing.instanceEncoding_length]
    change 4 ≤ _
    omega

end ProteinFolding.MatchingPacking

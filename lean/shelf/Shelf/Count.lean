import Mathlib
import ProteinFolding.Cubic.Proofs.PackingWords
import Shelf.Word

/-!
# Counting the letters of the string

Lemma 11 of the paper (first sentence): the string of a normalised instance has exactly
`n³` letters `H`. We also compute the length of the string.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue List

/-- The empty string has no `H`. -/
theorem hydrophobicCount_nil : hydrophobicCount ([] : Sequence) = 0 := by
  simp [hydrophobicCount, hydrophobicIndices]

/-- The number of `H` of a concatenation of words is the sum over the words. -/
theorem hydrophobicCount_flatten (L : List Sequence) :
    hydrophobicCount L.flatten = (L.map hydrophobicCount).sum := by
  induction L with
  | nil => simp [hydrophobicCount_nil]
  | cons w L ih =>
    simp [List.flatten_cons, CubicPacking.hydrophobicCount_append, ih]

/-- The number of `H` of a word repeated `k` times. -/
theorem hydrophobicCount_flatten_replicate (k : ℕ) (w : Sequence) :
    hydrophobicCount (replicate k w).flatten = k * hydrophobicCount w := by
  rw [hydrophobicCount_flatten]
  simp

/-- The dense run `D(r)` has `r` letters `H`. -/
theorem hydrophobicCount_denseRun (r : ℕ) : hydrophobicCount (denseRun r) = r := by
  cases r with
  | zero => simp [denseRun, hydrophobicCount_nil]
  | succ r =>
    simp [denseRun, CubicCertificates.hydrophobicCount_cons,
      hydrophobicCount_flatten_replicate, hydrophobicCount_nil]
    omega

/-- The dense run `D(r)` has `3 r - 2` letters. -/
theorem length_denseRun (r : ℕ) : (denseRun r).length = 3 * r - 2 := by
  cases r with
  | zero => simp [denseRun]
  | succ r =>
    simp [denseRun, List.length_flatten]
    omega

/-- There are `m + 1` separators. -/
theorem hydrophobicCount_separators (J : Packing.Instance) :
    hydrophobicCount (separators J) = J.bins + 1 := by
  simp [separators, CubicCertificates.hydrophobicCount_cons,
    hydrophobicCount_flatten_replicate, CubicPacking.hydrophobicCount_append,
    CubicPacking.hydrophobicCount_replicate, hydrophobicCount_nil]
  omega

/-- The items have `∑ aᵢ` letters `H`. -/
theorem hydrophobicCount_itemsWord (J : Packing.Instance) :
    hydrophobicCount (itemsWord J) = J.sizes.sum := by
  simp [itemsWord, hydrophobicCount_flatten, CubicPacking.hydrophobicCount_append,
    CubicPacking.hydrophobicCount_replicate, hydrophobicCount_denseRun, Function.comp_def]

/-- `12 n ≤ n³ + 16` for every natural `n`, since `n³ + 16 - 12 n = (n - 2)² (n + 4)`. -/
theorem twelve_mul_le (n : ℕ) : 12 * n ≤ n ^ 3 + 16 := by
  have : (0 : ℤ) ≤ ((n : ℤ) - 2) ^ 2 * ((n : ℤ) + 4) := by positivity
  have h : (12 * n : ℤ) ≤ (n : ℤ) ^ 3 + 16 := by nlinarith
  exact_mod_cast h

/-- Lemma 11, first sentence: the string of a normalised instance has exactly `n³` letters `H`. -/
theorem hydrophobicCount_shelfWord (J : Packing.Instance) (hJ : Normalised J) :
    hydrophobicCount (shelfWord J) = side J ^ 3 := by
  have hsum := hJ.sum_eq
  simp only [shelfWord, shelfPieces, hydrophobicCount_flatten, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, CubicPacking.hydrophobicCount_replicate,
    hydrophobicCount_denseRun, hydrophobicCount_separators, hydrophobicCount_itemsWord,
    CubicCertificates.hydrophobicCount_cons, hydrophobicCount_nil, coreLength, hsum]
  have h12 := twelve_mul_le (side J)
  have hside : side J = J.bins * J.capacity + J.bins + 3 := by
    simp only [side]; ring
  simp only [if_true, if_false, reduceCtorEq]
  generalize side J ^ 3 = c at *
  rw [Nat.mul_comm J.capacity J.bins]
  generalize J.bins * J.capacity = mb at *
  omega

/-- The length of the string, as a formula. -/
theorem length_shelfWord (J : Packing.Instance) :
    (shelfWord J).length =
      coreLength (side J) + 2 + (3 * (9 * side J - 10) - 2) + linkerLength J
        + (3 * (side J - 2) - 2) + side J + (1 + J.bins * (J.capacity + 7)) + side J
        + (3 * (side J - 2) - 2) + (J.sizes.map fun a => linkerLength J + (3 * a - 2)).sum + 1 := by
  simp only [shelfWord, shelfPieces, List.length_flatten, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_replicate, length_denseRun]
  have hsep : (separators J).length = 1 + J.bins * (J.capacity + 7) := by
    simp [separators, List.length_flatten]; ring
  have hitems : (itemsWord J).length =
      (J.sizes.map fun a => linkerLength J + (3 * a - 2)).sum := by
    simp [itemsWord, List.length_flatten, length_denseRun, Function.comp_def]
  rw [hsep, hitems]
  simp
  ring

end ProteinFolding.Shelf

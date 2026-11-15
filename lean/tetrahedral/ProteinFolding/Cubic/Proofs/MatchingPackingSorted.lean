import ProteinFolding.Cubic.Proofs.MatchingPackingBounds
import Mathlib.Data.List.Nodup

/-! A second numerical reduction witness, with dummy items emitted in vertex
order. It preserves all existing definitions: its item list is a permutation
of the earlier construction. Counting multiplicities is simpler to implement
than iterated list erasure, while exact packing ignores item-list order. -/

namespace ProteinFolding.MatchingPacking

open ThreeDimensionalMatching NumericPacking

def sortedDummies (n : ℕ) (xs : List ℕ) : List ℕ :=
  (List.range n).flatMap (fun i => List.replicate (xs.count i - 1) i)

theorem count_flatMap_replicate (ids : List ℕ) (hd : ids.Nodup) (f : ℕ → ℕ) (j : ℕ) :
    (ids.flatMap (fun i => List.replicate (f i) i)).count j = if j ∈ ids then f j else 0 := by
  induction ids with
  | nil => simp
  | cons i ids ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hd
    have ht := ih hnd
    by_cases hij : i = j
    · subst j
      simp [List.flatMap_cons, List.count_append, ht, hnot]
    · simp [List.flatMap_cons, List.count_append, List.count_replicate, hij, ht, Ne.symm hij]

theorem sortedDummies_count (n : ℕ) (xs : List ℕ) (j : ℕ) :
    (sortedDummies n xs).count j = if j < n then xs.count j - 1 else 0 := by
  simpa only [sortedDummies, List.mem_range] using
    count_flatMap_replicate (List.range n) (show (List.range n).Nodup from List.nodup_range) (fun i => xs.count i - 1) j

theorem sortedDummies_perm (n : ℕ) (xs : List ℕ) (hx : ∀ i ∈ xs, i < n) :
    (sortedDummies n xs).Perm (xs.diff (List.range n)) := by
  apply List.perm_iff_count.mpr
  intro j
  rw [sortedDummies_count, List.count_diff]
  rw [List.count_eq_of_nodup (show (List.range n).Nodup from List.nodup_range)]
  by_cases hj : j < n
  · simp [List.mem_range, hj]
  · have hn : j ∉ xs := fun hm => hj (hx j hm)
    simp [List.mem_range, hj, List.count_eq_zero_of_not_mem hn]

def sortedCoordinateTokens (make : ℕ → Bool → Token) (n : ℕ) (xs : List ℕ) : List Token :=
  (List.range n).map (fun i => make i true) ++ (sortedDummies n xs).map (fun i => make i false)

theorem sortedCoordinateTokens_perm (make : ℕ → Bool → Token) (n : ℕ) (xs : List ℕ)
    (hx : ∀ i ∈ xs, i < n) :
    (sortedCoordinateTokens make n xs).Perm (coordinateTokens make n xs) :=
  (List.Perm.refl _).append ((sortedDummies_perm n xs hx).map (fun i => make i false))

def sortedTokens (I : ThreeDimensionalMatching.Instance) : List Token :=
  I.triples.map selectorToken ++ sortedCoordinateTokens Token.x I.size (xCoordinates I) ++
    sortedCoordinateTokens Token.y I.size (yCoordinates I) ++ sortedCoordinateTokens Token.z I.size (zCoordinates I)

theorem sortedTokens_perm (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I) :
    (sortedTokens I).Perm (tokens I) := by
  have hx := sortedCoordinateTokens_perm Token.x I.size (xCoordinates I) (by
    intro i hi; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hi; exact (hw t ht).1)
  have hy := sortedCoordinateTokens_perm Token.y I.size (yCoordinates I) (by
    intro i hi; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hi; exact (hw t ht).2.1)
  have hz := sortedCoordinateTokens_perm Token.z I.size (zCoordinates I) (by
    intro i hi; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hi; exact (hw t ht).2.2)
  exact (((List.Perm.refl _).append hx).append hy).append hz

def sortedRawInstance (I : ThreeDimensionalMatching.Instance) : Packing.Instance :=
  ⟨(sortedTokens I).map (Token.value I.size), NumericPacking.capacity I.size, I.triples.length⟩

theorem modified_sizes_perm (xs ys : List ℕ) (hp : xs.Perm ys) (B K : ℕ) :
    Packing.ModifiedAccepts ⟨xs, B, K⟩ ↔ Packing.ModifiedAccepts ⟨ys, B, K⟩ := by
  have forward (a b : List ℕ) (hab : a.Perm b)
      (h : Packing.ModifiedAccepts ⟨a, B, K⟩) : Packing.ModifiedAccepts ⟨b, B, K⟩ := by
    obtain ⟨⟨hB, hK, hpos⟩, heven, htotal, ps, hparts⟩ := h
    refine ⟨⟨hB, hK, fun s hs => hpos s (hab.mem_iff.mpr hs)⟩,
      fun s hs => heven s (hab.mem_iff.mpr hs), ?_, ps, hparts.1, ?_, hparts.2.2⟩
    · exact hab.sum_eq.symm.trans htotal
    · exact hab.symm.trans hparts.2.1
  exact ⟨forward xs ys hp, forward ys xs hp.symm⟩

theorem sortedRaw_modified_iff (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I) :
    Packing.ModifiedAccepts (Packing.scale 2 (sortedRawInstance I)) ↔
      Packing.ModifiedAccepts (Packing.scale 2 (rawInstance I)) :=
  modified_sizes_perm _ _ (((sortedTokens_perm I hw).map (Token.value I.size)).map (2 * ·)) _ _

def sortedToModified (I : ThreeDimensionalMatching.Instance) : Packing.Instance :=
  if WellFormed I then
    if I.size = 0 then yesPacking else Packing.scale 2 (sortedRawInstance I)
  else noPacking

theorem sortedToModified_equiv (I : ThreeDimensionalMatching.Instance) :
    Packing.ModifiedAccepts (sortedToModified I) ↔ Packing.ModifiedAccepts (toModified I) := by
  by_cases hw : WellFormed I
  · by_cases hn : I.size = 0
    · simp only [sortedToModified, toModified, if_pos hw, if_pos hn]
    · simp only [sortedToModified, toModified, if_pos hw, if_neg hn]
      exact sortedRaw_modified_iff I hw
  · simp only [sortedToModified, toModified, if_neg hw]

/-- Reordering the dummy items changes the reducing function, while preserving
the source/target predicates and every definition of the original candidate. -/
theorem sortedToModified_correct (I : ThreeDimensionalMatching.Instance) :
    Accepts I ↔ Packing.ModifiedAccepts (sortedToModified I) :=
  (toModified_correct I).trans (sortedToModified_equiv I).symm

theorem sortedToModified_encoding_length (I : ThreeDimensionalMatching.Instance) :
    (Packing.instanceEncoding.encode (sortedToModified I)).length =
      (Packing.instanceEncoding.encode (toModified I)).length := by
  by_cases hw : WellFormed I
  · by_cases hn : I.size = 0
    · simp only [sortedToModified, toModified, if_pos hw, if_pos hn]
    · simp only [sortedToModified, toModified, if_pos hw, if_neg hn]
      rw [Packing.instanceEncoding_length, Packing.instanceEncoding_length]
      have hp := ((sortedTokens_perm I hw).map (Token.value I.size)).map (2 * ·)
      have hs := hp.sum_eq
      have hl := hp.length_eq
      dsimp only [Packing.scale, sortedRawInstance, rawInstance]
      rw [hs, hl]
  · simp only [sortedToModified, toModified, if_neg hw]

theorem sortedToModified_encoding_bound (I : ThreeDimensionalMatching.Instance) :
    (Packing.instanceEncoding.encode (sortedToModified I)).length ≤
      100 * (72 * (ThreeDimensionalMatching.instanceEncoding.encode I).length) ^ 7 := by
  rw [sortedToModified_encoding_length]
  exact toModified_encoding_bound I

end ProteinFolding.MatchingPacking

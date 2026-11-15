import ProteinFolding.Common.SAT.ThreeDimensionalMatching
import ProteinFolding.Common.NumericPackingBins
import ProteinFolding.Cubic.Proofs.PackingSources
import Mathlib.Data.List.Count

/-! The explicit bounded numerical instance associated to 3-dimensional
matching. Each coordinate has one real token; remaining occurrences are
dummy tokens. Every triple contributes a selector. All numbers have magnitude
polynomial in the explicitly represented source universe.

This file develops the combinatorial reduction. A polynomial-time machine and
the CNF-to-matching reduction are separate obligations; no hardness is assumed.
-/

namespace ProteinFolding.MatchingPacking

open ThreeDimensionalMatching NumericPacking

local instance : BEq Triple := instBEqOfDecidableEq

def xCoordinates (I : ThreeDimensionalMatching.Instance) : List ℕ := I.triples.map Prod.fst
def yCoordinates (I : ThreeDimensionalMatching.Instance) : List ℕ := I.triples.map (fun t => t.2.1)
def zCoordinates (I : ThreeDimensionalMatching.Instance) : List ℕ := I.triples.map (fun t => t.2.2)

def selectorToken (t : Triple) : Token := .triple t.1 t.2.1 t.2.2

def coordinateTokens (make : ℕ → Bool → Token) (n : ℕ) (xs : List ℕ) : List Token :=
  (List.range n).map (fun i => make i true) ++ (xs.diff (List.range n)).map (fun i => make i false)

def tokens (I : ThreeDimensionalMatching.Instance) : List Token :=
  I.triples.map selectorToken ++ coordinateTokens Token.x I.size (xCoordinates I) ++
    coordinateTokens Token.y I.size (yCoordinates I) ++ coordinateTokens Token.z I.size (zCoordinates I)

def rawInstance (I : ThreeDimensionalMatching.Instance) : Packing.Instance :=
  ⟨(tokens I).map (Token.value I.size), NumericPacking.capacity I.size, I.triples.length⟩

def quadruple (real : Bool) (t : Triple) : List Token :=
  [selectorToken t, .x t.1 real, .y t.2.1 real, .z t.2.2 real]

theorem quadruple_sum (n : ℕ) (t : Triple)
    (ht : t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n) (real : Bool) :
    ((quadruple real t).map (Token.value n)).sum = NumericPacking.capacity n := by
  simpa [quadruple, selectorToken, Token.value, Nat.add_assoc] using
    (selector_quad_iff n t.1 t.2.1 t.2.2 t.1 t.2.1 t.2.2
      ht.1 ht.2.1 ht.2.2 ht.1 ht.2.1 ht.2.2 real real real).mpr
      ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem append_diff_self {A : Type} [DecidableEq A] (xs ys : List A) :
    (xs ++ ys).diff xs = ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [List.diff_cons] using ih

/-- Removing selected occurrences commutes with projecting their coordinates,
up to permutation, even when the coordinate map identifies distinct triples. -/
theorem diff_map_perm {A B : Type} [DecidableEq A] [DecidableEq B]
    (selected all : List A) (h : selected.Subperm all) (f : A → B) :
    ((all.map f).diff (selected.map f)).Perm ((all.diff selected).map f) := by
  have hp : (selected ++ all.diff selected).Perm all :=
    List.subperm_append_diff_self_of_count_le (List.subperm_ext_iff.mp h)
  have hm := (hp.map f).symm.diff_right (selected.map f)
  simpa only [List.map_append, append_diff_self] using hm

theorem coordinateTokens_perm (make : ℕ → Bool → Token) (I : ThreeDimensionalMatching.Instance)
    (selected : List Triple) (hsub : selected.Subperm I.triples) (f : Triple → ℕ)
    (hcover : (selected.map f).Perm (List.range I.size)) :
    (coordinateTokens make I.size (I.triples.map f)).Perm
      ((selected.map (fun t => make (f t) true)) ++
        ((I.triples.diff selected).map (fun t => make (f t) false))) := by
  have hd : ((I.triples.map f).diff (List.range I.size)).Perm
      ((I.triples.diff selected).map f) := by
    rw [← hcover.diff_left (I.triples.map f)]
    exact diff_map_perm selected I.triples hsub f
  have hr := hcover.symm.map (fun i => make i true)
  have hf := hd.map (fun i => make i false)
  simpa only [coordinateTokens, List.map_map, Function.comp_def] using hr.append hf

theorem quadruple_flatten_perm {A : Type} [DecidableEq A] (ts : List Triple)
    (f g h k : Triple → A) :
    (ts.flatMap (fun t => [f t, g t, h t, k t])).Perm
      (ts.map f ++ ts.map g ++ ts.map h ++ ts.map k) := by
  apply List.perm_iff_count.mpr
  intro a
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.flatMap_cons, List.map_cons, List.count_append, List.count_cons,
      List.count_nil] at *
    omega

theorem quadruple_tokens_perm (I : ThreeDimensionalMatching.Instance) (selected : List Triple)
    (h : Matches I selected) :
    ((selected.flatMap (quadruple true)) ++
      ((I.triples.diff selected).flatMap (quadruple false))).Perm (tokens I) := by
  have hp : (selected ++ I.triples.diff selected).Perm I.triples :=
    List.subperm_append_diff_self_of_count_le (List.subperm_ext_iff.mp h.1)
  have hselector := hp.map selectorToken
  have hx := coordinateTokens_perm Token.x I selected h.1 Prod.fst h.2.1
  have hy := coordinateTokens_perm Token.y I selected h.1 (fun t => t.2.1) h.2.2.1
  have hz := coordinateTokens_perm Token.z I selected h.1 (fun t => t.2.2) h.2.2.2
  have hreal := quadruple_flatten_perm selected selectorToken
    (fun t => Token.x t.1 true) (fun t => Token.y t.2.1 true) (fun t => Token.z t.2.2 true)
  have hdummy := quadruple_flatten_perm (I.triples.diff selected) selectorToken
    (fun t => Token.x t.1 false) (fun t => Token.y t.2.1 false) (fun t => Token.z t.2.2 false)
  apply List.perm_iff_count.mpr
  intro a
  have hs := hselector.count_eq a
  have hxc := hx.count_eq a
  have hyc := hy.count_eq a
  have hzc := hz.count_eq a
  have hr := hreal.count_eq a
  have hd := hdummy.count_eq a
  simp only [List.count_append, List.map_append] at hs hxc hyc hzc hr hd
  simp only [tokens, List.count_append, xCoordinates, yCoordinates, zCoordinates]
  change (selected.flatMap (fun t => [selectorToken t, Token.x t.1 true,
      Token.y t.2.1 true, Token.z t.2.2 true])).count a +
    ((I.triples.diff selected).flatMap (fun t => [selectorToken t, Token.x t.1 false,
      Token.y t.2.1 false, Token.z t.2.2 false])).count a = _
  omega

def parts (n : ℕ) (selected rest : List Triple) : List (List ℕ) :=
  selected.map (fun t => (quadruple true t).map (Token.value n)) ++
    rest.map (fun t => (quadruple false t).map (Token.value n))

/-- A genuine three-dimensional matching yields an exact numerical packing.
Selectors outside the matching use three dummy tokens; selectors in the
matching use three real tokens. No item occurrence is discarded or duplicated. -/
theorem exists_exact_of_matches (I : ThreeDimensionalMatching.Instance)
    (hw : WellFormed I) (selected : List Triple) (hm : Matches I selected) :
    ∃ ps, Packing.Exact (rawInstance I) ps := by
  let rest := I.triples.diff selected
  have hsplit : (selected ++ rest).Perm I.triples :=
    List.subperm_append_diff_self_of_count_le (List.subperm_ext_iff.mp hm.1)
  refine ⟨parts I.size selected rest, ?_, ?_, ?_⟩
  · change (parts I.size selected rest).length = I.triples.length
    simpa only [parts, List.length_append, List.length_map] using hsplit.length_eq
  · have hp := (quadruple_tokens_perm I selected hm).symm.map (Token.value I.size)
    change ((tokens I).map (Token.value I.size)).Perm (parts I.size selected rest).flatten
    have he : (parts I.size selected rest).flatten =
        (selected.flatMap (quadruple true) ++ rest.flatMap (quadruple false)).map (Token.value I.size) := by
      simp [parts, List.flatMap_def, List.map_flatten, Function.comp_def]
    rw [he]
    exact hp
  · intro p hp
    change p.sum = NumericPacking.capacity I.size
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
      apply quadruple_sum
      exact hw t (hsplit.mem_iff.mp (List.mem_append_left rest ht))
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
      apply quadruple_sum
      exact hw t (hsplit.mem_iff.mp (List.mem_append_right selected ht))

theorem coordinateTokens_valid (make : ℕ → Bool → Token) (n : ℕ) (xs : List ℕ)
    (hm : ∀ i r, i < n → (make i r).Valid n) (hx : ∀ i ∈ xs, i < n) :
    ∀ t ∈ coordinateTokens make n xs, t.Valid n := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    exact hm i true (List.mem_range.mp hi)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    exact hm i false (hx i (List.diff_subset xs (List.range n) hi))

theorem tokens_valid (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I) :
    ∀ t ∈ tokens I, t.Valid I.size := by
  intro t ht
  simp only [tokens, List.mem_append, or_assoc] at ht
  rcases ht with ht | ht | ht | ht
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact hw u hu
  · apply coordinateTokens_valid Token.x I.size (xCoordinates I) (fun _ _ hi => hi) _ t ht
    intro i hi
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
    exact (hw u hu).1
  · apply coordinateTokens_valid Token.y I.size (yCoordinates I) (fun _ _ hi => hi) _ t ht
    intro i hi
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
    exact (hw u hu).2.1
  · apply coordinateTokens_valid Token.z I.size (zCoordinates I) (fun _ _ hi => hi) _ t ht
    intro i hi
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
    exact (hw u hu).2.2

theorem rawInstance_wellFormed (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I)
    (hn : 0 < I.size) (selected : List Triple) (hm : Matches I selected) :
    Packing.WellFormed (rawInstance I) := by
  refine ⟨?_, ?_, ?_⟩
  · change 0 < NumericPacking.capacity I.size
    have ho := offset_pos I.size
    dsimp [NumericPacking.capacity]
    omega
  · change 0 < I.triples.length
    have hl := matches_length hm
    have hs := hm.1.length_le
    omega
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact lt_of_lt_of_le (offset_pos I.size) (t.value_bounds I.size (tokens_valid I hw t ht)).1

theorem exact_total {I : Packing.Instance} {ps : List (List ℕ)} (hp : Packing.Exact I ps) :
    I.sizes.sum = I.capacity * I.bins := by
  have hs : ps.flatten.sum = I.capacity * ps.length := by
    have hload := hp.2.2
    clear hp
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have hh := hload p (by simp)
      have ht := ih (fun q hq => hload q (by simp [hq]))
      simp only [List.flatten_cons, List.sum_append, List.length_cons]
      nlinarith
  rw [← hp.2.1.sum_eq, hp.1] at hs
  exact hs

/-- The forward matching-to-bin-packing implication, including positivity and
the exact total-load requirement used by MODIFIED BIN PACKING. -/
theorem saturated_of_matching (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I)
    (hn : 0 < I.size) (selected : List Triple) (hm : Matches I selected) :
    Packing.SaturatedBinAccepts (rawInstance I) := by
  obtain ⟨ps, hp⟩ := exists_exact_of_matches I hw selected hm
  exact ⟨⟨rawInstance_wellFormed I hw hn selected hm, ps, Packing.exact_fits hp⟩, exact_total hp⟩

end ProteinFolding.MatchingPacking

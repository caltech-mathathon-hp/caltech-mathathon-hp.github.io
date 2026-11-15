import ProteinFolding.Cubic.Proofs.MatchingPacking
import ProteinFolding.Common.NumericPackingClassification

/-! Recovering a three-dimensional matching from arbitrary exact numerical
bins. Numerical partition witnesses are first lifted to token occurrences;
no injectivity assumption on token values is needed for this step. -/

namespace ProteinFolding.MatchingPacking

open ThreeDimensionalMatching NumericPacking

theorem lift_map_perm {A B : Type} (f : A → B) (xs : List A) (ys : List B)
    (h : (xs.map f).Perm ys) : ∃ zs, xs.Perm zs ∧ zs.map f = ys := by
  have hr : Relation.Comp (fun w z => w = z.map f) List.Perm ys xs := by
    rw [List.eq_map_comp_perm f]
    exact h.symm
  obtain ⟨zs, hmap, hperm⟩ := hr
  exact ⟨zs, hperm.symm, hmap.symm⟩

theorem split_map_groups {A B : Type} (f : A → B) (ps : List (List B)) (xs : List A)
    (h : xs.map f = ps.flatten) :
    ∃ qs : List (List A), qs.map (List.map f) = ps ∧ qs.flatten = xs := by
  induction ps generalizing xs with
  | nil =>
    have hx : xs = [] := by
      have hl := congrArg List.length h
      simpa using hl
    subst xs
    exact ⟨[], rfl, rfl⟩
  | cons p ps ih =>
    have htake : (xs.take p.length).map f = p := by
      rw [List.map_take, h]
      exact List.take_left
    have hdrop : (xs.drop p.length).map f = ps.flatten := by
      rw [List.map_drop, h]
      exact List.drop_left
    obtain ⟨qs, hmap, hflat⟩ := ih (xs.drop p.length) hdrop
    refine ⟨xs.take p.length :: qs, by simp [htake, hmap], ?_⟩
    simpa only [List.flatten_cons, hflat] using List.take_append_drop p.length xs

theorem lift_exact_parts (I : ThreeDimensionalMatching.Instance) (ps : List (List ℕ))
    (hp : Packing.Exact (rawInstance I) ps) :
    ∃ qs : List (List Token), (tokens I).Perm qs.flatten ∧
      ∀ q ∈ qs, (q.map (Token.value I.size)).sum = NumericPacking.capacity I.size := by
  obtain ⟨xs, hperm, hmap⟩ := lift_map_perm (Token.value I.size) (tokens I) ps.flatten hp.2.1
  obtain ⟨qs, hqs, hflat⟩ := split_map_groups (Token.value I.size) ps xs hmap
  refine ⟨qs, hflat ▸ hperm, ?_⟩
  intro q hq
  apply hp.2.2 (q.map (Token.value I.size))
  rw [← hqs]
  exact List.mem_map.mpr ⟨q, hq, rfl⟩

def readSelector : Token → Option Triple
  | .triple i j k => some (i, j, k)
  | _ => none

def readRealX : Token → Option ℕ
  | .x i true => some i
  | _ => none

def readRealY : Token → Option ℕ
  | .y i true => some i
  | _ => none

def readRealZ : Token → Option ℕ
  | .z i true => some i
  | _ => none

@[simp] theorem filterMap_none {A B : Type} (xs : List A) :
    xs.filterMap (fun _ => (none : Option B)) = [] := by
  induction xs <;> simp [*]

theorem readSelector_tokens (I : ThreeDimensionalMatching.Instance) :
    (tokens I).filterMap readSelector = I.triples := by
  simp [tokens, selectorToken, coordinateTokens, List.filterMap_append,
    List.filterMap_map, Function.comp_def, readSelector]

theorem readRealX_tokens (I : ThreeDimensionalMatching.Instance) :
    (tokens I).filterMap readRealX = List.range I.size := by
  simp [tokens, selectorToken, coordinateTokens, List.filterMap_append,
    List.filterMap_map, Function.comp_def, readRealX]

theorem readRealY_tokens (I : ThreeDimensionalMatching.Instance) :
    (tokens I).filterMap readRealY = List.range I.size := by
  simp [tokens, selectorToken, coordinateTokens, List.filterMap_append,
    List.filterMap_map, Function.comp_def, readRealY]

theorem readRealZ_tokens (I : ThreeDimensionalMatching.Instance) :
    (tokens I).filterMap readRealZ = List.range I.size := by
  simp [tokens, selectorToken, coordinateTokens, List.filterMap_append,
    List.filterMap_map, Function.comp_def, readRealZ]

def chosen (qs : List (Bool × Triple)) : List Triple :=
  qs.filterMap (fun rt => if rt.1 then some rt.2 else none)

def flattenQuadruples (qs : List (Bool × Triple)) : List Token :=
  qs.flatMap (fun rt => quadruple rt.1 rt.2)

theorem readSelector_quadruples (qs : List (Bool × Triple)) :
    (flattenQuadruples qs).filterMap readSelector = qs.map Prod.snd := by
  induction qs with
  | nil => rfl
  | cons rt qs ih =>
    simp [flattenQuadruples, quadruple, selectorToken, readSelector] at ih ⊢
    exact ih

theorem readRealX_quadruples (qs : List (Bool × Triple)) :
    (flattenQuadruples qs).filterMap readRealX = (chosen qs).map Prod.fst := by
  induction qs with
  | nil => rfl
  | cons rt qs ih =>
    obtain ⟨r, t⟩ := rt
    cases r <;> simp [flattenQuadruples, quadruple, selectorToken, readRealX, chosen] at ih ⊢ <;> exact ih

theorem readRealY_quadruples (qs : List (Bool × Triple)) :
    (flattenQuadruples qs).filterMap readRealY = (chosen qs).map (fun t => t.2.1) := by
  induction qs with
  | nil => rfl
  | cons rt qs ih =>
    obtain ⟨r, t⟩ := rt
    cases r <;> simp [flattenQuadruples, quadruple, selectorToken, readRealY, chosen] at ih ⊢ <;> exact ih

theorem readRealZ_quadruples (qs : List (Bool × Triple)) :
    (flattenQuadruples qs).filterMap readRealZ = (chosen qs).map (fun t => t.2.2) := by
  induction qs with
  | nil => rfl
  | cons rt qs ih =>
    obtain ⟨r, t⟩ := rt
    cases r <;> simp [flattenQuadruples, quadruple, selectorToken, readRealZ, chosen] at ih ⊢ <;> exact ih

theorem chosen_sublist (qs : List (Bool × Triple)) : (chosen qs).Sublist (qs.map Prod.snd) := by
  induction qs with
  | nil => exact List.Sublist.refl _
  | cons rt qs ih =>
    obtain ⟨r, t⟩ := rt
    cases r
    · simpa [chosen] using ih.cons t
    · simpa [chosen] using ih.cons₂ t

theorem matches_of_quadruple_partition (I : ThreeDimensionalMatching.Instance)
    (qs : List (Bool × Triple)) (hp : (tokens I).Perm (flattenQuadruples qs)) :
    Matches I (chosen qs) := by
  have hs := hp.filterMap readSelector
  have hx := hp.filterMap readRealX
  have hy := hp.filterMap readRealY
  have hz := hp.filterMap readRealZ
  rw [readSelector_tokens, readSelector_quadruples] at hs
  rw [readRealX_tokens, readRealX_quadruples] at hx
  rw [readRealY_tokens, readRealY_quadruples] at hy
  rw [readRealZ_tokens, readRealZ_quadruples] at hz
  exact ⟨(chosen_sublist qs).subperm.trans hs.symm.subperm, hx.symm, hy.symm, hz.symm⟩

theorem classify_exact_parts (n : ℕ) (ps : List (List Token))
    (hv : ∀ p ∈ ps, ∀ t ∈ p, t.Valid n)
    (hs : ∀ p ∈ ps, (p.map (Token.value n)).sum = NumericPacking.capacity n) :
    ∃ qs : List (Bool × Triple), ps.flatten.Perm (flattenQuadruples qs) := by
  induction ps with
  | nil => exact ⟨[], List.Perm.refl _⟩
  | cons p ps ih =>
    obtain ⟨i, j, k, r, hp⟩ := exact_bin_quadruple n p
      (hv p (by simp)) (hs p (by simp))
    obtain ⟨qs, hqs⟩ := ih (fun q hq => hv q (by simp [hq]))
      (fun q hq => hs q (by simp [hq]))
    refine ⟨(r, (i, j, k)) :: qs, ?_⟩
    simpa only [List.flatten_cons, flattenQuadruples, List.flatMap_cons,
      quadruple, selectorToken] using hp.append hqs

/-- Arbitrary exact numerical bins yield a matching covering every coordinate
exactly once. Neither type restrictions nor four-item restrictions are imposed
on the supplied packing witness; the numerical gadget derives them. -/
theorem exists_matching_of_exact (I : ThreeDimensionalMatching.Instance)
    (hw : WellFormed I) (ps : List (List ℕ)) (hp : Packing.Exact (rawInstance I) ps) :
    ∃ selected, Matches I selected := by
  obtain ⟨ts, htperm, htsum⟩ := lift_exact_parts I ps hp
  have hv : ∀ p ∈ ts, ∀ t ∈ p, t.Valid I.size := by
    intro p hpt t ht
    exact tokens_valid I hw t (htperm.mem_iff.mpr (List.mem_flatten.mpr ⟨p, hpt, ht⟩))
  obtain ⟨qs, hqperm⟩ := classify_exact_parts I.size ts hv htsum
  exact ⟨chosen qs, matches_of_quadruple_partition I qs (htperm.trans hqperm)⟩

theorem accepts_of_exact (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I)
    (ps : List (List ℕ)) (hp : Packing.Exact (rawInstance I) ps) : Accepts I :=
  ⟨hw, exists_matching_of_exact I hw ps hp⟩

theorem accepts_of_saturated (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I)
    (hp : Packing.SaturatedBinAccepts (rawInstance I)) : Accepts I := by
  obtain ⟨⟨_, ps, hfit⟩, htotal⟩ := hp
  exact accepts_of_exact I hw ps (Packing.exact_of_fits_of_total hfit htotal)

theorem exact_iff_accepts (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I) :
    (∃ ps, Packing.Exact (rawInstance I) ps) ↔ Accepts I := by
  constructor
  · rintro ⟨ps, hp⟩
    exact accepts_of_exact I hw ps hp
  · rintro ⟨_, selected, hm⟩
    exact exists_exact_of_matches I hw selected hm

theorem saturated_iff_accepts (I : ThreeDimensionalMatching.Instance) (hw : WellFormed I)
    (hn : 0 < I.size) : Packing.SaturatedBinAccepts (rawInstance I) ↔ Accepts I := by
  constructor
  · exact accepts_of_saturated I hw
  · rintro ⟨_, selected, hm⟩
    exact saturated_of_matching I hw hn selected hm

end ProteinFolding.MatchingPacking

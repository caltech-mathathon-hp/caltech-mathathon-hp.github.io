import ProteinFolding.Tetrahedral.SiteProfileEquality

/-! Extraction of a central square layer from an extremal run profile. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

theorem canonicalSquare_parts_init (n : ℕ) :
    ∃ q : List ℕ, (canonicalSquare n).parts = q ++ [n + 1] := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ n =>
    exact ⟨(canonicalSquare n).parts ++ [n + 1], rfl⟩

theorem rawPrefix_of_sorted_split (A : Finset ℤ) (β : ℤ → ℕ)
    (left right : List ℤ) (b : ℤ)
    (hset : (left ++ b :: right).toFinset = A)
    (hsorted : (left ++ b :: right).Pairwise (fun i j => i < j)) :
    rawPrefix A β b = (left.map β).sum := by
  have hs := List.pairwise_append.mp hsorted
  have hright := List.pairwise_cons.mp hs.2.1
  have hfilter : A.filter (fun j => j < b) = left.toFinset := by
    ext j
    simp only [Finset.mem_filter, List.mem_toFinset]
    have hmem : j ∈ A ↔ j ∈ left ∨ j = b ∨ j ∈ right := by
      rw [← hset]
      simp only [List.mem_toFinset, List.mem_append, List.mem_cons]
    rw [hmem]
    constructor
    · rintro ⟨hj | (hj | hj), hjlt⟩
      · exact hj
      · omega
      · have hbj := hright.1 j hj
        omega
    · intro hj
      exact ⟨Or.inl hj, hs.2.2 j hj b (by simp)⟩
  have hnodup : left.Nodup := hs.1.imp (fun h => ne_of_lt h)
  unfold rawPrefix
  rw [hfilter, List.sum_toFinset β hnodup]

theorem rawKeysConvex_consecutive (A : Finset ℤ) (pre post : List ℤ) (a b : ℤ)
    (hset : (pre ++ a :: b :: post).toFinset = A)
    (hsorted : (pre ++ a :: b :: post).Pairwise (fun i j => i < j))
    (hconv : RawKeysConvex A) : b = a + 1 := by
  have hs := List.pairwise_append.mp hsorted
  have htail := List.pairwise_cons.mp hs.2.1
  have htail' := List.pairwise_cons.mp htail.2
  have hab : a < b := htail.1 b (by simp)
  have ha : a ∈ A := by rw [← hset]; simp
  have hb : b ∈ A := by rw [← hset]; simp
  have hmiddle := hconv a ha b hb (a + 1) (by omega) (by omega)
  have hmem : a + 1 ∈ pre ∨ a + 1 = a ∨ a + 1 = b ∨ a + 1 ∈ post := by
    have h := hmiddle
    rw [← hset] at h
    simpa only [List.mem_toFinset, List.mem_append, List.mem_cons] using h
  rcases hmem with hp | heq | heq | hp
  · have hlt := hs.2.2 (a + 1) hp a (by simp)
    omega
  · omega
  · omega
  · have hlt := htail'.1 (a + 1) hp
    omega

/-- The central layer of an extremal site set has two adjacent run counts m,
and exactly m² sites. Its prefix run mass is also m². -/
theorem site_extremal_central_layer (S : Finset Site) (hne : S.Nonempty) (m : ℕ)
    (hm : 0 < m) (hcard : S.card = octahedralNumber m)
    (hRuns : totalRuns S = 2 * m ^ 2) :
    ∃ k : ℤ, k ∈ activeLayers S ∧ gapRunCount S (k - 1) = m ∧
      gapRunCount S k = m ∧ runsBefore S k = m ^ 2 ∧
      (finiteLayer S k).card = m ^ 2 := by
  obtain ⟨keys, hset, hsorted, hmap, hconv⟩ :=
    site_profile_canonical_run_list S hne m hm hcard hRuns
  obtain ⟨q, hq⟩ := canonicalSquare_parts_init (m - 1)
  have hindex : m - 1 + 1 = m := by omega
  rw [hindex] at hq
  have hmap' : keys.map (gapRunCount S) = q ++ (m :: m :: q.reverse) := by
    rw [hmap, hq]
    simp [List.reverse_append, List.append_assoc]
  obtain ⟨pre, rest, hkeys, hpre, hrest⟩ := List.map_eq_append_iff.mp hmap'
  cases rest with
  | nil => simp at hrest
  | cons a tail =>
    cases tail with
    | nil => simp at hrest
    | cons b post =>
      have hrest' : gapRunCount S a = m ∧ gapRunCount S b = m ∧
          post.map (gapRunCount S) = q.reverse := by
        simpa only [List.map_cons, List.cons.injEq] using hrest
      have hset' : (pre ++ a :: b :: post).toFinset = activeGaps S := by
        rw [← hkeys]
        exact hset
      have hsorted' : (pre ++ a :: b :: post).Pairwise (fun i j => i < j) := by
        rw [← hkeys]
        exact hsorted
      have hab := rawKeysConvex_consecutive (activeGaps S) pre post a b hset' hsorted' hconv
      have ha : a = b - 1 := by omega
      have hbmem : b ∈ activeGaps S := by rw [← hset']; simp
      have hamem : b - 1 ∈ activeGaps S := by rw [← ha, ← hset']; simp
      have hnonempty := site_internal_layer_nonempty S hne m hm hcard hRuns b hbmem hamem
      have hactive : b ∈ activeLayers S := by
        obtain ⟨p, hp⟩ := hnonempty
        have h := Finset.mem_filter.mp hp
        exact Finset.mem_image.mpr ⟨p, h.1, h.2⟩
      have hbefore : runsBefore S b = m ^ 2 := by
        have hprefix := rawPrefix_of_sorted_split (activeGaps S) (gapRunCount S)
          (pre ++ [a]) post b (by simpa only [List.append_assoc, List.singleton_append] using hset')
          (by simpa only [List.append_assoc, List.singleton_append] using hsorted')
        have hmass := PositiveComposition.parts_sum (canonicalSquare (m - 1))
        rw [canonicalSquare_mass, hindex, hq] at hmass
        change runsBefore S b = _ at hprefix
        have hprefix' : runsBefore S b = (q ++ [m]).sum := by
          simpa only [List.map_append, List.map_singleton, hpre, hrest'.1] using hprefix
        exact hprefix'.trans hmass
      have htight := site_layer_relaxation_tight S hne m hm hcard hRuns b hactive
      have hprod : m * m = m ^ 2 := by ring
      rw [← ha, hrest'.1, hrest'.2.1, hbefore, hRuns, hprod] at htight
      have hroom : 2 * m ^ 2 - m ^ 2 = m ^ 2 := by omega
      rw [hroom, min_self, min_self] at htight
      exact ⟨b, hactive, by rw [← ha]; exact hrest'.1, hrest'.2.1, hbefore, htight⟩

end ProteinFolding.Tetrahedral

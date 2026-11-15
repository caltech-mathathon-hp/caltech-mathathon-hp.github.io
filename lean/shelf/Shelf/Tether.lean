import Shelf.Anatomy

/-!
# Isolated `H`'s, tethers and dense runs

Lemmas 5 to 8 of our write-up (Sections 2.2 and 2.3): the clamp map, isolated `H`'s
lie on the skeleton, the Tether Lemma, and the `H`'s of a dense run form a simple
path on the skeleton.
-/

namespace ProteinFolding.Shelf

open ProteinFolding ProteinFolding.CubicPackingGeometry Residue

/-- The map `t ↦ max 0 (min t (n - 1))` does not increase distances in `ℤ`. -/
theorem natAbs_clamp_le (n : ℕ) (t t' : ℤ) :
    (max 0 (min t ((n : ℤ) - 1)) - max 0 (min t' ((n : ℤ) - 1))).natAbs ≤ (t - t').natAbs := by
  omega

/-- Lemma 5(a): the clamp map does not increase distances. -/
theorem latticeDistance_clamp_le (n : ℕ) (w w' : Site) :
    latticeDistance (clamp n w) (clamp n w') ≤ latticeDistance w w' := by
  simp only [latticeDistance_eq, clamp]
  have h0 := natAbs_clamp_le n (w 0) (w' 0)
  have h1 := natAbs_clamp_le n (w 1) (w' 1)
  have h2 := natAbs_clamp_le n (w 2) (w' 2)
  omega

/-- Lemma 5(b): a site outside the cube that is adjacent to a point `u` of the cube is clamped to `u`. -/
theorem clamp_eq_of_adj {n : ℕ} {u w : Site} (hu : u ∈ Q n) (hw : w ∉ Q n)
    (h : cubicLattice.Adj u w) : clamp n w = u := by
  rw [adj_iff, latticeDistance_eq] at h
  rw [mem_Q] at hu hw
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  have hw' : ¬ ((0 ≤ w 0 ∧ w 0 < n) ∧ (0 ≤ w 1 ∧ w 1 < n) ∧ (0 ≤ w 2 ∧ w 2 < n)) := by
    rintro ⟨a, b, c⟩
    exact hw (fun k => by fin_cases k <;> assumption)
  funext k
  fin_cases k <;> simp only [clamp] <;> simp <;> omega

/-- A letter that exists has an index below the length. -/
theorem lt_length_of_getElem? {S : Sequence} {i : ℕ} {x : Residue} (h : S[i]? = some x) :
    i < S.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- Different letters sit on different sites. -/
theorem site_ne {N : ℕ} (f : Fold cubicLattice N) {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : i ≠ j) : site f i ≠ site f j :=
  fun he => h (site_inj f hi hj he)

/-- Two sites at distance `0` are equal. -/
theorem eq_of_latticeDistance_eq_zero {x y : Site} (h : latticeDistance x y = 0) : x = y := by
  rw [latticeDistance_eq] at h
  funext k
  fin_cases k <;> simp <;> omega

variable {S : Sequence} {f : Fold cubicLattice S.length} {n : ℕ}

/-- Lemma 6: an isolated `H` sits on the skeleton. -/
theorem Isolated.on_skeleton (hf : Fills S f n) {i : ℕ} (hi : Isolated S i) :
    EdgeSkeleton 0 n (site f i) := by
  obtain ⟨h1, hP, hH, hP'⟩ := hi
  obtain ⟨ha, ha'⟩ := List.getElem?_eq_some_iff.mp hP
  obtain ⟨hb, hb'⟩ := List.getElem?_eq_some_iff.mp hH
  obtain ⟨hc, hc'⟩ := List.getElem?_eq_some_iff.mp hP'
  rw [site_eq f hb]
  exact php_on_edge f 0 n hf ⟨i - 1, ha⟩ ⟨i, hb⟩ ⟨i + 1, hc⟩ (by simp; omega) rfl ha' hb' hc'

/-- Lemma 7 (Tether Lemma): if letters `i < j` are `H`'s and all `g = j - i - 1 ≥ 1` letters
between them are `P`'s, then the two sites are at distance at most `g - 1`. -/
theorem tether (hf : Fills S f n) {i j : ℕ} (hij : i + 1 < j)
    (hi : S[i]? = some H) (hj : S[j]? = some H)
    (hP : ∀ t, i < t → t < j → S[t]? = some P) :
    latticeDistance (site f i) (site f j) + 2 ≤ j - i := by
  have hjl := lt_length_of_getElem? hj
  have hA : clamp n (site f (i + 1)) = site f i :=
    clamp_eq_of_adj (hf.site_mem hi) (hf.site_not_mem (hP _ (by omega) hij))
      (site_adj f (by omega))
  have hB : clamp n (site f (j - 1)) = site f j := by
    have hadj := site_adj f (i := j - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hadj
    exact clamp_eq_of_adj (hf.site_mem hj) (hf.site_not_mem (hP _ (by omega) (by omega)))
      hadj.symm
  have hwalk := latticeDistance_site_le f (i := i + 1) (j := j - 1) (by omega) (by omega)
  have hcl := latticeDistance_clamp_le n (site f (i + 1)) (site f (j - 1))
  rw [hA, hB] at hcl
  omega

/-- The case `g = 2` of the Tether Lemma: in `H P P H` the two `H`'s are adjacent. -/
theorem adj_of_HPPH (hf : Fills S f n) {i : ℕ} (h0 : S[i]? = some H) (h1 : S[i + 1]? = some P)
    (h2 : S[i + 2]? = some P) (h3 : S[i + 3]? = some H) :
    cubicLattice.Adj (site f i) (site f (i + 3)) := by
  have ht := tether hf (i := i) (j := i + 3) (by omega) h0 h3 (by
    intro t ht1 ht2
    rcases (show t = i + 1 ∨ t = i + 2 by omega) with rfl | rfl
    · exact h1
    · exact h2)
  have hne := site_ne f (lt_length_of_getElem? h0) (lt_length_of_getElem? h3)
    (show i ≠ i + 3 by omega)
  rw [adj_iff]
  have : latticeDistance (site f i) (site f (i + 3)) ≠ 0 :=
    fun h => hne (eq_of_latticeDistance_eq_zero h)
  omega

theorem runSites_length {N : ℕ} (f : Fold cubicLattice N) (o r : ℕ) :
    (runSites f o r).length = r := by
  simp [runSites]

theorem mem_runSites {N : ℕ} {f : Fold cubicLattice N} {o r : ℕ} {p : Site} :
    p ∈ runSites f o r ↔ ∃ t, t < r ∧ site f (o + 3 * t) = p := by
  simp [runSites]

theorem getElem?_runSites {N : ℕ} (f : Fold cubicLattice N) (o r : ℕ) {t : ℕ} (ht : t < r) :
    (runSites f o r)[t]? = some (site f (o + 3 * t)) := by
  simp [runSites, ht]

/-- Lemma 8, first part: the `H`'s of a dense run sit on different sites. -/
theorem RunAt.nodup (f : Fold cubicLattice S.length) {o r : ℕ} (h : RunAt S o r) :
    (runSites f o r).Nodup := by
  unfold runSites
  refine List.Nodup.map_on ?_ List.nodup_range
  intro a ha b hb hab
  rw [List.mem_range] at ha hb
  have := site_inj f (lt_length_of_getElem? (h a ha).2.2.1)
    (lt_length_of_getElem? (h b hb).2.2.1) hab
  omega

/-- Lemma 8: consecutive `H`'s of a dense run are adjacent. -/
theorem RunAt.adj (hf : Fills S f n) {o r : ℕ} (h : RunAt S o r) {t : ℕ} (ht : t + 1 < r) :
    cubicLattice.Adj (site f (o + 3 * t)) (site f (o + 3 * (t + 1))) := by
  obtain ⟨-, -, hH, hP⟩ := h t (by omega)
  obtain ⟨-, hP', hH', -⟩ := h (t + 1) ht
  have e1 : o + 3 * (t + 1) - 1 = o + 3 * t + 2 := by omega
  have e2 : o + 3 * (t + 1) = o + 3 * t + 3 := by omega
  rw [e1] at hP'
  rw [e2] at hH' ⊢
  exact adj_of_HPPH hf hH hP hP' hH'

/-- Lemma 8: the `H`'s of a dense run, in their order, form a walk. -/
theorem RunAt.isChain (hf : Fills S f n) {o r : ℕ} (h : RunAt S o r) :
    (runSites f o r).IsChain cubicLattice.Adj := by
  unfold runSites
  rw [List.isChain_map, List.isChain_range]
  intro m hm
  exact h.adj hf (by omega)

/-- Lemma 8: the `H`'s of a dense run sit on the skeleton. -/
theorem RunAt.on_skeleton (hf : Fills S f n) {o r : ℕ} (h : RunAt S o r) :
    ∀ p ∈ runSites f o r, EdgeSkeleton 0 n p := by
  intro p hp
  obtain ⟨t, ht, rfl⟩ := mem_runSites.mp hp
  exact (h t ht).on_skeleton hf

end ProteinFolding.Shelf

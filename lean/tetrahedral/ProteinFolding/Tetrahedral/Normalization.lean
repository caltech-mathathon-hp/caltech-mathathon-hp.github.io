import ProteinFolding.Tetrahedral.Layers

/-!
# Normalizing tetrahedral folds

Translations by A-sites preserve both sublattices. Reflection about half a
B-site exchanges them. Either operation preserves the graph and the H-H score;
together they normalize an arbitrary first site to the origin.
-/

namespace ProteinFolding.Tetrahedral

theorem sub_A_A {p a : Coordinates} (hp : InASublattice p) (ha : InASublattice a) :
    InASublattice (fun k => p k - a k) := by
  constructor
  · intro k
    change (p k - a k) % 2 = 0
    rw [Int.sub_emod, hp.1 k, ha.1 k]
    decide
  · change coordinateSum (fun k => p k - a k) % 4 = 0
    rw [coordinateSum_sub, Int.sub_emod, hp.2, ha.2]
    decide

theorem sub_B_A {p a : Coordinates} (hp : InBSublattice p) (ha : InASublattice a) :
    InBSublattice (fun k => p k - a k) := by
  constructor
  · intro k
    change (p k - a k) % 2 = 1
    rw [Int.sub_emod, hp.1 k, ha.1 k]
    decide
  · change coordinateSum (fun k => p k - a k) % 4 = 3
    rw [coordinateSum_sub, Int.sub_emod, hp.2, ha.2]
    decide

theorem sub_B_B {p a : Coordinates} (hp : InBSublattice p) (ha : InBSublattice a) :
    InASublattice (fun k => p k - a k) := by
  constructor
  · intro k
    change (p k - a k) % 2 = 0
    rw [Int.sub_emod, hp.1 k, ha.1 k]
    decide
  · change coordinateSum (fun k => p k - a k) % 4 = 0
    rw [coordinateSum_sub, Int.sub_emod, hp.2, ha.2]
    decide

def origin : Site := ⟨![0, 0, 0], by decide⟩

@[simp] theorem origin_val (k : Fin 3) : origin.val k = 0 := by fin_cases k <;> rfl

def shiftSite (a : Site) (ha : InASublattice a.val) (p : Site) : Site :=
  ⟨fun k => p.val k - a.val k, p.property.elim
    (fun hp => Or.inl (sub_A_A hp ha)) (fun hp => Or.inr (sub_B_A hp ha))⟩

def reflectSite (a : Site) (ha : InBSublattice a.val) (p : Site) : Site :=
  ⟨fun k => a.val k - p.val k, p.property.elim
    (fun hp => Or.inr (sub_B_A ha hp)) (fun hp => Or.inl (sub_B_B ha hp))⟩

theorem shiftSite_injective (a : Site) (ha : InASublattice a.val) :
    Function.Injective (shiftSite a ha) := by
  intro p q h
  apply Subtype.ext
  funext k
  have hk := congrArg (fun r : Site => r.val k) h
  change p.val k - a.val k = q.val k - a.val k at hk
  omega

theorem reflectSite_injective (a : Site) (ha : InBSublattice a.val) :
    Function.Injective (reflectSite a ha) := by
  intro p q h
  apply Subtype.ext
  funext k
  have hk := congrArg (fun r : Site => r.val k) h
  change a.val k - p.val k = a.val k - q.val k at hk
  omega

theorem directedBond_shift {p q : Site} (h : DirectedBond p q)
    (a : Site) (ha : InASublattice a.val) :
    DirectedBond (shiftSite a ha p) (shiftSite a ha q) := by
  refine ⟨sub_A_A h.1 ha, sub_B_A h.2.1 ha, ?_⟩
  obtain ⟨d, hd⟩ := h.2.2
  refine ⟨d, ?_⟩
  intro k
  change q.val k - a.val k = p.val k - a.val k + bondVector d k
  have hk := hd k
  omega

theorem directedBond_reflect {p q : Site} (h : DirectedBond p q)
    (a : Site) (ha : InBSublattice a.val) :
    DirectedBond (reflectSite a ha q) (reflectSite a ha p) := by
  refine ⟨sub_B_B ha h.2.1, sub_B_A ha h.1, ?_⟩
  obtain ⟨d, hd⟩ := h.2.2
  refine ⟨d, ?_⟩
  intro k
  change a.val k - p.val k = a.val k - q.val k + bondVector d k
  have hk := hd k
  omega

theorem adj_shift_iff (a : Site) (ha : InASublattice a.val) (p q : Site) :
    tetrahedralLattice.Adj (shiftSite a ha p) (shiftSite a ha q) ↔
      tetrahedralLattice.Adj p q := by
  constructor
  · intro h
    rcases h with h | h
    · apply Or.inl
      have hpA : InASublattice p.val := by
        rcases p.property with hp | hp
        · exact hp
        · exact False.elim (sublattices_disjoint _ h.1 (sub_B_A hp ha))
      have hqB : InBSublattice q.val := by
        rcases q.property with hq | hq
        · exact False.elim (sublattices_disjoint _ (sub_A_A hq ha) h.2.1)
        · exact hq
      obtain ⟨d, hd⟩ := h.2.2
      refine ⟨hpA, hqB, d, ?_⟩
      intro k
      have hk := hd k
      change q.val k - a.val k = p.val k - a.val k + bondVector d k at hk
      omega
    · apply Or.inr
      have hqA : InASublattice q.val := by
        rcases q.property with hq | hq
        · exact hq
        · exact False.elim (sublattices_disjoint _ h.1 (sub_B_A hq ha))
      have hpB : InBSublattice p.val := by
        rcases p.property with hp | hp
        · exact False.elim (sublattices_disjoint _ (sub_A_A hp ha) h.2.1)
        · exact hp
      obtain ⟨d, hd⟩ := h.2.2
      refine ⟨hqA, hpB, d, ?_⟩
      intro k
      have hk := hd k
      change p.val k - a.val k = q.val k - a.val k + bondVector d k at hk
      omega
  · intro h
    exact h.elim (fun h => Or.inl (directedBond_shift h a ha))
      (fun h => Or.inr (directedBond_shift h a ha))

@[simp] theorem reflectSite_involutive (a : Site) (ha : InBSublattice a.val) (p : Site) :
    reflectSite a ha (reflectSite a ha p) = p := by
  apply Subtype.ext
  funext k
  change a.val k - (a.val k - p.val k) = p.val k
  omega

theorem adj_reflect (a : Site) (ha : InBSublattice a.val) {p q : Site}
    (h : tetrahedralLattice.Adj p q) :
    tetrahedralLattice.Adj (reflectSite a ha p) (reflectSite a ha q) := by
  exact h.elim (fun h => Or.inr (directedBond_reflect h a ha))
    (fun h => Or.inl (directedBond_reflect h a ha))

theorem adj_reflect_iff (a : Site) (ha : InBSublattice a.val) (p q : Site) :
    tetrahedralLattice.Adj (reflectSite a ha p) (reflectSite a ha q) ↔
      tetrahedralLattice.Adj p q := by
  constructor
  · intro h
    simpa only [reflectSite_involutive] using adj_reflect a ha h
  · exact adj_reflect a ha

/-- A graph embedding that sends an arbitrary anchor to the origin. -/
def normalizeSite (a p : Site) : Site :=
  if h : InASublattice a.val then shiftSite a h p
  else reflectSite a ((inB_iff_not_inA a).mpr h) p

theorem normalizeSite_injective (a : Site) : Function.Injective (normalizeSite a) := by
  intro p q heq
  by_cases h : InASublattice a.val
  · apply shiftSite_injective a h
    simpa only [normalizeSite, dif_pos h] using heq
  · apply reflectSite_injective a ((inB_iff_not_inA a).mpr h)
    simpa only [normalizeSite, dif_neg h] using heq

theorem adj_normalizeSite_iff (a p q : Site) :
    tetrahedralLattice.Adj (normalizeSite a p) (normalizeSite a q) ↔
      tetrahedralLattice.Adj p q := by
  by_cases h : InASublattice a.val
  · simpa [normalizeSite, h] using adj_shift_iff a h p q
  · simpa [normalizeSite, h] using adj_reflect_iff a ((inB_iff_not_inA a).mpr h) p q

@[simp] theorem normalizeSite_self (a : Site) : normalizeSite a a = origin := by
  apply Subtype.ext
  funext k
  by_cases h : InASublattice a.val <;> simp [normalizeSite, shiftSite, reflectSite, h]

def normalizeFold {n : ℕ} (f : Fold tetrahedralLattice n) (a : Site) :
    Fold tetrahedralLattice n where
  pos i := normalizeSite a (f.pos i)
  injective_pos := (normalizeSite_injective a).comp f.injective_pos
  consecutive i j h := (adj_normalizeSite_iff a _ _).mpr (f.consecutive i j h)

theorem hhBonds_normalize (S : Sequence) (f : Fold tetrahedralLattice S.length) (a : Site) :
    hhBonds S (normalizeFold f a) = hhBonds S f := by
  ext ij
  simp only [hhBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    normalizeFold, adj_normalizeSite_iff]

theorem bondCount_normalize (S : Sequence) (f : Fold tetrahedralLattice S.length) (a : Site) :
    bondCount S (normalizeFold f a) = bondCount S f := by
  unfold bondCount
  rw [hhBonds_normalize]

def IsNormalized {n : ℕ} (f : Fold tetrahedralLattice n) : Prop :=
  ∀ i : Fin n, i.val = 0 → f.pos i = origin

def normalizedFold {n : ℕ} (f : Fold tetrahedralLattice n) : Fold tetrahedralLattice n :=
  if h : 0 < n then normalizeFold f (f.pos ⟨0, h⟩) else f

theorem normalizedFold_normalized {n : ℕ} (f : Fold tetrahedralLattice n) :
    IsNormalized (normalizedFold f) := by
  intro i hi
  by_cases hn : 0 < n
  · have he : i = (⟨0, hn⟩ : Fin n) := Fin.ext hi
    subst i
    simp [normalizedFold, hn, normalizeFold]
  · have hlt := i.isLt
    omega

theorem normalizedFold_bondCount (S : Sequence) (f : Fold tetrahedralLattice S.length) :
    bondCount S (normalizedFold f) = bondCount S f := by
  by_cases h : 0 < S.length
  · simpa only [normalizedFold, dif_pos h] using bondCount_normalize S f (f.pos ⟨0, h⟩)
  · simp only [normalizedFold, dif_neg h]

theorem normalized_coordinate_bounds {n : ℕ} (f : Fold tetrahedralLattice n)
    (hf : IsNormalized f) (i : Fin n) (k : Fin 3) :
    -(i.val : ℤ) ≤ (f.pos i).val k ∧ (f.pos i).val k ≤ (i.val : ℤ) := by
  have hbound : ∀ j (hj : j < n),
      -(j : ℤ) ≤ (f.pos ⟨j, hj⟩).val k ∧ (f.pos ⟨j, hj⟩).val k ≤ (j : ℤ) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [hf ⟨0, hj⟩ rfl, origin_val]
      simp
    | succ j ih =>
      intro hj
      have hj' : j < n := by omega
      have hb := ih hj'
      have hadj := f.consecutive ⟨j, hj'⟩ ⟨j + 1, hj⟩ rfl
      have hd := adj_coordinate hadj k
      change -(↑(j + 1) : ℤ) ≤ _ ∧ _ ≤ (↑(j + 1) : ℤ)
      omega
  exact hbound i.val i.isLt

theorem normalized_coordinate_natAbs_le {n : ℕ} (f : Fold tetrahedralLattice n)
    (hf : IsNormalized f) (i : Fin n) (k : Fin 3) :
    ((f.pos i).val k).natAbs ≤ i.val := by
  have h := normalized_coordinate_bounds f hf i k
  omega

/-- A normalized, coordinate-bounded witness with exactly the original H-H score. -/
theorem exists_normalized_bounded_fold (S : Sequence) (f : Fold tetrahedralLattice S.length) :
    ∃ g : Fold tetrahedralLattice S.length,
      IsNormalized g ∧ bondCount S g = bondCount S f ∧
        ∀ (i : Fin S.length) (k : Fin 3), ((g.pos i).val k).natAbs ≤ i.val := by
  refine ⟨normalizedFold f, normalizedFold_normalized f, normalizedFold_bondCount S f, ?_⟩
  exact normalized_coordinate_natAbs_le _ (normalizedFold_normalized f)

end ProteinFolding.Tetrahedral

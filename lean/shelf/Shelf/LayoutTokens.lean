import Shelf.Layout

/-!
# The tokens on the three free edges

The run `A` leaves three edges of the cube free: `(x, N, 0)`, `(x, 0, 0)` and
`(x, 0, N)`. Table 1 puts `F₁` on the first, the separators and the items on the
second (the shelf) and `F₂` on the third. This file checks the coordinates: every
token is valid, we know where each run starts and ends, and different tokens have
different centres.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue CubicPackingGeometry Layout

/-! ### Numbers -/

theorem side_even {J : Packing.Instance} (hJ : Normalised J) : Even (side J) := by
  obtain ⟨k, hk⟩ := hJ.bins_odd
  obtain ⟨c, hc⟩ := hJ.six_dvd_capacity
  unfold side
  rw [hk, hc]
  exact ⟨k * (6 * c + 1) + 3 * c + 2, by ring⟩

theorem ten_le_side {J : Packing.Instance} (hJ : Normalised J) : 10 ≤ side J := by
  obtain ⟨k, hk⟩ := hJ.bins_odd
  obtain ⟨c, hc⟩ := hJ.six_dvd_capacity
  have hc0 := hJ.capacity_pos
  unfold side
  have h1 : 1 ≤ J.bins := by omega
  have h2 : 7 ≤ J.capacity + 1 := by omega
  have := Nat.mul_le_mul h1 h2
  omega

theorem sizes_length_pos {J : Packing.Instance} (hJ : Normalised J) : 0 < J.sizes.length := by
  rcases Nat.eq_zero_or_pos J.sizes.length with h | h
  · have hnil : J.sizes = [] := List.eq_nil_of_length_eq_zero h
    have hs := hJ.sum_eq
    rw [hnil, List.sum_nil] at hs
    obtain ⟨k, hk⟩ := hJ.bins_odd
    have := hJ.capacity_pos
    have : 0 < J.capacity * J.bins := Nat.mul_pos this (by omega)
    omega
  · exact h

theorem item_pos {J : Packing.Instance} (hJ : Normalised J) (i : Fin J.sizes.length) :
    0 < J.sizes.get i := by
  exact hJ.size_pos _ (List.get_mem _ _)

theorem item_even {J : Packing.Instance} (hJ : Normalised J) (i : Fin J.sizes.length) :
    Even (J.sizes.get i) := by
  have h := hJ.six_dvd_size _ (List.get_mem J.sizes i)
  exact even_iff_two_dvd.mpr (Nat.dvd_trans ⟨3, rfl⟩ h)

theorem N_eq (J : Packing.Instance) :
    N J = (J.bins : ℤ) * ((J.capacity : ℤ) + 1) + 2 := by
  unfold N side
  push_cast
  ring

theorem sepCol_zero (J : Packing.Instance) : sepCol J 0 = 1 := by
  simp [sepCol]

theorem sepCol_succ (J : Packing.Instance) (j : ℕ) :
    sepCol J (j + 1) = sepCol J j + ((J.capacity : ℤ) + 1) := by
  unfold sepCol
  push_cast
  ring

/-- The last separator is at the far end of the shelf. -/
theorem sepCol_bins (J : Packing.Instance) : sepCol J J.bins = N J - 1 := by
  rw [N_eq]
  unfold sepCol
  ring

theorem sepCol_lt (J : Packing.Instance) {j j' : ℕ} (h : j < j') : sepCol J j < sepCol J j' := by
  unfold sepCol
  have h1 : (j : ℤ) < j' := by exact_mod_cast h
  have h2 : (0 : ℤ) ≤ J.capacity := by positivity
  nlinarith

theorem sepCol_mono (J : Packing.Instance) {j j' : ℕ} (h : j ≤ j') :
    sepCol J j ≤ sepCol J j' := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (sepCol_lt J h)
  · exact le_rfl

theorem sepCol_range (J : Packing.Instance) {j : ℕ} (hj : j ≤ J.bins) :
    1 ≤ sepCol J j ∧ sepCol J j ≤ N J - 1 := by
  refine ⟨?_, ?_⟩
  · unfold sepCol
    have : (0 : ℤ) ≤ (j : ℤ) * ((J.capacity : ℤ) + 1) := by positivity
    linarith
  · rw [← sepCol_bins]
    exact sepCol_mono J hj

/-! ### The columns of the items -/

/-- An item lies on inner nodes of the shelf, away from its two ends. -/
theorem lo_range {J : Packing.Instance} {lo : Fin J.sizes.length → ℕ} (hlo : Placed J lo)
    (i : Fin J.sizes.length) :
    2 ≤ lo i ∧ (lo i : ℤ) + (J.sizes.get i : ℤ) ≤ N J - 1 := by
  obtain ⟨b, hb, h1, h2⟩ := hlo.bin i
  refine ⟨by omega, ?_⟩
  have h3 : (b + 1) * (J.capacity + 1) ≤ J.bins * (J.capacity + 1) :=
    Nat.mul_le_mul_right _ hb
  rw [add_mul, one_mul] at h3
  have h4 : lo i + J.sizes.get i ≤ J.bins * (J.capacity + 1) + 1 := by omega
  have h5 : ((lo i + J.sizes.get i : ℕ) : ℤ) ≤ ((J.bins * (J.capacity + 1) + 1 : ℕ) : ℤ) := by
    exact_mod_cast h4
  push_cast at h5
  rw [N_eq]
  linarith

/-- No column of an item is the column of a separator. -/
theorem col_ne_sepCol {J : Packing.Instance} {lo : Fin J.sizes.length → ℕ} (hlo : Placed J lo)
    (i : Fin J.sizes.length) {c : ℤ} (h₁ : (lo i : ℤ) ≤ c)
    (h₂ : c < (lo i : ℤ) + (J.sizes.get i : ℤ)) (j : ℕ) : c ≠ sepCol J j := by
  obtain ⟨b, -, h3, h4⟩ := hlo.bin i
  have h3' : ((2 + b * (J.capacity + 1) : ℕ) : ℤ) ≤ (lo i : ℤ) := by exact_mod_cast h3
  have h4' : ((lo i + J.sizes.get i : ℕ) : ℤ) ≤
      ((2 + b * (J.capacity + 1) + J.capacity : ℕ) : ℤ) := by exact_mod_cast h4
  push_cast at h3' h4'
  have hb : sepCol J b < c := by unfold sepCol; linarith
  have hb' : c < sepCol J (b + 1) := by rw [sepCol_succ]; unfold sepCol; linarith
  intro hc
  rcases le_or_gt j b with hj | hj
  · have := sepCol_mono J hj
    linarith
  · have := sepCol_mono J (show b + 1 ≤ j by omega)
    linarith

theorem firstCol_mem {J : Packing.Instance} (hJ : Normalised J) (lo : Fin J.sizes.length → ℕ)
    (i : Fin J.sizes.length) :
    (lo i : ℤ) ≤ firstCol lo i ∧ firstCol lo i < (lo i : ℤ) + (J.sizes.get i : ℤ) := by
  have := item_pos hJ i
  unfold firstCol
  split_ifs <;> omega

theorem lastCol_mem {J : Packing.Instance} (hJ : Normalised J) (lo : Fin J.sizes.length → ℕ)
    (i : Fin J.sizes.length) :
    (lo i : ℤ) ≤ lastCol lo i ∧ lastCol lo i < (lo i : ℤ) + (J.sizes.get i : ℤ) := by
  have := item_pos hJ i
  unfold lastCol
  split_ifs <;> omega

/-- An item starts in an odd column … -/
theorem firstCol_odd {J : Packing.Instance} (hJ : Normalised J) (lo : Fin J.sizes.length → ℕ)
    (i : Fin J.sizes.length) : firstCol lo i % 2 = 1 := by
  obtain ⟨r, hr⟩ := item_even hJ i
  have := item_pos hJ i
  unfold firstCol
  split_ifs <;> omega

/-- … and ends in an even one, because its size is even. -/
theorem lastCol_even {J : Packing.Instance} (hJ : Normalised J) (lo : Fin J.sizes.length → ℕ)
    (i : Fin J.sizes.length) : lastCol lo i % 2 = 0 := by
  obtain ⟨r, hr⟩ := item_even hJ i
  have := item_pos hJ i
  unfold lastCol
  split_ifs <;> omega

/-- Two items that share a column are the same item. -/
theorem eq_of_col {J : Packing.Instance} {lo : Fin J.sizes.length → ℕ} (hlo : Placed J lo)
    {i i' : Fin J.sizes.length} {c : ℤ} (h₁ : (lo i : ℤ) ≤ c)
    (h₂ : c < (lo i : ℤ) + (J.sizes.get i : ℤ)) (h₁' : (lo i' : ℤ) ≤ c)
    (h₂' : c < (lo i' : ℤ) + (J.sizes.get i' : ℤ)) : i = i' := by
  by_contra hne
  have hd := hlo.disjoint i i' hne
  obtain ⟨u, rfl⟩ : ∃ u : ℕ, c = u := ⟨c.toNat, by omega⟩
  have hu : u ∈ Finset.Ico (lo i) (lo i + J.sizes.get i) := by rw [Finset.mem_Ico]; omega
  have hu' : u ∈ Finset.Ico (lo i') (lo i' + J.sizes.get i') := by
    rw [Finset.mem_Ico]; omega
  exact Finset.disjoint_left.mp hd hu hu'

theorem firstCol_inj {J : Packing.Instance} (hJ : Normalised J) {lo : Fin J.sizes.length → ℕ}
    (hlo : Placed J lo) {i i' : Fin J.sizes.length} (h : firstCol lo i = firstCol lo i') :
    i = i' := by
  obtain ⟨h1, h2⟩ := firstCol_mem hJ lo i
  obtain ⟨h1', h2'⟩ := firstCol_mem hJ lo i'
  rw [h] at h1 h2
  exact eq_of_col hlo h1 h2 h1' h2'

theorem lastCol_inj {J : Packing.Instance} (hJ : Normalised J) {lo : Fin J.sizes.length → ℕ}
    (hlo : Placed J lo) {i i' : Fin J.sizes.length} (h : lastCol lo i = lastCol lo i') :
    i = i' := by
  obtain ⟨h1, h2⟩ := lastCol_mem hJ lo i
  obtain ⟨h1', h2'⟩ := lastCol_mem hJ lo i'
  rw [h] at h1 h2
  exact eq_of_col hlo h1 h2 h1' h2'

/-! ### Helpers for tokens -/

namespace LayoutTokens

/-- The point number `t` of a row, in coordinates. -/
theorem run_pt (x y z u v w t : ℤ) :
    (fun k : Fin 3 => pt x y z k + t * pt u v w k) = pt (x + t * u) (y + t * v) (z + t * w) :=
  site_ext (by simp) (by simp) (by simp)

theorem zero_eq_pt : (0 : Site) = pt 0 0 0 := site_ext (by simp) (by simp) (by simp)

theorem adj_zero_pt {x y z : ℤ} :
    cubicLattice.Adj 0 (pt x y z) ↔ x.natAbs + y.natAbs + z.natAbs = 1 := by
  rw [zero_eq_pt, adj_pt]
  simp

/-- A token given by coordinates is valid when its centre is in the cube, its two `P`'s are
outside and the two normals are different unit vectors. -/
theorem valid_pt {n : ℕ} {x y z a₁ a₂ a₃ b₁ b₂ b₃ : ℤ} (hc : pt x y z ∈ Q n)
    (ha : pt (x + a₁) (y + a₂) (z + a₃) ∉ Q n) (hb : pt (x + b₁) (y + b₂) (z + b₃) ∉ Q n)
    (haa : a₁.natAbs + a₂.natAbs + a₃.natAbs = 1) (hbb : b₁.natAbs + b₂.natAbs + b₃.natAbs = 1)
    (hne : ¬ (a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃)) :
    Token.Valid n ⟨pt x y z, pt a₁ a₂ a₃, pt b₁ b₂ b₃⟩ where
  mem := hc
  a_out := by simpa [pt_add] using ha
  b_out := by simpa [pt_add] using hb
  a_adj := by
    show cubicLattice.Adj (pt x y z) (pt x y z + pt a₁ a₂ a₃)
    rw [pt_add, adj_pt]
    omega
  b_adj := by
    show cubicLattice.Adj (pt x y z) (pt x y z + pt b₁ b₂ b₃)
    rw [pt_add, adj_pt]
    omega
  ne := fun h => hne (pt_eq_iff.mp h)

theorem tokSites_head?_of {ts : List Token} {t : Token} (h : ts.head? = some t) :
    (tokSites ts).head? = some (t.c + t.a) := by
  cases ts with
  | nil => simp at h
  | cons s ts =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact tokSites_head? _ _

theorem tokSites_getLast?_of {ts : List Token} {t : Token} (h : ts.getLast? = some t) :
    (tokSites ts).getLast? = some (t.c + t.b) := by
  obtain ⟨l, rfl⟩ := List.getLast?_eq_some_iff.mp h
  exact tokSites_getLast? _ _

theorem three_le_side (J : Packing.Instance) : 3 ≤ side J := by
  unfold side; omega

end LayoutTokens

open LayoutTokens

/-! ### `F₁` -/

theorem mem_f₁Tokens_c {J : Packing.Instance} {t : Token} (h : t ∈ f₁Tokens J) :
    1 ≤ t.c 0 ∧ t.c 0 ≤ N J - 1 ∧ t.c 1 = N J ∧ t.c 2 = 0 := by
  obtain ⟨t, ht, rfl⟩ := mem_altRun.mp h
  have := three_le_side J
  simp only [pt_apply_zero, pt_apply_one, pt_apply_two, N]
  omega

theorem f₁Tokens_valid (J : Packing.Instance) : ∀ t ∈ f₁Tokens J, t.Valid (side J) := by
  intro tk h
  obtain ⟨t, ht, rfl⟩ := mem_altRun.mp h
  have := three_le_side J
  rw [run_pt]
  split_ifs <;> apply valid_pt <;>
    first | (simp only [pt_mem_Q, N]; omega) | simp

theorem f₁_isChain (J : Packing.Instance) :
    (tokSites (f₁Tokens J)).IsChain cubicLattice.Adj := by
  exact tokSites_isChain (f₁Tokens_valid J)
    (altRun_isChain _ (adj_zero_pt.mpr (by decide)) _ _ _)

theorem f₁_head? (J : Packing.Instance) :
    (tokSites (f₁Tokens J)).head? = some (pt (N J - 1) (N J) (-1)) := by
  have := three_le_side J
  rw [f₁Tokens, tokSites_head?_of (altRun_head? _ _ (by omega) _ _)]
  simp [pt_add]

theorem f₁_getLast? {J : Packing.Instance} (hJ : Normalised J) :
    (tokSites (f₁Tokens J)).getLast? = some (pt 1 (N J) (-1)) := by
  have := three_le_side J
  have he : Even (side J - 2) := by
    obtain ⟨k, hk⟩ := side_even hJ
    exact ⟨k - 1, by omega⟩
  rw [f₁Tokens, tokSites_getLast?_of (altRun_getLast?_even _ _ (by omega) he _ _)]
  simp only [run_pt, pt_add, Option.some.injEq, pt_eq_iff, N]
  omega

/-! ### `F₂` -/

theorem mem_f₂Tokens_c {J : Packing.Instance} {t : Token} (h : t ∈ f₂Tokens J) :
    1 ≤ t.c 0 ∧ t.c 0 ≤ N J - 1 ∧ t.c 1 = 0 ∧ t.c 2 = N J := by
  obtain ⟨t, ht, rfl⟩ := mem_altRun.mp h
  have := three_le_side J
  simp only [pt_apply_zero, pt_apply_one, pt_apply_two, N]
  omega

theorem f₂Tokens_valid (J : Packing.Instance) : ∀ t ∈ f₂Tokens J, t.Valid (side J) := by
  intro tk h
  obtain ⟨t, ht, rfl⟩ := mem_altRun.mp h
  have := three_le_side J
  rw [run_pt]
  split_ifs <;> apply valid_pt <;>
    first | (simp only [pt_mem_Q, N]; omega) | simp

theorem f₂_isChain (J : Packing.Instance) :
    (tokSites (f₂Tokens J)).IsChain cubicLattice.Adj := by
  exact tokSites_isChain (f₂Tokens_valid J)
    (altRun_isChain _ (adj_zero_pt.mpr (by decide)) _ _ _)

theorem f₂_head? (J : Packing.Instance) :
    (tokSites (f₂Tokens J)).head? = some (pt (N J - 1) (-1) (N J)) := by
  have := three_le_side J
  rw [f₂Tokens, tokSites_head?_of (altRun_head? _ _ (by omega) _ _)]
  simp [pt_add]

theorem f₂_getLast? {J : Packing.Instance} (hJ : Normalised J) :
    (tokSites (f₂Tokens J)).getLast? = some (pt 1 (-1) (N J)) := by
  have := three_le_side J
  have he : Even (side J - 2) := by
    obtain ⟨k, hk⟩ := side_even hJ
    exact ⟨k - 1, by omega⟩
  rw [f₂Tokens, tokSites_getLast?_of (altRun_getLast?_even _ _ (by omega) he _ _)]
  simp only [run_pt, pt_add, Option.some.injEq, pt_eq_iff, N]
  omega

/-! ### The separators -/

theorem sepToken_valid (J : Packing.Instance) {j : ℕ} (hj : j ≤ J.bins) :
    (sepToken J j).Valid (side J) := by
  have := sepCol_range J hj
  have := three_le_side J
  unfold sepToken
  apply valid_pt <;> simp only [pt_mem_Q, N] at * <;> omega

/-! ### The items -/

theorem mem_itemTokens_c {J : Packing.Instance} {lo : Fin J.sizes.length → ℕ}
    {i : Fin J.sizes.length} {t : Token} (h : t ∈ itemTokens lo i) :
    (lo i : ℤ) ≤ t.c 0 ∧ t.c 0 < (lo i : ℤ) + (J.sizes.get i : ℤ) ∧ t.c 1 = 0 ∧ t.c 2 = 0 := by
  obtain ⟨t, ht, rfl⟩ := mem_altRun.mp h
  simp only [pt_apply_zero, pt_apply_one, pt_apply_two]
  by_cases hp : lo i % 2 = 1 <;> simp only [firstCol, hp, if_true, if_false] <;> omega

theorem itemTokens_valid {J : Packing.Instance} {lo : Fin J.sizes.length → ℕ}
    (hlo : Placed J lo) (i : Fin J.sizes.length) :
    ∀ t ∈ itemTokens lo i, t.Valid (side J) := by
  intro tk h
  have hc := mem_itemTokens_c h
  have hr := lo_range hlo i
  have := three_le_side J
  obtain ⟨t, ht, rfl⟩ := mem_altRun.mp h
  simp only [pt_apply_zero, pt_apply_one, pt_apply_two] at hc
  rw [run_pt]
  generalize firstCol lo i + ↑t * (if lo i % 2 = 1 then (1 : ℤ) else -1) = X at hc ⊢
  split_ifs <;> apply valid_pt <;>
    (simp only [pt_mem_Q, N] at *; omega)

theorem item_isChain {J : Packing.Instance} {lo : Fin J.sizes.length → ℕ}
    (hlo : Placed J lo) (i : Fin J.sizes.length) :
    (tokSites (itemTokens lo i)).IsChain cubicLattice.Adj := by
  refine tokSites_isChain (itemTokens_valid hlo i)
    (altRun_isChain _ (adj_zero_pt.mpr ?_) _ _ _)
  split_ifs <;> decide

theorem item_head? {J : Packing.Instance} (hJ : Normalised J) (lo : Fin J.sizes.length → ℕ)
    (i : Fin J.sizes.length) :
    (tokSites (itemTokens lo i)).head? = some (itemIn lo i) := by
  have := item_pos hJ i
  rw [itemTokens, tokSites_head?_of (altRun_head? _ _ this _ _)]
  simp [pt_add, itemIn]

theorem item_getLast? {J : Packing.Instance} (hJ : Normalised J) (lo : Fin J.sizes.length → ℕ)
    (i : Fin J.sizes.length) :
    (tokSites (itemTokens lo i)).getLast? = some (itemOut lo i) := by
  have := item_pos hJ i
  rw [itemTokens, tokSites_getLast?_of (altRun_getLast?_even _ _ this (item_even hJ i) _ _)]
  simp only [run_pt, pt_add, Option.some.injEq, itemOut, pt_eq_iff]
  by_cases hp : lo i % 2 = 1 <;> simp only [firstCol, lastCol, hp, if_true, if_false] <;>
    omega

/-! ### All of them together -/

/-- The tokens on the three free edges: `F₁`, the separators, `F₂` and the items. -/
def shelfTokens (J : Packing.Instance) (lo : Fin J.sizes.length → ℕ) : List Token :=
  f₁Tokens J ++ (List.range (J.bins + 1)).map (sepToken J) ++ f₂Tokens J ++
    (List.finRange J.sizes.length).flatMap (itemTokens lo)

theorem mem_shelfTokens {J : Packing.Instance} {lo : Fin J.sizes.length → ℕ} {t : Token}
    (h : t ∈ shelfTokens J lo) :
    t ∈ f₁Tokens J ∨ (∃ j, j ≤ J.bins ∧ t = sepToken J j) ∨ t ∈ f₂Tokens J ∨
      ∃ i, t ∈ itemTokens lo i := by
  simp only [shelfTokens, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_finRange, true_and] at h
  rcases h with ((h | ⟨j, hj, rfl⟩) | h) | ⟨i, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨j, by omega, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨i, h⟩))

theorem shelfTokens_valid {J : Packing.Instance} {lo : Fin J.sizes.length → ℕ}
    (hlo : Placed J lo) : ∀ t ∈ shelfTokens J lo, t.Valid (side J) := by
  intro t ht
  rcases mem_shelfTokens ht with h | ⟨j, hj, rfl⟩ | h | ⟨i, h⟩
  · exact f₁Tokens_valid J t h
  · exact sepToken_valid J hj
  · exact f₂Tokens_valid J t h
  · exact itemTokens_valid hlo i t h

/-- Every centre is an inner node of one of the three free edges. -/
theorem shelfTokens_c {J : Packing.Instance} {lo : Fin J.sizes.length → ℕ}
    (hlo : Placed J lo) : ∀ t ∈ shelfTokens J lo,
      1 ≤ t.c 0 ∧ t.c 0 ≤ N J - 1 ∧
        ((t.c 1 = N J ∧ t.c 2 = 0) ∨ (t.c 1 = 0 ∧ t.c 2 = 0) ∨ (t.c 1 = 0 ∧ t.c 2 = N J)) := by
  intro t ht
  rcases mem_shelfTokens ht with h | ⟨j, hj, rfl⟩ | h | ⟨i, h⟩
  · obtain ⟨h1, h2, h3, h4⟩ := mem_f₁Tokens_c h
    exact ⟨h1, h2, Or.inl ⟨h3, h4⟩⟩
  · obtain ⟨h1, h2⟩ := sepCol_range J hj
    exact ⟨h1, h2, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := mem_f₂Tokens_c h
    exact ⟨h1, h2, Or.inr (Or.inr ⟨h3, h4⟩)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := mem_itemTokens_c h
    obtain ⟨h5, h6⟩ := lo_range hlo i
    exact ⟨by omega, by omega, Or.inr (Or.inl ⟨h3, h4⟩)⟩

theorem shelfTokens_skeleton {J : Packing.Instance} {lo : Fin J.sizes.length → ℕ}
    (hlo : Placed J lo) : ∀ t ∈ shelfTokens J lo, EdgeSkeleton 0 (side J) t.c := by
  intro t ht
  obtain ⟨-, -, h⟩ := shelfTokens_c hlo t ht
  have hm := (shelfTokens_valid hlo t ht).mem
  refine ⟨hm, 1, 2, by decide, ?_, ?_⟩ <;>
    simp only [BoundaryCoordinate, Pi.zero_apply, N] at h ⊢ <;> omega

/-- Different tokens have different centres. -/
theorem shelfTokens_nodup {J : Packing.Instance} {lo : Fin J.sizes.length → ℕ}
    (hlo : Placed J lo) : ((shelfTokens J lo).map Token.c).Nodup := by
  have hN : 2 ≤ N J := by have := three_le_side J; unfold N; omega
  -- what we know of the centres of each family
  have h1 : ∀ x ∈ (f₁Tokens J).map Token.c, x 1 = N J ∧ x 2 = 0 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨-, -, h3, h4⟩ := mem_f₁Tokens_c ht
    exact ⟨h3, h4⟩
  have h2 : ∀ x ∈ ((List.range (J.bins + 1)).map (sepToken J)).map Token.c,
      ∃ j, x = pt (sepCol J j) 0 0 := by
    intro x hx
    simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact ⟨j, rfl⟩
  have h3 : ∀ x ∈ (f₂Tokens J).map Token.c, x 1 = 0 ∧ x 2 = N J := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨-, -, h3, h4⟩ := mem_f₂Tokens_c ht
    exact ⟨h3, h4⟩
  have h4 : ∀ i, ∀ x ∈ (itemTokens lo i).map Token.c,
      (lo i : ℤ) ≤ x 0 ∧ x 0 < (lo i : ℤ) + (J.sizes.get i : ℤ) ∧ x 1 = 0 ∧ x 2 = 0 := by
    intro i x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact mem_itemTokens_c ht
  have h4' : ∀ x ∈ ((List.finRange J.sizes.length).flatMap (itemTokens lo)).map Token.c,
      ∃ i, (lo i : ℤ) ≤ x 0 ∧ x 0 < (lo i : ℤ) + (J.sizes.get i : ℤ) ∧ x 1 = 0 ∧ x 2 = 0 := by
    intro x hx
    rw [List.map_flatMap, List.mem_flatMap] at hx
    obtain ⟨i, -, hx⟩ := hx
    exact ⟨i, h4 i x hx⟩
  -- each family on its own
  have n1 : ((f₁Tokens J).map Token.c).Nodup := by
    rw [f₁Tokens, altRun_centres]
    exact line_nodup _ (fun h => by simpa using congrFun h 0) _
  have n3 : ((f₂Tokens J).map Token.c).Nodup := by
    rw [f₂Tokens, altRun_centres]
    exact line_nodup _ (fun h => by simpa using congrFun h 0) _
  have n2 : (((List.range (J.bins + 1)).map (sepToken J)).map Token.c).Nodup := by
    rw [List.map_map]
    refine List.Nodup.map ?_ List.nodup_range
    intro j j' h
    have h' := (pt_eq_iff.mp h).1
    rcases lt_trichotomy j j' with hj | rfl | hj
    · exact absurd h' (ne_of_lt (sepCol_lt J hj))
    · rfl
    · exact absurd h' (ne_of_gt (sepCol_lt J hj))
  have n4 : (((List.finRange J.sizes.length).flatMap (itemTokens lo)).map Token.c).Nodup := by
    rw [List.map_flatMap, List.nodup_flatMap]
    refine ⟨fun i _ => ?_, ?_⟩
    · rw [itemTokens, altRun_centres]
      refine line_nodup _ (fun h => ?_) _
      have := congrFun h 0
      split_ifs at this <;> simp at this
    · refine (List.nodup_finRange _).imp ?_
      intro i i' hne x hx hx'
      obtain ⟨a1, a2, -, -⟩ := h4 i x hx
      obtain ⟨b1, b2, -, -⟩ := h4 i' x hx'
      exact hne (eq_of_col hlo a1 a2 b1 b2)
  rw [shelfTokens, List.map_append, List.map_append, List.map_append]
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr
    ⟨n1, n2, ?_⟩, n3, ?_⟩, n4, ?_⟩
  · rintro x hx y hy rfl
    obtain ⟨j, rfl⟩ := h2 x hy
    have := (h1 _ hx).1
    simp at this
    omega
  · rintro x hx y hy rfl
    have := (h3 x hy)
    rcases List.mem_append.mp hx with hx | hx
    · have := h1 x hx
      omega
    · obtain ⟨j, rfl⟩ := h2 x hx
      simp at this
      omega
  · rintro x hx y hy rfl
    obtain ⟨i, a1, a2, a3, a4⟩ := h4' x hy
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · have := h1 x hx
        omega
      · obtain ⟨j, rfl⟩ := h2 x hx
        simp only [pt_apply_zero] at a1 a2
        exact col_ne_sepCol hlo i a1 a2 j rfl
    · have := h3 x hx
      omega

end ProteinFolding.Shelf

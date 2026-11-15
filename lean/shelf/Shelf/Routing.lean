import Shelf.Sites

namespace ProteinFolding.Shelf.Routing

open ProteinFolding

/-- `|p 0 - q 0|`, written without `abs`. -/
def dx (p q : Site) : ℤ := if p 0 < q 0 then q 0 - p 0 else p 0 - q 0

/-- Step numbers at the ends of the first four pieces, and the length `L` of the path. -/
def T1 (p : Site) (Y : ℤ) : ℤ := p 1 - Y
def T2 (p : Site) (Y Z : ℤ) : ℤ := T1 p Y + (p 2 - Z)
def T3 (p q : Site) (Y Z : ℤ) : ℤ := T2 p Y Z + dx p q
def T4 (p q : Site) (Y Z : ℤ) : ℤ := T3 p q Y Z + (q 2 - Z)
def L (p q : Site) (Y Z : ℤ) : ℤ := T4 p q Y Z + (q 1 - Y)

/-- The site reached after `t` steps on the path from `p` to `q` through the level `y = Y`
and the row `z = Z`. -/
def g (p q : Site) (Y Z : ℤ) (t : ℤ) : Site :=
  pt (if t ≤ T2 p Y Z then p 0 else if t ≤ T3 p q Y Z then
        (if p 0 < q 0 then p 0 + (t - T2 p Y Z) else p 0 - (t - T2 p Y Z)) else q 0)
     (if t ≤ T1 p Y then p 1 - t else if t ≤ T4 p q Y Z then Y else Y + (t - T4 p q Y Z))
     (if t ≤ T1 p Y then p 2 else if t ≤ T2 p Y Z then p 2 - (t - T1 p Y) else
        if t ≤ T3 p q Y Z then Z else if t ≤ T4 p q Y Z then Z + (t - T3 p q Y Z) else q 2)

variable {p q : Site} {Y Z : ℤ}

theorem g_zero (hY : Y < p 1) (hZ : Z < p 2) : g p q Y Z 0 = p := by
  apply site_ext <;> simp only [g, T1, T2, T3, T4, dx, pt_apply_zero, pt_apply_one,
    pt_apply_two] <;> split_ifs <;> omega

theorem g_L (hZ : Z < p 2) (hY' : Y < q 1) (hZ' : Z < q 2) :
    g p q Y Z (L p q Y Z) = q := by
  apply site_ext <;> simp only [g, L, T1, T2, T3, T4, dx, pt_apply_zero, pt_apply_one,
    pt_apply_two] <;> split_ifs <;> omega

theorem g_adj (hZ : Z < p 2) (hZ' : Z < q 2) (t : ℤ) :
    cubicLattice.Adj (g p q Y Z t) (g p q Y Z (t + 1)) := by
  rw [g, g, adj_pt]
  simp only [T1, T2, T3, T4, dx]
  split_ifs <;> omega

/-- Which piece the `t`-th site lies on, with its coordinates. -/
theorem g_piece (hZ : Z < p 2) (hZ' : Z < q 2) (t : ℤ) :
    (t ≤ T1 p Y ∧ g p q Y Z t 0 = p 0 ∧ g p q Y Z t 1 = p 1 - t ∧ g p q Y Z t 2 = p 2) ∨
    (T1 p Y < t ∧ t ≤ T2 p Y Z ∧ g p q Y Z t 0 = p 0 ∧ g p q Y Z t 1 = Y ∧
      g p q Y Z t 2 = p 2 - (t - T1 p Y)) ∨
    (T2 p Y Z < t ∧ t ≤ T3 p q Y Z ∧ g p q Y Z t 1 = Y ∧ g p q Y Z t 2 = Z ∧
      ((p 0 < q 0 ∧ g p q Y Z t 0 = p 0 + (t - T2 p Y Z)) ∨
       (¬ p 0 < q 0 ∧ g p q Y Z t 0 = p 0 - (t - T2 p Y Z)))) ∨
    (T3 p q Y Z < t ∧ t ≤ T4 p q Y Z ∧ g p q Y Z t 0 = q 0 ∧ g p q Y Z t 1 = Y ∧
      g p q Y Z t 2 = Z + (t - T3 p q Y Z)) ∨
    (T4 p q Y Z < t ∧ g p q Y Z t 0 = q 0 ∧ g p q Y Z t 1 = Y + (t - T4 p q Y Z) ∧
      g p q Y Z t 2 = q 2) := by
  have a : T1 p Y < T2 p Y Z ∧ T2 p Y Z ≤ T3 p q Y Z ∧ T3 p q Y Z ≤ T4 p q Y Z := by
    simp only [T2, T3, T4, dx]; split_ifs <;> omega
  simp only [g, pt_apply_zero, pt_apply_one, pt_apply_two]
  split_ifs <;> omega

theorem g_inj (hZ : Z < p 2) (hZ' : Z < q 2)
    (hx : p 0 ≠ q 0) {t t' : ℤ} (h : g p q Y Z t = g p q Y Z t') : t = t' := by
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have hT : T2 p Y Z = T1 p Y + (p 2 - Z) ∧ T3 p q Y Z = T2 p Y Z + dx p q ∧
      T4 p q Y Z = T3 p q Y Z + (q 2 - Z) ∧ L p q Y Z = T4 p q Y Z + (q 1 - Y) ∧
      T1 p Y = p 1 - Y := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hd : (p 0 < q 0 → dx p q = q 0 - p 0) ∧ (¬ p 0 < q 0 → dx p q = p 0 - q 0) := by
    unfold dx; constructor <;> intro h <;> simp [h]
  rcases g_piece (p := p) (q := q) (Y := Y) (Z := Z) hZ hZ' t with h | h | h | h | h <;>
  rcases g_piece (p := p) (q := q) (Y := Y) (Z := Z) hZ hZ' t' with h' | h' | h' | h' | h' <;>
  omega

/-- The inner sites of the path lie on the vertical piece under `p`, in the level `y = Y`
with `x ∈ {x(p), x(q)}` or `z = Z`, or on the vertical piece under `q`. -/
theorem g_cases (hZ : Z < p 2) (hZ' : Z < q 2) (t : ℤ) :
    (g p q Y Z t 0 = p 0 ∧ g p q Y Z t 2 = p 2 ∧ g p q Y Z t 1 = p 1 - t ∧ Y ≤ g p q Y Z t 1) ∨
    (g p q Y Z t 1 = Y ∧ (g p q Y Z t 0 = p 0 ∨ g p q Y Z t 0 = q 0 ∨ g p q Y Z t 2 = Z)) ∨
    (g p q Y Z t 0 = q 0 ∧ g p q Y Z t 2 = q 2 ∧
      g p q Y Z t 1 = q 1 - (L p q Y Z - t) ∧ Y ≤ g p q Y Z t 1) := by
  simp only [g, L, T1, T2, T3, T4, dx, pt_apply_zero, pt_apply_one, pt_apply_two]
  split_ifs <;> omega

theorem dx_eq_abs (p q : Site) : dx p q = |p 0 - q 0| := by
  unfold dx
  split_ifs with h
  · rw [abs_of_neg (by omega)]; ring
  · rw [abs_of_nonneg (by omega)]

/-- The inner sites of the path: steps `1, …, L - 1`. -/
def mid (p q : Site) (Y Z : ℤ) : List Site :=
  (List.range ((L p q Y Z).toNat - 1)).map fun n : ℕ => g p q Y Z ((n : ℤ) + 1)

theorem L_ge (hY : Y < p 1) (hZ : Z < p 2) (hY' : Y < q 1) (hZ' : Z < q 2) :
    2 ≤ L p q Y Z := by
  simp only [L, T1, T2, T3, T4, dx]; split_ifs <;> omega

theorem mid_length (hY : Y < p 1) (hZ : Z < p 2) (hY' : Y < q 1) (hZ' : Z < q 2) :
    ((mid p q Y Z).length : ℤ) + 1 = L p q Y Z := by
  have := L_ge hY hZ hY' hZ'
  simp only [mid, List.length_map, List.length_range]
  omega

theorem mem_mid {s : Site} (h : s ∈ mid p q Y Z) :
    ∃ t : ℤ, 1 ≤ t ∧ t + 1 ≤ L p q Y Z ∧ g p q Y Z t = s := by
  simp only [mid, List.mem_map, List.mem_range] at h
  obtain ⟨n, hn, rfl⟩ := h
  exact ⟨n + 1, by omega, by omega, rfl⟩

theorem path_eq (hY : Y < p 1) (hZ : Z < p 2) (hY' : Y < q 1) (hZ' : Z < q 2) :
    p :: (mid p q Y Z ++ [q]) =
      (List.range ((L p q Y Z).toNat + 1)).map fun n : ℕ => g p q Y Z n := by
  have hL := L_ge hY hZ hY' hZ'
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (L p q Y Z).toNat = N + 1 := ⟨(L p q Y Z).toNat - 1, by omega⟩
  rw [mid, hN, List.range_succ, List.range_succ_eq_map, List.map_append, List.map_cons,
    List.map_map]
  simp only [Nat.add_sub_cancel, List.map_cons, List.map_nil, List.cons_append]
  congr 1
  · exact (g_zero hY hZ).symm
  · have e : (((N + 1 : ℕ) : ℤ)) = L p q Y Z := by omega
    rw [e, g_L hZ hY' hZ']
    congr 1

theorem path_chain (hY : Y < p 1) (hZ : Z < p 2) (hY' : Y < q 1) (hZ' : Z < q 2) :
    (p :: (mid p q Y Z ++ [q])).IsChain cubicLattice.Adj := by
  rw [path_eq hY hZ hY' hZ', List.isChain_map, List.isChain_range]
  intro m hm
  simpa using g_adj (p := p) (q := q) (Y := Y) (Z := Z) hZ hZ' m

theorem path_nodup (hY : Y < p 1) (hZ : Z < p 2) (hY' : Y < q 1) (hZ' : Z < q 2)
    (hx : p 0 ≠ q 0) : (p :: (mid p q Y Z ++ [q])).Nodup := by
  rw [path_eq hY hZ hY' hZ', List.nodup_map_iff_inj_on List.nodup_range]
  intro a ha b hb h
  simp only [List.mem_range] at ha hb
  exact_mod_cast g_inj hZ hZ' hx h

/-- Where an inner site of the path lies: strictly below `p` on its vertical line, in the
level `y = Y` with `x ∈ {x(p), x(q)}` or `z = Z`, or strictly below `q`. -/
theorem mid_cases (hY : Y < p 1) (hZ : Z < p 2) (hY' : Y < q 1) (hZ' : Z < q 2)
    {s : Site} (hs : s ∈ mid p q Y Z) :
    (s 0 = p 0 ∧ s 2 = p 2 ∧ Y ≤ s 1 ∧ s 1 < p 1) ∨
    (s 1 = Y ∧ (s 0 = p 0 ∨ s 0 = q 0 ∨ s 2 = Z)) ∨
    (s 0 = q 0 ∧ s 2 = q 2 ∧ Y ≤ s 1 ∧ s 1 < q 1) := by
  obtain ⟨t, h1, h2, rfl⟩ := mem_mid hs
  have := g_cases (p := p) (q := q) (Y := Y) (Z := Z) hZ hZ' t
  omega

end ProteinFolding.Shelf.Routing

namespace ProteinFolding.Shelf

open ProteinFolding Routing

/-- The number `b_i` of Lemma 15: the length of the shortest route of the `i`-th pair of
ports `p`, `q`, which goes down to the level `y = y₀ - 1 - i`, forward to `z = z₀ - 1`,
across in direction `x`, and back. -/
def routeBound (y₀ z₀ : ℤ) (i : ℕ) (p q : Site) : ℤ :=
  (p 1 - (y₀ - 1 - i)) + (q 1 - (y₀ - 1 - i)) + (p 2 - z₀ + 1) + (q 2 - z₀ + 1) + |p 0 - q 0|

/-- **Lemma 15 (Routing Lemma).** `W` is a set of sites with `y ≥ y₀` and `z ≥ z₀`; the ports
`p i`, `q i` have pairwise different `x`-coordinates, and no site of `W` is below a port.
Then the pairs can be joined by pairwise disjoint paths that avoid `W`, the `i`-th one with
`routeBound … + 2 * e i` steps for any prescribed `e i`. We return the inner sites `mid i` of
the paths: the `i`-th path is `p i :: (mid i ++ [q i])`. -/
theorem routes (W : Set Site) (y₀ z₀ : ℤ) (hW : ∀ w ∈ W, y₀ ≤ w 1 ∧ z₀ ≤ w 2)
    (k : ℕ) (p q : Fin k → Site) (e : Fin k → ℕ)
    (hp : ∀ i, y₀ ≤ p i 1 ∧ z₀ ≤ p i 2) (hq : ∀ i, y₀ ≤ q i 1 ∧ z₀ ≤ q i 2)
    (hpp : ∀ i j, i ≠ j → p i 0 ≠ p j 0) (hqq : ∀ i j, i ≠ j → q i 0 ≠ q j 0)
    (hpq : ∀ i j, p i 0 ≠ q j 0)
    (hpW : ∀ i, ∀ t : ℤ, 1 ≤ t → pt (p i 0) (p i 1 - t) (p i 2) ∉ W)
    (hqW : ∀ i, ∀ t : ℤ, 1 ≤ t → pt (q i 0) (q i 1 - t) (q i 2) ∉ W) :
    ∃ mid : Fin k → List Site,
      (∀ i, ((mid i).length : ℤ) + 1 = routeBound y₀ z₀ i (p i) (q i) + 2 * (e i : ℤ)) ∧
      (∀ i, (p i :: (mid i ++ [q i])).IsChain cubicLattice.Adj) ∧
      (∀ i, (p i :: (mid i ++ [q i])).Nodup) ∧
      (∀ i j, i ≠ j → ∀ s ∈ mid i, s ∉ mid j) ∧
      (∀ i, ∀ s ∈ mid i, s ∉ W) ∧
      (∀ i j, ∀ s ∈ mid i, s ≠ p j ∧ s ≠ q j) := by
  -- The level `Y i` and the row `Z i` of the `i`-th path.
  set Y : Fin k → ℤ := fun i => y₀ - 1 - (i : ℕ) with hYdef
  set Z : Fin k → ℤ := fun i => z₀ - 1 - (e i : ℤ) with hZdef
  have hY : ∀ i, Y i < p i 1 := fun i => by simp only [hYdef]; have := hp i; omega
  have hY' : ∀ i, Y i < q i 1 := fun i => by simp only [hYdef]; have := hq i; omega
  have hZ : ∀ i, Z i < p i 2 := fun i => by simp only [hZdef]; have := hp i; omega
  have hZ' : ∀ i, Z i < q i 2 := fun i => by simp only [hZdef]; have := hq i; omega
  have cases : ∀ i, ∀ s ∈ Routing.mid (p i) (q i) (Y i) (Z i),
      (s 0 = p i 0 ∧ s 2 = p i 2 ∧ y₀ - 1 - (i : ℕ) ≤ s 1 ∧ s 1 < p i 1) ∨
      (s 1 = y₀ - 1 - (i : ℕ) ∧ (s 0 = p i 0 ∨ s 0 = q i 0 ∨ s 2 = z₀ - 1 - (e i : ℤ))) ∨
      (s 0 = q i 0 ∧ s 2 = q i 2 ∧ y₀ - 1 - (i : ℕ) ≤ s 1 ∧ s 1 < q i 1) :=
    fun i s hs => mid_cases (hY i) (hZ i) (hY' i) (hZ' i) hs
  refine ⟨fun i => Routing.mid (p i) (q i) (Y i) (Z i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [mid_length (hY i) (hZ i) (hY' i) (hZ' i)]
    simp only [L, T4, T3, T2, T1, dx_eq_abs, routeBound, hYdef, hZdef]
    ring
  · exact fun i => path_chain (hY i) (hZ i) (hY' i) (hZ' i)
  · exact fun i => path_nodup (hY i) (hZ i) (hY' i) (hZ' i) (hpq i i)
  · intro i j hij s hi hj
    have hij' : ((i : ℕ) : ℤ) ≠ ((j : ℕ) : ℤ) := by
      intro h; exact hij (Fin.ext (by exact_mod_cast h))
    have := cases i s hi
    have := cases j s hj
    have := hpp i j hij; have := hpp j i (Ne.symm hij)
    have := hqq i j hij; have := hqq j i (Ne.symm hij)
    have := hpq i j; have := hpq j i; have := hpq i i; have := hpq j j
    have := hp i; have := hp j; have := hq i; have := hq j
    omega
  · intro i s hs hsW
    have hs' := cases i s hs
    have := hW s hsW
    rcases hs' with h | h | h
    · apply hpW i (p i 1 - s 1) (by omega)
      convert hsW using 1
      exact site_ext (by simp [h.1]) (by simp) (by simp [h.2.1])
    · omega
    · apply hqW i (q i 1 - s 1) (by omega)
      convert hsW using 1
      exact site_ext (by simp [h.1]) (by simp) (by simp [h.2.1])
  · intro i j s hs
    have := cases i s hs
    have := hp i; have := hp j; have := hq i; have := hq j
    have := hpq i j; have := hpq j i; have := hpq i i
    by_cases hij : i = j
    · subst hij
      constructor <;> rintro rfl <;> omega
    · have := hpp i j hij; have := hqq i j hij
      constructor <;> rintro rfl <;> omega

end ProteinFolding.Shelf

import Shelf.LayoutTokens

/-!
# The `P`'s that belong to no token

Apart from the tokens and the inner sites of the linkers, the fold has a few
single `P`'s and three tethers. This file checks their coordinates: they are
different sites, they are outside the cube, and none of them is a site of a
token. It also checks that everything except the inside of the linkers lies in
the box `InBox`, which the linkers avoid.
-/

namespace ProteinFolding.Shelf
open ProteinFolding Residue CubicPackingGeometry Layout
namespace LayoutPlain

theorem line_pt (x y z u v w : ℤ) (r : ℕ) :
    line (pt x y z) (pt u v w) r =
      (List.range r).map fun t : ℕ => pt (x + t * u) (y + t * v) (z + t * w) := by
  unfold line
  congr 1
  funext t
  exact site_ext rfl rfl rfl

theorem mem_line_pt {x y z u v w : ℤ} {r : ℕ} {p : Site} :
    p ∈ line (pt x y z) (pt u v w) r ↔
      ∃ t : ℕ, t < r ∧ p = pt (x + t * u) (y + t * v) (z + t * w) := by
  rw [line_pt, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, List.mem_range.mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, List.mem_range.mpr ht, rfl⟩

theorem line_pt_getLast? (x y z u v w : ℤ) {r : ℕ} (hr : 0 < r) :
    (line (pt x y z) (pt u v w) r).getLast? =
      some (pt (x + ((r : ℤ) - 1) * u) (y + ((r : ℤ) - 1) * v) (z + ((r : ℤ) - 1) * w)) := by
  rw [line_getLast? _ _ hr]
  congr 1
  exact site_ext rfl rfl rfl

theorem adj_zero_pt {u v w : ℤ} :
    cubicLattice.Adj 0 (pt u v w) ↔ u.natAbs + v.natAbs + w.natAbs = 1 := by
  rw [show (0 : Site) = pt 0 0 0 from site_ext rfl rfl rfl, adj_pt]
  simp

theorem side_cast (J : Packing.Instance) : (side J : ℤ) = N J + 1 := by
  unfold N; ring

theorem two_le_N (J : Packing.Instance) : 2 ≤ N J := by
  rw [N_eq]
  have : (0 : ℤ) ≤ (J.bins : ℤ) * ((J.capacity : ℤ) + 1) := by positivity
  omega

theorem mem_tether₁ {J : Packing.Instance} {p : Site} (h : p ∈ tether₁ J) :
    ∃ y, 1 ≤ y ∧ y ≤ N J - 1 ∧ p = pt 1 y (-1) := by
  have := side_cast J
  rw [tether₁, mem_line_pt] at h
  obtain ⟨t, ht, rfl⟩ := h
  refine ⟨N J - 1 - t, by omega, by omega, ?_⟩
  rw [pt_eq_iff]
  refine ⟨by ring, by ring, by ring⟩

theorem mem_tether₂ {J : Packing.Instance} {p : Site} (h : p ∈ tether₂ J) :
    ∃ z, 1 ≤ z ∧ z ≤ N J - 1 ∧ p = pt (N J - 1) (-1) z := by
  have := side_cast J
  rw [tether₂, mem_line_pt] at h
  obtain ⟨t, ht, rfl⟩ := h
  refine ⟨1 + t, by omega, by omega, ?_⟩
  rw [pt_eq_iff]
  refine ⟨by ring, by ring, by ring⟩

/-- Where the sites of `innerMid J j` are, with `s = sepCol J j`: in the strip
`s ≤ x ≤ s + B + 1`, `-1 ≤ y ≤ 0`, `-2 ≤ z ≤ -1`, and only the last three sites leave
the row `(x, -1, -1)`. -/
theorem mem_innerMid {J : Packing.Instance} {j : ℕ} {p : Site} (h : p ∈ innerMid J j) :
    ∃ x y z, p = pt x y z ∧ sepCol J j ≤ x ∧ x ≤ sepCol J j + J.capacity + 1 ∧
      -1 ≤ y ∧ y ≤ 0 ∧ -2 ≤ z ∧ z ≤ -1 ∧ (y = 0 → z = -2) ∧
      (x = sepCol J j + J.capacity + 1 → z = -2) ∧ (z = -2 → sepCol J j + J.capacity ≤ x) := by
  have hs := sepCol_succ J j
  unfold innerMid at h
  rw [List.mem_append, mem_line_pt] at h
  rcases h with ⟨t, ht, rfl⟩ | h
  · refine ⟨_, _, _, rfl, ?_⟩
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl, by omega⟩

end LayoutPlain

open LayoutPlain

/-! ### Sites that no token uses -/

/-- A site that no token centred on the skeleton can use. -/
def OffTokens (n : ℕ) (p : Site) : Prop :=
  ∀ t : Token, t.Valid n → EdgeSkeleton 0 n t.c → p ∉ t.sites

namespace LayoutPlain

theorem clamp_pt (n : ℕ) (x y z : ℤ) :
    clamp n (pt x y z) =
      pt (max 0 (min x ((n : ℤ) - 1))) (max 0 (min y ((n : ℤ) - 1)))
        (max 0 (min z ((n : ℤ) - 1))) :=
  site_ext rfl rfl rfl

theorem skel_pt {n : ℕ} {x y z : ℤ} (h : EdgeSkeleton 0 n (pt x y z)) :
    ((x = 0 ∨ x + 1 = n) ∧ (y = 0 ∨ y + 1 = n)) ∨ ((x = 0 ∨ x + 1 = n) ∧ (z = 0 ∨ z + 1 = n)) ∨
      ((y = 0 ∨ y + 1 = n) ∧ (z = 0 ∨ z + 1 = n)) := by
  obtain ⟨_, i, j, hij, hi, hj⟩ := h
  simp only [BoundaryCoordinate, Pi.zero_apply, zero_add] at hi hj
  fin_cases i <;> fin_cases j <;> simp_all

/-- A site is off the tokens if, whenever its clamp is on the skeleton, it is at distance
at least 2 from its clamp. -/
theorem off_pt {n : ℕ} {x y z : ℤ}
    (h : (((max 0 (min x ((n : ℤ) - 1)) = 0 ∨ max 0 (min x ((n : ℤ) - 1)) + 1 = n) ∧
          (max 0 (min y ((n : ℤ) - 1)) = 0 ∨ max 0 (min y ((n : ℤ) - 1)) + 1 = n)) ∨
        ((max 0 (min x ((n : ℤ) - 1)) = 0 ∨ max 0 (min x ((n : ℤ) - 1)) + 1 = n) ∧
          (max 0 (min z ((n : ℤ) - 1)) = 0 ∨ max 0 (min z ((n : ℤ) - 1)) + 1 = n)) ∨
        ((max 0 (min y ((n : ℤ) - 1)) = 0 ∨ max 0 (min y ((n : ℤ) - 1)) + 1 = n) ∧
          (max 0 (min z ((n : ℤ) - 1)) = 0 ∨ max 0 (min z ((n : ℤ) - 1)) + 1 = n))) →
      2 ≤ (max 0 (min x ((n : ℤ) - 1)) - x).natAbs + (max 0 (min y ((n : ℤ) - 1)) - y).natAbs +
        (max 0 (min z ((n : ℤ) - 1)) - z).natAbs) :
    OffTokens n (pt x y z) := by
  intro t hv hs hp
  have hc := hv.clamp_of_mem hp
  have hd := hv.latticeDistance_le hp
  rw [← hc, clamp_pt] at hs hd
  rw [latticeDistance_pt] at hd
  have := h (skel_pt hs)
  omega

end LayoutPlain

/-- A point of the cube that is not on the skeleton is not a site of a token. -/
theorem offTokens_of_core {n : ℕ} {p : Site} (hp : p ∈ Q n) (hs : ¬ EdgeSkeleton 0 n p) :
    OffTokens n p := by
  intro t hv hc hpt
  rw [← hv.clamp_of_mem hpt, clamp_eq_self hp] at hc
  exact hs hc

theorem not_mem_tokSites_of_off {n : ℕ} {ts : List Token} (hv : ∀ t ∈ ts, t.Valid n)
    (hs : ∀ t ∈ ts, EdgeSkeleton 0 n t.c) {p : Site} (hp : OffTokens n p) :
    p ∉ tokSites ts := by
  intro h
  unfold tokSites at h
  obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.mp h
  exact hp t (hv t ht) (hs t ht) hpt

/-! ### The box -/

theorem inBox_of_mem_Q {J : Packing.Instance} {p : Site} (hp : p ∈ Q (side J)) : InBox J p := by
  have := side_cast J
  rw [mem_Q] at hp
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  left
  omega

theorem inBox_of_token {J : Packing.Instance} {t : Token} (hv : t.Valid (side J)) {p : Site}
    (hp : p ∈ t.sites) : InBox J p := by
  have := side_cast J
  have hd := hv.latticeDistance_le hp
  rw [latticeDistance_eq] at hd
  have hc := hv.mem
  rw [mem_Q] at hc
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  left
  omega

theorem inBox_of_tokSites {J : Packing.Instance} {ts : List Token}
    (hv : ∀ t ∈ ts, t.Valid (side J)) {p : Site} (hp : p ∈ tokSites ts) : InBox J p := by
  unfold tokSites at hp
  obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.mp hp
  exact inBox_of_token (hv t ht) hpt

/-! ### The plain `P`'s -/

/-- The `P`'s of the fold that belong to no token and are not inside a linker. -/
def plain (J : Packing.Instance) : List Site :=
  [firstP J, p₀ J, q₀ J, q₀' J] ++ tether₁ J ++ (List.range J.bins).flatMap (innerMid J) ++
    tether₂ J

theorem mem_plain {J : Packing.Instance} {p : Site} :
    p ∈ plain J ↔ p = firstP J ∨ p = p₀ J ∨ p = q₀ J ∨ p = q₀' J ∨ p ∈ tether₁ J ∨
      (∃ j, j < J.bins ∧ p ∈ innerMid J j) ∨ p ∈ tether₂ J := by
  simp only [plain, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range, or_assoc]

theorem plain_not_mem_Q (J : Packing.Instance) : ∀ p ∈ plain J, p ∉ Q (side J) := by
  have := side_cast J
  have := two_le_N J
  intro p hp
  rw [mem_plain] at hp
  rcases hp with rfl | rfl | rfl | rfl | hp | ⟨j, _, hp⟩ | hp
  · rw [firstP, pt_mem_Q]; omega
  · rw [p₀, pt_mem_Q]; omega
  · rw [q₀, pt_mem_Q]; omega
  · rw [q₀', pt_mem_Q]; omega
  · obtain ⟨y, _, _, rfl⟩ := mem_tether₁ hp
    rw [pt_mem_Q]; omega
  · obtain ⟨x, y, z, rfl, h⟩ := mem_innerMid hp
    rw [pt_mem_Q]; omega
  · obtain ⟨z, _, _, rfl⟩ := mem_tether₂ hp
    rw [pt_mem_Q]; omega

theorem plain_off (J : Packing.Instance) : ∀ p ∈ plain J, OffTokens (side J) p := by
  have := side_cast J
  have := two_le_N J
  intro p hp
  rw [mem_plain] at hp
  rcases hp with rfl | rfl | rfl | rfl | hp | ⟨j, _, hp⟩ | hp
  · apply off_pt; omega
  · apply off_pt; omega
  · apply off_pt; omega
  · apply off_pt; omega
  · obtain ⟨y, _, _, rfl⟩ := mem_tether₁ hp
    apply off_pt; omega
  · obtain ⟨x, y, z, rfl, h⟩ := mem_innerMid hp
    apply off_pt; omega
  · obtain ⟨z, _, _, rfl⟩ := mem_tether₂ hp
    apply off_pt; omega

theorem plain_inBox (J : Packing.Instance) : ∀ p ∈ plain J, InBox J p := by
  have := side_cast J
  have := two_le_N J
  intro p hp
  rw [mem_plain] at hp
  rcases hp with rfl | rfl | rfl | rfl | hp | ⟨j, hj, hp⟩ | hp
  · left; simp only [firstP, pt_apply_zero, pt_apply_one, pt_apply_two]; omega
  · right; left; rfl
  · right; right; rfl
  · left; simp only [q₀', pt_apply_zero, pt_apply_one, pt_apply_two]; omega
  · obtain ⟨y, _, _, rfl⟩ := mem_tether₁ hp
    left; simp only [pt_apply_zero, pt_apply_one, pt_apply_two]; omega
  · obtain ⟨x, y, z, rfl, h⟩ := mem_innerMid hp
    have h1 := sepCol_range J (show j + 1 ≤ J.bins by omega)
    have h2 := sepCol_succ J j
    left; simp only [pt_apply_zero, pt_apply_one, pt_apply_two]; omega
  · obtain ⟨z, _, _, rfl⟩ := mem_tether₂ hp
    left; simp only [pt_apply_zero, pt_apply_one, pt_apply_two]; omega

namespace LayoutPlain

theorem pt_ne_zero {u v w : ℤ} (h : u ≠ 0) : pt u v w ≠ 0 := fun e => h (congrFun e 0)

theorem tether₁_nodup (J : Packing.Instance) : (tether₁ J).Nodup :=
  line_nodup _ (fun e => by simpa using congrFun e 1) _

theorem tether₂_nodup (J : Packing.Instance) : (tether₂ J).Nodup :=
  line_nodup _ (fun e => by simpa using congrFun e 2) _

theorem innerMid_nodup (J : Packing.Instance) (j : ℕ) : (innerMid J j).Nodup := by
  unfold innerMid
  rw [List.nodup_append]
  refine ⟨line_nodup _ (pt_ne_zero one_ne_zero) _, ?_, ?_⟩
  · simp [pt_eq_iff]
  · intro a ha b hb
    rw [mem_line_pt] at ha
    obtain ⟨t, _, rfl⟩ := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> rw [Ne, pt_eq_iff] <;> omega

end LayoutPlain

theorem plain_nodup {J : Packing.Instance} (hJ : Normalised J) : (plain J).Nodup := by
  have hB := hJ.capacity_pos
  have := side_cast J
  have := two_le_N J
  unfold plain
  rw [List.nodup_append, List.nodup_append, List.nodup_append]
  refine ⟨⟨⟨?_, tether₁_nodup J, ?_⟩, ?_, ?_⟩, tether₂_nodup J, ?_⟩
  · simp only [firstP, p₀, q₀, q₀', List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      pt_eq_iff, List.nodup_nil, not_or, and_true, not_false_eq_true]
    omega
  · intro a ha b hb
    obtain ⟨y, _, _, rfl⟩ := mem_tether₁ hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;>
      simp only [firstP, p₀, q₀, q₀', Ne, pt_eq_iff] <;> omega
  · rw [List.nodup_flatMap]
    refine ⟨fun j _ => innerMid_nodup J j, ?_⟩
    refine List.pairwise_lt_range.imp ?_
    intro j j' hjj' a ha hb
    obtain ⟨x, y, z, rfl, h⟩ := mem_innerMid ha
    obtain ⟨x', y', z', he, h'⟩ := mem_innerMid hb
    rw [pt_eq_iff] at he
    have hs := sepCol_succ J j
    have hle : sepCol J (j + 1) ≤ sepCol J j' := by
      rcases Nat.lt_or_ge (j + 1) j' with h1 | h1
      · exact (sepCol_lt J h1).le
      · rw [show j' = j + 1 by omega]
    omega
  · intro a ha b hb
    obtain ⟨j, _, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨x, y, z, rfl, h⟩ := mem_innerMid hb
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;>
        simp only [firstP, p₀, q₀, q₀', Ne, pt_eq_iff] <;> omega
    · obtain ⟨y, _, _, rfl⟩ := mem_tether₁ ha
      rw [Ne, pt_eq_iff]; omega
  · intro a ha b hb
    obtain ⟨z, _, _, rfl⟩ := mem_tether₂ hb
    rw [List.mem_append, List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;>
        simp only [firstP, p₀, q₀, q₀', Ne, pt_eq_iff] <;> omega
    · obtain ⟨y, _, _, rfl⟩ := mem_tether₁ ha
      rw [Ne, pt_eq_iff]; omega
    · obtain ⟨j, _, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨x, y, z, rfl, h⟩ := mem_innerMid ha
      rw [Ne, pt_eq_iff]; omega

/-! ### The tethers -/

theorem tether₁_length (J : Packing.Instance) : (tether₁ J).length = side J - 2 := by
  simp [tether₁]

theorem tether₁_isChain (J : Packing.Instance) : (tether₁ J).IsChain cubicLattice.Adj :=
  line_isChain _ (adj_zero_pt.mpr (by norm_num)) _

theorem tether₁_head? (J : Packing.Instance) :
    (tether₁ J).head? = some (pt 1 (N J - 1) (-1)) := by
  have h3 : 3 ≤ side J := by unfold side; omega
  exact line_head? _ _ (by omega)

theorem tether₁_getLast? (J : Packing.Instance) :
    (tether₁ J).getLast? = some (pt 1 1 (-1)) := by
  have h3 : 3 ≤ side J := by unfold side; omega
  rw [tether₁, line_pt_getLast? _ _ _ _ _ _ (by omega), Option.some_inj, pt_eq_iff]
  have := side_cast J
  push_cast [Nat.cast_sub (show 2 ≤ side J by omega)]
  refine ⟨by ring, by linarith, by ring⟩

theorem tether₂_length (J : Packing.Instance) : (tether₂ J).length = side J - 2 := by
  simp [tether₂]

theorem tether₂_isChain (J : Packing.Instance) : (tether₂ J).IsChain cubicLattice.Adj :=
  line_isChain _ (adj_zero_pt.mpr (by norm_num)) _

theorem tether₂_head? (J : Packing.Instance) :
    (tether₂ J).head? = some (pt (N J - 1) (-1) 1) := by
  have h3 : 3 ≤ side J := by unfold side; omega
  exact line_head? _ _ (by omega)

theorem tether₂_getLast? (J : Packing.Instance) :
    (tether₂ J).getLast? = some (pt (N J - 1) (-1) (N J - 1)) := by
  have h3 : 3 ≤ side J := by unfold side; omega
  rw [tether₂, line_pt_getLast? _ _ _ _ _ _ (by omega), Option.some_inj, pt_eq_iff]
  have := side_cast J
  push_cast [Nat.cast_sub (show 2 ≤ side J by omega)]
  refine ⟨by ring, by ring, by linarith⟩

/-! ### The separators with their tethers -/

theorem innerMid_length (J : Packing.Instance) (j : ℕ) :
    (innerMid J j).length = J.capacity + 4 := by
  simp [innerMid]

namespace LayoutPlain

theorem tokSites_sepToken (J : Packing.Instance) (j : ℕ) :
    tokSites [sepToken J j] =
      [pt (sepCol J j) 0 (-1), pt (sepCol J j) 0 0, pt (sepCol J j) (-1) 0] := by
  simp [tokSites, Token.sites, sepToken]

/-- The first `j` tethers and the separators `0, …, j`. -/
def pre (J : Packing.Instance) (m : ℕ) : List Site :=
  tokSites [sepToken J 0] ++
    (List.range m).flatMap fun j => innerMid J j ++ tokSites [sepToken J (j + 1)]

theorem pre_succ (J : Packing.Instance) (m : ℕ) :
    pre J (m + 1) = pre J m ++ (innerMid J m ++ tokSites [sepToken J (m + 1)]) := by
  simp only [pre, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.append_assoc]

theorem seg_eq (J : Packing.Instance) (j : ℕ) :
    innerMid J j ++ tokSites [sepToken J (j + 1)] =
      line (pt (sepCol J j) (-1) (-1)) (pt 1 0 0) (J.capacity + 1) ++
        [pt (sepCol J (j + 1) - 1) (-1) (-2), pt (sepCol J (j + 1)) (-1) (-2),
          pt (sepCol J (j + 1)) 0 (-2), pt (sepCol J (j + 1)) 0 (-1), pt (sepCol J (j + 1)) 0 0,
          pt (sepCol J (j + 1)) (-1) 0] := by
  rw [innerMid, tokSites_sepToken]
  simp

theorem seg_isChain (J : Packing.Instance) (j : ℕ) :
    (innerMid J j ++ tokSites [sepToken J (j + 1)]).IsChain cubicLattice.Adj := by
  have hs := sepCol_succ J j
  rw [seg_eq]
  refine List.IsChain.append (line_isChain _ (adj_zero_pt.mpr (by norm_num)) _) ?_ ?_
  · simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true, adj_pt]
    omega
  · intro x hx y hy
    rw [line_pt_getLast? _ _ _ _ _ _ (by omega), Option.mem_some_iff] at hx
    simp only [List.head?_cons, Option.mem_some_iff] at hy
    subst hx hy
    rw [adj_pt]
    push_cast
    omega

theorem seg_head? (J : Packing.Instance) (j : ℕ) :
    (innerMid J j ++ tokSites [sepToken J (j + 1)]).head? = some (pt (sepCol J j) (-1) (-1)) := by
  rw [seg_eq, List.head?_append, line_head? _ _ (by omega)]
  rfl

theorem seg_getLast? (J : Packing.Instance) (j : ℕ) :
    (innerMid J j ++ tokSites [sepToken J (j + 1)]).getLast? =
      some (pt (sepCol J (j + 1)) (-1) 0) := by
  rw [seg_eq]
  simp

theorem pre_spec (J : Packing.Instance) (m : ℕ) :
    (pre J m).IsChain cubicLattice.Adj ∧ (pre J m).getLast? = some (pt (sepCol J m) (-1) 0) ∧
      (pre J m).head? = some (pt 1 0 (-1)) := by
  induction m with
  | zero =>
    simp only [pre, List.range_zero, List.flatMap_nil, List.append_nil, tokSites_sepToken,
      sepCol_zero]
    refine ⟨?_, by simp, by simp⟩
    simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true, adj_pt]
    omega
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [pre_succ]
    refine ⟨List.IsChain.append h1 (seg_isChain J m) ?_, ?_, ?_⟩
    · intro x hx y hy
      rw [h2, Option.mem_some_iff] at hx
      rw [seg_head?, Option.mem_some_iff] at hy
      subst hx hy
      rw [adj_pt]
      omega
    · rw [List.getLast?_append, seg_getLast?]
      rfl
    · rw [List.head?_append, h3]
      rfl

end LayoutPlain

theorem sepPart_isChain (J : Packing.Instance) : (sepPart J).IsChain cubicLattice.Adj :=
  (pre_spec J J.bins).1

theorem sepPart_head? (J : Packing.Instance) : (sepPart J).head? = some (pt 1 0 (-1)) :=
  (pre_spec J J.bins).2.2

theorem sepPart_getLast? (J : Packing.Instance) :
    (sepPart J).getLast? = some (pt (N J - 1) (-1) 0) := by
  rw [← sepCol_bins]
  exact (pre_spec J J.bins).2.1

namespace LayoutPlain

theorem forall₂_flatMap {α β γ : Type*} {R : β → γ → Prop} {l : List α} {f : α → List β}
    {g : α → List γ} (h : ∀ a ∈ l, List.Forall₂ R (f a) (g a)) :
    List.Forall₂ R (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact List.rel_append (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

end LayoutPlain

/-- The separators and their tethers spell `PHP (P^(B+4) PHP)^m`. -/
theorem sepPart_fits (J : Packing.Instance) :
    List.Forall₂ (Fits (side J)) (sepPart J)
      (tokWord 1 ++ (List.range J.bins).flatMap fun _ =>
        List.replicate (J.capacity + 4) P ++ tokWord 1) := by
  have hn := side_cast J
  unfold sepPart
  refine List.rel_append ?_ (forall₂_flatMap ?_)
  · exact tokSites_fits (ts := [sepToken J 0]) (fun t ht => by
      rw [List.mem_singleton] at ht
      subst ht
      exact sepToken_valid J (Nat.zero_le _))
  · intro j hj
    rw [List.mem_range] at hj
    refine List.rel_append ?_ ?_
    · have := fits_replicate_P (n := side J) (ps := innerMid J j) (fun p hp => by
        obtain ⟨x, y, z, rfl, h⟩ := mem_innerMid hp
        rw [pt_mem_Q]
        omega)
      rwa [innerMid_length] at this
    · exact tokSites_fits (ts := [sepToken J (j + 1)]) (fun t ht => by
        rw [List.mem_singleton] at ht
        subst ht
        exact sepToken_valid J (by omega))

/-- The same sites, with the tokens first and the tethers after them. -/
theorem sepPart_perm (J : Packing.Instance) :
    (sepPart J).Perm (tokSites ((List.range (J.bins + 1)).map (sepToken J)) ++
      (List.range J.bins).flatMap (innerMid J)) := by
  have h : tokSites ((List.range (J.bins + 1)).map (sepToken J)) =
      tokSites [sepToken J 0] ++
        (List.range J.bins).flatMap fun j => tokSites [sepToken J (j + 1)] := by
    rw [List.range_succ_eq_map, List.map_cons]
    simp [tokSites, List.flatMap_map]
  rw [h, List.append_assoc]
  unfold sepPart
  refine List.Perm.append_left _ ?_
  exact (List.flatMap_append_perm _ _ _).symm.trans List.perm_append_comm

end ProteinFolding.Shelf

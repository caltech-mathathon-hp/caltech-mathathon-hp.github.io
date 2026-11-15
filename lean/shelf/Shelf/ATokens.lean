import Shelf.LayoutTokens

/-!
# The long run `A`

Table 1 lays the run `A` on nine edges of the cube and the eight corners between
them. It starts at `(0, N, N - 1)`, goes down the edge `(0, N, z)` and then
through the corners

  `(0,N,0)`, `(0,0,0)`, `(0,0,N)`, `(0,N,N)`, `(N,N,N)`, `(N,0,N)`, `(N,0,0)`, `(N,N,0)`

up to `(N, N, N - 1)`. The three edges it leaves free are `(x, N, 0)`, `(x, 0, 0)`
and `(x, 0, N)`.

Each of the nine edges has `n - 2` inner nodes, an even number. So if the `P`
before the first node of an edge hangs on the side `ν`, and the `P`'s alternate
between the two outer sides `ν`, `ν'` of the edge, then the `P` after its last
node hangs on the side `ν` again. A corner takes the side of the edge before it
and the side of the edge after it.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue CubicPackingGeometry Layout

/-- The `n - 2` inner nodes of an edge, from `a` in direction `e`: the `P` before the
first node and the `P` after the last one hang on the side `ν`. -/
def aEdge (J : Packing.Instance) (a e ν ν' : Site) : List Token :=
  altRun a e (side J - 2) ν ν'

/-- The tokens of the run `A`. -/
def aTokens (J : Packing.Instance) : List Token :=
  aEdge J (pt 0 (N J) (N J - 1)) (pt 0 0 (-1)) (pt 0 1 0) (pt (-1) 0 0) ++
  [⟨pt 0 (N J) 0, pt 0 1 0, pt 0 0 (-1)⟩] ++
  aEdge J (pt 0 (N J - 1) 0) (pt 0 (-1) 0) (pt 0 0 (-1)) (pt (-1) 0 0) ++
  [⟨pt 0 0 0, pt 0 0 (-1), pt (-1) 0 0⟩] ++
  aEdge J (pt 0 0 1) (pt 0 0 1) (pt (-1) 0 0) (pt 0 (-1) 0) ++
  [⟨pt 0 0 (N J), pt (-1) 0 0, pt 0 0 1⟩] ++
  aEdge J (pt 0 1 (N J)) (pt 0 1 0) (pt 0 0 1) (pt (-1) 0 0) ++
  [⟨pt 0 (N J) (N J), pt 0 0 1, pt 0 1 0⟩] ++
  aEdge J (pt 1 (N J) (N J)) (pt 1 0 0) (pt 0 1 0) (pt 0 0 1) ++
  [⟨pt (N J) (N J) (N J), pt 0 1 0, pt 1 0 0⟩] ++
  aEdge J (pt (N J) (N J - 1) (N J)) (pt 0 (-1) 0) (pt 1 0 0) (pt 0 0 1) ++
  [⟨pt (N J) 0 (N J), pt 1 0 0, pt 0 (-1) 0⟩] ++
  aEdge J (pt (N J) 0 (N J - 1)) (pt 0 0 (-1)) (pt 0 (-1) 0) (pt 1 0 0) ++
  [⟨pt (N J) 0 0, pt 0 (-1) 0, pt 0 0 (-1)⟩] ++
  aEdge J (pt (N J) 1 0) (pt 0 1 0) (pt 0 0 (-1)) (pt 1 0 0) ++
  [⟨pt (N J) (N J) 0, pt 0 0 (-1), pt 1 0 0⟩] ++
  aEdge J (pt (N J) (N J) 1) (pt 0 0 1) (pt 1 0 0) (pt 0 1 0)


namespace ATokens

/-- A point of a row, written by its coordinates. -/
theorem row_pt (x y z u v w s : ℤ) :
    (fun k => pt x y z k + s * pt u v w k) = pt (x + s * u) (y + s * v) (z + s * w) :=
  site_ext rfl rfl rfl

theorem three_le_side (J : Packing.Instance) : 3 ≤ side J := by
  unfold side; exact Nat.le_add_left _ _

/-- To check a property of every token of a row, check it for both choices of the sides at
every node. -/
theorem forall_altRun {a e ν ν' : Site} {r : ℕ} {P : Token → Prop}
    (h : ∀ t : ℕ, t < r → P ⟨fun k => a k + (t : ℤ) * e k, ν, ν'⟩ ∧
      P ⟨fun k => a k + (t : ℤ) * e k, ν', ν⟩) :
    ∀ tk ∈ altRun a e r ν ν', P tk := by
  intro tk htk
  obtain ⟨t, ht, rfl⟩ := mem_altRun.mp htk
  split_ifs
  · exact (h t ht).1
  · exact (h t ht).2

/-- The same, for a row given by coordinates. -/
theorem forall_altRun_pt {x y z u v w : ℤ} {ν ν' : Site} {r : ℕ} {P : Token → Prop}
    (h : ∀ t : ℕ, t < r →
      P ⟨pt (x + (t : ℤ) * u) (y + (t : ℤ) * v) (z + (t : ℤ) * w), ν, ν'⟩ ∧
      P ⟨pt (x + (t : ℤ) * u) (y + (t : ℤ) * v) (z + (t : ℤ) * w), ν', ν⟩) :
    ∀ tk ∈ altRun (pt x y z) (pt u v w) r ν ν', P tk := by
  apply forall_altRun
  intro t ht
  rw [row_pt]
  exact h t ht

/-- A token given by coordinates is valid as soon as the arithmetic says so. -/
theorem valid_pt {n : ℕ} {x y z a b c a' b' c' : ℤ}
    (hm : (0 ≤ x ∧ x < n) ∧ (0 ≤ y ∧ y < n) ∧ (0 ≤ z ∧ z < n))
    (ha : ¬ ((0 ≤ x + a ∧ x + a < n) ∧ (0 ≤ y + b ∧ y + b < n) ∧ (0 ≤ z + c ∧ z + c < n)))
    (hb : ¬ ((0 ≤ x + a' ∧ x + a' < n) ∧ (0 ≤ y + b' ∧ y + b' < n) ∧
      (0 ≤ z + c' ∧ z + c' < n)))
    (hau : a.natAbs + b.natAbs + c.natAbs = 1) (hbu : a'.natAbs + b'.natAbs + c'.natAbs = 1)
    (hne : ¬ (a = a' ∧ b = b' ∧ c = c')) :
    Token.Valid n ⟨pt x y z, pt a b c, pt a' b' c'⟩ where
  mem := pt_mem_Q.mpr hm
  a_out := by simp only [pt_add]; rw [pt_mem_Q]; exact ha
  b_out := by simp only [pt_add]; rw [pt_mem_Q]; exact hb
  a_adj := by simp only [pt_add]; rw [adj_pt]; simpa using hau
  b_adj := by simp only [pt_add]; rw [adj_pt]; simpa using hbu
  ne := by rw [Ne, pt_eq_iff]; exact hne

/-- A point of the cube with two coordinates in `{0, N}` is on the skeleton. -/
theorem skel_pt {n : ℕ} {x y z : ℤ}
    (hm : (0 ≤ x ∧ x < n) ∧ (0 ≤ y ∧ y < n) ∧ (0 ≤ z ∧ z < n))
    (h : ((x = 0 ∨ x + 1 = n) ∧ (y = 0 ∨ y + 1 = n)) ∨ ((x = 0 ∨ x + 1 = n) ∧
      (z = 0 ∨ z + 1 = n)) ∨ ((y = 0 ∨ y + 1 = n) ∧ (z = 0 ∨ z + 1 = n))) :
    EdgeSkeleton 0 n (pt x y z) := by
  refine ⟨pt_mem_Q.mpr hm, ?_⟩
  simp only [BoundaryCoordinate, Pi.zero_apply, zero_add]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, 1, by decide, h1, h2⟩
  · exact ⟨0, 2, by decide, h1, h2⟩
  · exact ⟨1, 2, by decide, h1, h2⟩

theorem third_pt {x y z M : ℤ} (h : (x = 0 ∨ x = M) ∨ (y = M ∧ z = M)) :
    (pt x y z 0 = 0 ∨ pt x y z 0 = M) ∨ (pt x y z 1 = M ∧ pt x y z 2 = M) := h

/-- Adding a row of tokens to a chain of linked tokens. -/
theorem chain_append_edge {L : List Token} {s : Token} {a e ν ν' : Site} {r : ℕ}
    (hL : L.IsChain Linked) (hs : L.getLast? = some s) (hl : Linked s ⟨a, ν, ν'⟩)
    (he : cubicLattice.Adj 0 e) (hr : 0 < r) (heven : Even r) :
    (L ++ altRun a e r ν ν').IsChain Linked ∧
      (L ++ altRun a e r ν ν').getLast? =
        some ⟨fun k => a k + ((r : ℤ) - 1) * e k, ν', ν⟩ := by
  have hne : altRun a e r ν ν' ≠ [] := by
    intro h; have := altRun_length a e r ν ν'; rw [h] at this; simp at this; omega
  refine ⟨List.IsChain.append hL (altRun_isChain a he r ν ν') ?_, ?_⟩
  · intro x hx y hy
    rw [hs, Option.mem_some_iff] at hx
    rw [altRun_head? a e hr, Option.mem_some_iff] at hy
    subst hx hy; exact hl
  · rw [List.getLast?_append_of_ne_nil _ hne, altRun_getLast?_even a e hr heven]

/-- Adding one token to a chain of linked tokens. -/
theorem chain_snoc {L : List Token} {s C : Token} (hL : L.IsChain Linked)
    (hs : L.getLast? = some s) (hl : Linked s C) :
    (L ++ [C]).IsChain Linked ∧ (L ++ [C]).getLast? = some C := by
  refine ⟨List.IsChain.append hL (List.IsChain.singleton C) ?_, by simp⟩
  intro x hx y hy
  rw [hs, Option.mem_some_iff] at hx
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst hx hy; exact hl

/-- A chain of linked tokens that ends with the token `s`. -/
def ChainEnd (L : List Token) (s : Token) : Prop := L.IsChain Linked ∧ L.getLast? = some s

theorem ChainEnd.isChain {L : List Token} {s : Token} (h : ChainEnd L s) : L.IsChain Linked :=
  h.1

theorem adj_zero_pt {u v w : ℤ} (h : u.natAbs + v.natAbs + w.natAbs = 1) :
    cubicLattice.Adj 0 (pt u v w) := by
  have : (0 : Site) = pt 0 0 0 := site_ext rfl rfl rfl
  rw [this, adj_pt]; simpa using h

theorem last_pt (x y z u v w : ℤ) (r : ℕ) (ν ν' : Site) :
    (⟨fun k => pt x y z k + ((r : ℤ) - 1) * pt u v w k, ν', ν⟩ : Token) =
      ⟨pt (x + ((r : ℤ) - 1) * u) (y + ((r : ℤ) - 1) * v) (z + ((r : ℤ) - 1) * w), ν', ν⟩ := by
  rw [row_pt]

theorem edge_start {x y z u v w : ℤ} {r : ℕ} {ν ν' : Site}
    (he : u.natAbs + v.natAbs + w.natAbs = 1) (hr : 0 < r) (heven : Even r) :
    ChainEnd (altRun (pt x y z) (pt u v w) r ν ν')
      ⟨pt (x + ((r : ℤ) - 1) * u) (y + ((r : ℤ) - 1) * v) (z + ((r : ℤ) - 1) * w), ν', ν⟩ := by
  refine ⟨altRun_isChain _ (adj_zero_pt he) r ν ν', ?_⟩
  rw [altRun_getLast?_even _ _ hr heven, last_pt]

theorem edge_step {L : List Token} {s : Token} {x y z u v w : ℤ} {r : ℕ} {ν ν' : Site}
    (hL : ChainEnd L s) (hl : Linked s ⟨pt x y z, ν, ν'⟩)
    (he : u.natAbs + v.natAbs + w.natAbs = 1) (hr : 0 < r) (heven : Even r) :
    ChainEnd (L ++ altRun (pt x y z) (pt u v w) r ν ν')
      ⟨pt (x + ((r : ℤ) - 1) * u) (y + ((r : ℤ) - 1) * v) (z + ((r : ℤ) - 1) * w), ν', ν⟩ := by
  have := chain_append_edge hL.1 hL.2 hl (adj_zero_pt he) hr heven
  rw [last_pt] at this
  exact this

theorem snoc_step {L : List Token} {s C : Token} (hL : ChainEnd L s) (hl : Linked s C) :
    ChainEnd (L ++ [C]) C :=
  chain_snoc hL.1 hL.2 hl

/-- The centres of a row, with the box they lie in. -/
theorem line_box {x y z u v w : ℤ} {r : ℕ} (hu : u.natAbs + v.natAbs + w.natAbs = 1) :
    (line (pt x y z) (pt u v w) r).Nodup ∧ ∀ p ∈ line (pt x y z) (pt u v w) r,
      (min x (x + ((r : ℤ) - 1) * u) ≤ p 0 ∧ p 0 ≤ max x (x + ((r : ℤ) - 1) * u)) ∧
      (min y (y + ((r : ℤ) - 1) * v) ≤ p 1 ∧ p 1 ≤ max y (y + ((r : ℤ) - 1) * v)) ∧
      (min z (z + ((r : ℤ) - 1) * w) ≤ p 2 ∧ p 2 ≤ max z (z + ((r : ℤ) - 1) * w)) := by
  refine ⟨line_nodup _ (fun h => ?_) r, ?_⟩
  · have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
    simp at h0 h1 h2; subst h0 h1 h2; simp at hu
  · intro p hp
    obtain ⟨t, ht, hpk⟩ := mem_line.mp hp
    have h0 := hpk 0; have h1 := hpk 1; have h2 := hpk 2
    simp only [pt_apply_zero, pt_apply_one, pt_apply_two] at h0 h1 h2
    rw [h0, h1, h2]
    have hu' : u = -1 ∨ u = 0 ∨ u = 1 := by omega
    have hv' : v = -1 ∨ v = 0 ∨ v = 1 := by omega
    have hw' : w = -1 ∨ w = 0 ∨ w = 1 := by omega
    rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl <;>
      rcases hw' with rfl | rfl | rfl <;> simp only [mul_neg, mul_one, mul_zero] <;> omega

theorem single_box (x y z : ℤ) :
    [pt x y z].Nodup ∧ ∀ p ∈ [pt x y z], p 0 = x ∧ p 1 = y ∧ p 2 = z := by
  refine ⟨List.nodup_singleton _, ?_⟩
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp; simp

theorem nodup_step {L l : List Site} {P Q : Site → Prop} (h : L.Nodup ∧ ∀ p ∈ L, P p)
    (hl : l.Nodup ∧ ∀ p ∈ l, Q p) (hPQ : ∀ p, P p → Q p → False) :
    (L ++ l).Nodup ∧ ∀ p ∈ L ++ l, P p ∨ Q p := by
  refine ⟨List.nodup_append.mpr ⟨h.1, hl.1, ?_⟩, ?_⟩
  · intro p hp q hq hpq
    subst hpq
    exact hPQ p (h.2 p hp) (hl.2 p hq)
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact Or.inl (h.2 p hp)
    · exact Or.inr (hl.2 p hp)

theorem nodup_of_spec {L : List Site} {P : Site → Prop} (h : L.Nodup ∧ ∀ p ∈ L, P p) :
    L.Nodup := h.1

end ATokens

open ATokens

theorem aTokens_length (J : Packing.Instance) : (aTokens J).length = 9 * side J - 10 := by
  have h3 := three_le_side J
  simp only [aTokens, aEdge, List.length_append, altRun_length, List.length_singleton]
  omega

theorem aTokens_valid (J : Packing.Instance) : ∀ t ∈ aTokens J, t.Valid (side J) := by
  have h3 := three_le_side J
  intro tk htk
  simp only [aTokens, List.mem_append, List.mem_singleton, or_assoc] at htk
  rcases htk with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals first
    | (subst h; apply valid_pt <;> (try simp only [N]) <;> omega)
    | (revert tk; unfold aEdge; apply forall_altRun_pt; intro t ht;
       (try simp only [mul_neg, mul_one, mul_zero, add_zero, N]);
       constructor <;> apply valid_pt <;> omega)

theorem aTokens_linked {J : Packing.Instance} (hJ : Normalised J) :
    (aTokens J).IsChain Linked := by
  have h3 := ten_le_side hJ
  have hN : N J = (side J : ℤ) - 1 := rfl
  have hr : 0 < side J - 2 := by omega
  have hev : Even (side J - 2) := by
    obtain ⟨k, hk⟩ := side_even hJ
    exact ⟨k - 1, by omega⟩
  unfold aTokens aEdge
  refine ChainEnd.isChain (edge_step (snoc_step (edge_step (snoc_step (edge_step (snoc_step (edge_step (snoc_step (edge_step (snoc_step (edge_step (snoc_step (edge_step (snoc_step (edge_step (snoc_step (edge_start ?_ ?_ ?_) ?_) ?_ ?_ ?_ ?_) ?_) ?_ ?_ ?_ ?_) ?_) ?_ ?_ ?_ ?_) ?_) ?_ ?_ ?_ ?_) ?_) ?_ ?_ ?_ ?_) ?_) ?_ ?_ ?_ ?_) ?_) ?_ ?_ ?_ ?_) ?_) ?_ ?_ ?_ ?_)
  all_goals first
    | exact hr
    | exact hev
    | omega
    | (refine ⟨rfl, adj_pt.mpr ?_⟩; (try simp only [mul_neg, mul_one, mul_zero, add_zero]); omega)

theorem aTokens_nodup (J : Packing.Instance) : ((aTokens J).map Token.c).Nodup := by
  have h3 := three_le_side J
  have hN : N J = (side J : ℤ) - 1 := rfl
  simp only [aTokens, aEdge, List.map_append, altRun_centres, List.map_cons, List.map_nil]
  refine nodup_of_spec (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (nodup_step (line_box ?_) (single_box _ _ _) ?_) (line_box ?_) ?_) (single_box _ _ _) ?_) (line_box ?_) ?_) (single_box _ _ _) ?_) (line_box ?_) ?_) (single_box _ _ _) ?_) (line_box ?_) ?_) (single_box _ _ _) ?_) (line_box ?_) ?_) (single_box _ _ _) ?_) (line_box ?_) ?_) (single_box _ _ _) ?_) (line_box ?_) ?_) (single_box _ _ _) ?_) (line_box ?_) ?_)
  all_goals omega

/-- The centres are on the skeleton, and not on the inside of the three free edges. -/
theorem aTokens_centres (J : Packing.Instance) : ∀ t ∈ aTokens J,
    EdgeSkeleton 0 (side J) t.c ∧
      ((t.c 0 = 0 ∨ t.c 0 = N J) ∨ (t.c 1 = N J ∧ t.c 2 = N J)) := by
  have h3 := three_le_side J
  have hN : N J = (side J : ℤ) - 1 := rfl
  intro tk htk
  simp only [aTokens, List.mem_append, List.mem_singleton, or_assoc] at htk
  rcases htk with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals first
    | (subst h; dsimp only; refine ⟨skel_pt ?_ ?_, third_pt ?_⟩ <;> omega)
    | (revert tk; unfold aEdge; apply forall_altRun_pt; intro t ht;
       simp only [mul_neg, mul_one, mul_zero, add_zero];
       constructor <;> refine ⟨skel_pt ?_ ?_, third_pt ?_⟩ <;> omega)

theorem aTokens_head? (J : Packing.Instance) :
    (tokSites (aTokens J)).head? = some (aIn J) := by
  have h3 := three_le_side J
  have hh : (aTokens J).head? = some ⟨pt 0 (N J) (N J - 1), pt 0 1 0, pt (-1) 0 0⟩ := by
    simp only [aTokens, aEdge, List.head?_append, altRun_head? _ _ (show 0 < side J - 2 by omega),
      Option.some_or]
  obtain ⟨tl, htl⟩ := List.head?_eq_some_iff.mp hh
  rw [htl, tokSites_head?, aIn, pt_add, Option.some_inj, pt_eq_iff]
  omega

theorem aTokens_getLast? {J : Packing.Instance} (hJ : Normalised J) :
    (tokSites (aTokens J)).getLast? = some (aOut J) := by
  have h3 := ten_le_side hJ
  have hev : Even (side J - 2) := by
    obtain ⟨k, hk⟩ := side_even hJ
    exact ⟨k - 1, by omega⟩
  have hl : (aTokens J).getLast? = some ⟨pt (N J + ((((side J - 2 : ℕ) : ℤ)) - 1) * 0)
      (N J + ((((side J - 2 : ℕ) : ℤ)) - 1) * 0) (1 + ((((side J - 2 : ℕ) : ℤ)) - 1) * 1),
      pt 0 1 0, pt 1 0 0⟩ := by
    simp only [aTokens, aEdge, List.getLast?_append,
      altRun_getLast?_even _ _ (show 0 < side J - 2 by omega) hev, last_pt, Option.some_or]
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
  rw [hys, tokSites_getLast?, aOut, pt_add, Option.some_inj, pt_eq_iff, N]
  simp only [mul_zero, mul_one]
  omega

end ProteinFolding.Shelf

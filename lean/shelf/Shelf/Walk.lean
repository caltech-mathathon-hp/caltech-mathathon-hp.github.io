import Shelf.Sites
import Shelf.Tether
import Shelf.Word
import ProteinFolding.Cubic.Proofs.PackingCountCompleteness

/-!
# Walks and tokens

The foundation of Section 5 of the paper, where we build a fold from a packing. A fold
is given as a list of sites, one per letter (`perfect_of_walk`). Since
`P D(r) P = (PHP)^r`, every isolated `H` is laid together with the `P` before it and
the `P` after it; we call these three sites a token. Lemma 13 of the paper ("laying a
dense run") becomes `tokSites_isChain` and `tokSites_nodup`, and `altRun` lays tokens
along a row with the normals alternating, as in Table 1.
-/

namespace ProteinFolding.Shelf
open ProteinFolding Residue

/-! ## A fold given by a list of sites -/

/-- The letter `x` may sit at the site `p`: an `H` inside the cube, a `P` outside. -/
def Fits (n : ℕ) (p : Site) (x : Residue) : Prop := x = H ↔ p ∈ Q n

theorem fits_H {n : ℕ} {p : Site} (hp : p ∈ Q n) : Fits n p H :=
  ⟨fun _ => hp, fun _ => rfl⟩

theorem fits_P {n : ℕ} {p : Site} (hp : p ∉ Q n) : Fits n p P :=
  ⟨fun h => absurd h (by decide), fun h => absurd h hp⟩

/-- A list of sites for the letters of `S`, pairwise different, consecutive ones adjacent,
with the `H`'s inside the cube `Q n` and the `P`'s outside, is a perfect fold as soon as `S`
has `n³` letters `H`. (We never have to show that the `H`'s cover the cube.) -/
theorem perfect_of_walk {S : Sequence} {n : ℕ} (w : List Site)
    (hfit : List.Forall₂ (Fits n) w S) (hnd : w.Nodup)
    (hchain : w.IsChain cubicLattice.Adj) (hcount : hydrophobicCount S = n ^ 3) :
    PerfectHPStringFold S n := by
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp hfit
  let f : Fold cubicLattice S.length :=
    { pos := fun i => w[i.val]'(by have := i.isLt; omega)
      injective_pos := by
        intro i j h
        exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h)
      consecutive := by
        intro i j hij
        have := List.isChain_iff_get.mp hchain i.val (by have := j.isLt; omega)
        simp only [List.get_eq_getElem] at this
        simp only [← hij]
        exact this }
  refine ⟨hcount, f, CubicGeometry.packsCube_of_inside_of_count S f 0 n hcount ?_⟩
  rintro p ⟨i, hi, rfl⟩
  exact (hget i.val (by have := i.isLt; omega) i.isLt).mp hi

theorem fits_replicate_P {n : ℕ} {ps : List Site} (h : ∀ p ∈ ps, p ∉ Q n) :
    List.Forall₂ (Fits n) ps (List.replicate ps.length P) := by
  induction ps with
  | nil => exact List.Forall₂.nil
  | cons p ps ih =>
    rw [List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons (fits_P (h p (by simp)))
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem fits_replicate_H {n : ℕ} {ps : List Site} (h : ∀ p ∈ ps, p ∈ Q n) :
    List.Forall₂ (Fits n) ps (List.replicate ps.length H) := by
  induction ps with
  | nil => exact List.Forall₂.nil
  | cons p ps ih =>
    rw [List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons (fits_H (h p (by simp)))
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

/-! ## Tokens -/

/-- An isolated `H` together with the `P` before it and the `P` after it: the `H` sits at
`c`, the two `P`'s at `c + a` and `c + b`. -/
structure Token where
  c : Site
  a : Site
  b : Site

/-- The three sites of a token, in the order of the string `PHP`. -/
def Token.sites (t : Token) : List Site := [t.c + t.a, t.c, t.c + t.b]

/-- The `H` is in the cube, and `a ≠ b` are unit vectors that point out of the cube at `c`
(outward normals, in the words of the paper). -/
structure Token.Valid (n : ℕ) (t : Token) : Prop where
  mem : t.c ∈ Q n
  a_out : t.c + t.a ∉ Q n
  b_out : t.c + t.b ∉ Q n
  a_adj : cubicLattice.Adj t.c (t.c + t.a)
  b_adj : cubicLattice.Adj t.c (t.c + t.b)
  ne : t.a ≠ t.b

/-- The sites of a list of tokens; they spell `(PHP)^r`. -/
def tokSites (ts : List Token) : List Site := ts.flatMap Token.sites

/-- Two consecutive tokens fit together: the `P` after the first and the `P` before the
second hang on the same side (this is one link of the paper), and the centres are adjacent. -/
def Linked (s t : Token) : Prop := t.a = s.b ∧ cubicLattice.Adj s.c t.c

theorem mem_tokSites {ts : List Token} {p : Site} :
    p ∈ tokSites ts ↔ ∃ t ∈ ts, p = t.c + t.a ∨ p = t.c ∨ p = t.c + t.b := by
  simp [tokSites, Token.sites]

theorem tokSites_nil : tokSites [] = [] := rfl

theorem tokSites_cons (t : Token) (ts : List Token) :
    tokSites (t :: ts) = t.sites ++ tokSites ts := by
  simp [tokSites]

theorem tokSites_length (ts : List Token) : (tokSites ts).length = 3 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [tokSites_cons, List.length_append, ih]
    simp [Token.sites]
    omega

theorem tokSites_append (ts ts' : List Token) :
    tokSites (ts ++ ts') = tokSites ts ++ tokSites ts' := by
  simp [tokSites]

theorem tokSites_head? (t : Token) (ts : List Token) :
    (tokSites (t :: ts)).head? = some (t.c + t.a) := by
  simp [tokSites, Token.sites]

theorem tokSites_getLast? (ts : List Token) (t : Token) :
    (tokSites (ts ++ [t])).getLast? = some (t.c + t.b) := by
  rw [tokSites_append, tokSites_cons, tokSites_nil, List.append_nil, List.getLast?_append]
  simp [Token.sites]

/-- Adjacency is invariant under translation. -/
theorem adj_add_right {x y : Site} (h : cubicLattice.Adj x y) (v : Site) :
    cubicLattice.Adj (x + v) (y + v) := by
  rw [adj_iff, latticeDistance_eq] at h ⊢
  simpa using h

/-- A point of the cube is its own clamp. -/
theorem clamp_eq_self {n : ℕ} {u : Site} (hu : u ∈ Q n) : clamp n u = u := by
  rw [mem_Q] at hu
  funext k
  have := hu k
  simp only [clamp]
  omega

/-- All three sites of a valid token are clamped to its centre (Lemma 5(b)). -/
theorem Token.Valid.clamp_of_mem {n : ℕ} {t : Token} (hv : t.Valid n) {p : Site}
    (hp : p ∈ t.sites) : clamp n p = t.c := by
  simp only [Token.sites, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact clamp_eq_of_adj hv.mem hv.a_out hv.a_adj
  · exact clamp_eq_self hv.mem
  · exact clamp_eq_of_adj hv.mem hv.b_out hv.b_adj

theorem Token.Valid.sites_nodup {n : ℕ} {t : Token} (hv : t.Valid n) : t.sites.Nodup := by
  have h1 : t.c + t.a ≠ t.c := fun h => hv.a_out (by rw [h]; exact hv.mem)
  have h2 : t.c ≠ t.c + t.b := fun h => hv.b_out (by rw [← h]; exact hv.mem)
  have h3 : t.c + t.a ≠ t.c + t.b := fun h => hv.ne (add_left_cancel h)
  simp [Token.sites, h1, h2, h3]

theorem Token.Valid.sites_isChain {n : ℕ} {t : Token} (hv : t.Valid n) :
    t.sites.IsChain cubicLattice.Adj := by
  simp only [Token.sites, List.isChain_cons_cons, List.IsChain.singleton, and_true]
  exact ⟨hv.a_adj.symm, hv.b_adj⟩

/-- Every site of a valid token is at distance at most 1 from its centre. -/
theorem Token.Valid.latticeDistance_le {n : ℕ} {t : Token} (hv : t.Valid n) {p : Site}
    (hp : p ∈ t.sites) : latticeDistance t.c p ≤ 1 := by
  simp only [Token.sites, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact le_of_eq hv.a_adj
  · simp [latticeDistance_self]
  · exact le_of_eq hv.b_adj

/-- Lemma 13, adjacency: consecutive sites of linked tokens are adjacent. -/
theorem tokSites_isChain {n : ℕ} {ts : List Token} (hv : ∀ t ∈ ts, t.Valid n)
    (hl : ts.IsChain Linked) : (tokSites ts).IsChain cubicLattice.Adj := by
  induction ts with
  | nil => exact List.IsChain.nil
  | cons t ts ih =>
    have ht := hv t (by simp)
    have ih' := ih (fun s hs => hv s (by simp [hs])) hl.tail
    rw [tokSites_cons]
    refine List.IsChain.append ht.sites_isChain ih' ?_
    intro x hx y hy
    cases ts with
    | nil => simp [tokSites] at hy
    | cons s ts =>
      have hts : Linked t s := (List.isChain_cons_cons.mp hl).1
      simp [Token.sites] at hx
      rw [tokSites_head?, Option.mem_some_iff] at hy
      subst hx hy
      rw [hts.1]
      exact adj_add_right hts.2 _

/-- Lemma 13, distinctness: tokens with different centres have different sites (Lemma 5(b)). -/
theorem tokSites_nodup {n : ℕ} {ts : List Token} (hv : ∀ t ∈ ts, t.Valid n)
    (hc : (ts.map Token.c).Nodup) : (tokSites ts).Nodup := by
  unfold tokSites
  rw [List.nodup_flatMap]
  refine ⟨fun t ht => (hv t ht).sites_nodup, ?_⟩
  refine (List.pairwise_map.mp hc).imp_of_mem ?_
  intro s t hs ht hne p hps hpt
  exact hne (((hv s hs).clamp_of_mem hps).symm.trans ((hv t ht).clamp_of_mem hpt))

theorem tokSites_fits {n : ℕ} {ts : List Token} (hv : ∀ t ∈ ts, t.Valid n) :
    List.Forall₂ (Fits n) (tokSites ts) (List.replicate ts.length [P, H, P]).flatten := by
  induction ts with
  | nil => exact List.Forall₂.nil
  | cons t ts ih =>
    have ht := hv t (by simp)
    have ih' := ih (fun s hs => hv s (by simp [hs]))
    rw [tokSites_cons, List.length_cons, List.replicate_succ, List.flatten_cons]
    simp only [Token.sites, List.cons_append, List.nil_append]
    exact .cons (fits_P ht.a_out) (.cons (fits_H ht.mem) (.cons (fits_P ht.b_out) ih'))

/-- A site that is at distance at least 2 from every centre is not a token site. -/
theorem not_mem_tokSites {n : ℕ} {ts : List Token} (hv : ∀ t ∈ ts, t.Valid n) {p : Site}
    (h : ∀ t ∈ ts, 2 ≤ latticeDistance t.c p) : p ∉ tokSites ts := by
  intro hp
  unfold tokSites at hp
  obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.mp hp
  have := (hv t ht).latticeDistance_le hpt
  have := h t ht
  omega

/-- A site of the cube that is not a centre is not a token site. -/
theorem not_mem_tokSites_of_mem_Q {n : ℕ} {ts : List Token} (hv : ∀ t ∈ ts, t.Valid n)
    {p : Site} (hp : p ∈ Q n) (h : ∀ t ∈ ts, t.c ≠ p) : p ∉ tokSites ts := by
  intro hmem
  obtain ⟨t, ht, h1 | h1 | h1⟩ := mem_tokSites.mp hmem
  · exact (hv t ht).a_out (h1 ▸ hp)
  · exact h t ht h1.symm
  · exact (hv t ht).b_out (h1 ▸ hp)

/-! ## Rows -/

/-- One step along a row: `a + t e` and `a + (t + 1) e` are adjacent when `e` is a unit
vector. -/
theorem adj_row (a : Site) {e : Site} (he : cubicLattice.Adj 0 e) (t : ℤ) :
    cubicLattice.Adj (fun k => a k + t * e k) (fun k => a k + (t + 1) * e k) := by
  rw [adj_iff, latticeDistance_eq] at he ⊢
  have hk : ∀ k, a k + t * e k - (a k + (t + 1) * e k) = 0 - e k := fun k => by ring
  rw [hk, hk, hk]
  simpa using he

theorem line_nodup (a : Site) {e : Site} (he : e ≠ 0) (r : ℕ) : (line a e r).Nodup := by
  unfold line
  refine List.Nodup.map_on ?_ List.nodup_range
  intro t _ t' _ h
  obtain ⟨k, hk⟩ : ∃ k, e k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact he (funext hcon)
  have h1 := congrFun h k
  have h2 : ((t : ℤ) - t') * e k = 0 := by rw [sub_mul]; linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · omega
  · exact absurd h3 hk

theorem line_isChain (a : Site) {e : Site} (he : cubicLattice.Adj 0 e) (r : ℕ) :
    (line a e r).IsChain cubicLattice.Adj := by
  unfold line
  rw [List.isChain_map, List.isChain_range]
  intro m _
  have := adj_row a he (m : ℤ)
  push_cast
  exact this

theorem line_head? (a e : Site) {r : ℕ} (hr : 0 < r) : (line a e r).head? = some a := by
  unfold line
  rw [List.head?_map, List.head?_range, if_neg (by omega)]
  simp

theorem line_getLast? (a e : Site) {r : ℕ} (hr : 0 < r) :
    (line a e r).getLast? = some (fun k => a k + ((r : ℤ) - 1) * e k) := by
  unfold line
  rw [List.getLast?_map, List.getLast?_range, if_neg (by omega)]
  simp only [Option.map_some]
  congr
  funext k
  push_cast [Nat.cast_sub (show 1 ≤ r by omega)]
  ring

/-! ## Rows of tokens with alternating normals -/

/-- Tokens on the row `a, a + e, a + 2e, …` whose `P`'s hang alternately on the sides `ν`
and `ν'`: token number `t` (from 0) has the `P` before it on `ν` and the `P` after it on
`ν'` if `t` is even, and the other way round if `t` is odd. -/
def altRun (a e : Site) (r : ℕ) (ν ν' : Site) : List Token :=
  (List.range r).map fun (t : ℕ) =>
    ⟨fun k => a k + (t : ℤ) * e k, if t % 2 = 0 then ν else ν', if t % 2 = 0 then ν' else ν⟩

theorem altRun_length (a e : Site) (r : ℕ) (ν ν' : Site) : (altRun a e r ν ν').length = r := by
  simp [altRun]

theorem mem_altRun {a e : Site} {r : ℕ} {ν ν' : Site} {tk : Token} :
    tk ∈ altRun a e r ν ν' ↔ ∃ t, t < r ∧
      tk = ⟨fun k => a k + (t : ℤ) * e k, if t % 2 = 0 then ν else ν',
        if t % 2 = 0 then ν' else ν⟩ := by
  unfold altRun
  rw [List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, List.mem_range.mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, List.mem_range.mpr ht, rfl⟩

theorem altRun_centres (a e : Site) (r : ℕ) (ν ν' : Site) :
    (altRun a e r ν ν').map Token.c = line a e r := by
  simp [altRun, line, Function.comp_def]

theorem altRun_isChain (a : Site) {e : Site} (he : cubicLattice.Adj 0 e) (r : ℕ)
    (ν ν' : Site) : (altRun a e r ν ν').IsChain Linked := by
  unfold altRun
  rw [List.isChain_map, List.isChain_range]
  intro m _
  refine ⟨?_, ?_⟩
  · rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have h' : m.succ % 2 = 1 := by omega
      simp [h, h']
    · have h' : m.succ % 2 = 0 := by omega
      simp [h, h']
  · have := adj_row a he (m : ℤ)
    push_cast
    exact this

theorem altRun_head? (a e : Site) {r : ℕ} (hr : 0 < r) (ν ν' : Site) :
    (altRun a e r ν ν').head? = some ⟨a, ν, ν'⟩ := by
  unfold altRun
  rw [List.head?_map, List.head?_range, if_neg (by omega)]
  simp

theorem altRun_getLast?_even (a e : Site) {r : ℕ} (hr : 0 < r) (heven : Even r) (ν ν' : Site) :
    (altRun a e r ν ν').getLast? = some ⟨fun k => a k + ((r : ℤ) - 1) * e k, ν', ν⟩ := by
  unfold altRun
  rw [List.getLast?_map, List.getLast?_range, if_neg (by omega)]
  obtain ⟨j, rfl⟩ := heven
  have h : (j + j - 1) % 2 = 1 := by omega
  simp only [Option.map_some, h]
  simp only [one_ne_zero, if_false, Option.some.injEq, Token.mk.injEq, and_true]
  funext k
  push_cast [Nat.cast_sub (show 1 ≤ j + j by omega)]
  ring

theorem altRun_getLast?_odd (a e : Site) {r : ℕ} (hodd : Odd r) (ν ν' : Site) :
    (altRun a e r ν ν').getLast? = some ⟨fun k => a k + ((r : ℤ) - 1) * e k, ν, ν'⟩ := by
  unfold altRun
  obtain ⟨j, rfl⟩ := hodd
  rw [List.getLast?_map, List.getLast?_range, if_neg (by omega)]
  have h : (2 * j + 1 - 1) % 2 = 0 := by omega
  simp only [Option.map_some, h]
  simp only [if_true, Option.some.injEq, Token.mk.injEq, and_true]
  funext k
  push_cast
  ring

/-! ## Dense runs -/

theorem flatten_PPH_append_P (k : ℕ) :
    (List.replicate k [P, P, H]).flatten ++ [P] = P :: (List.replicate k [P, H, P]).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih, List.replicate_succ,
      List.flatten_cons]
    rfl

/-- A dense run with the `P` before it and the `P` after it is `(PHP)^r`. -/
theorem P_denseRun_P {r : ℕ} (hr : 0 < r) :
    P :: (denseRun r ++ [P]) = (List.replicate r [P, H, P]).flatten := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [denseRun, List.cons_append, flatten_PPH_append_P, List.replicate_succ, List.flatten_cons]
  rfl

end ProteinFolding.Shelf

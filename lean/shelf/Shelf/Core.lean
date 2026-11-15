import Mathlib
import Shelf.Sites
import Shelf.Word
import Shelf.Count

/-!
# The Core Lemma

Lemma 14 of the paper: for even `n ≥ 6`, the points of the cube `Q n` off the skeleton
carry a path of length `n³ - 12n + 16` ending at `(1, N, N - 1)`, with `N = n - 1`.

We write `n = 2m + 6`, so `N = 2m + 5`. A layer `y = const` is described by the pairs
`(x, z)`. The planar path `deltaRev m` is the cycle `Δ` of the paper without its edge
`pr`, run from `p = (2, N - 1)` to `r = (1, N - 1)`; `gamma m` is the cycle `Γ` without
its edge `pp'`, run from `p` to `p' = (2, N)`. Both are glued from columns and rows, and
from the zigzag `zig F L y k`, which runs `L` and its reverse alternately at the `2k`
positions `y, y + 1, …`. The same zigzag stacks `gamma m` over the middle layers.
-/

namespace ProteinFolding.Shelf.Core

open ProteinFolding

/-- The integers `a, a + 1, …, a + len - 1`. -/
def zr (a : ℤ) : ℕ → List ℤ
  | 0 => []
  | len + 1 => a :: zr (a + 1) len

/-- The zigzag: `L` placed at `y`, then `L` reversed at `y + 1`, then the same at `y + 2`,
and so on, `k` times. -/
def zig {α β : Type} (F : ℤ → β → α) (L : List β) : ℤ → ℕ → List α
  | _, 0 => []
  | y, k + 1 => L.map (F y) ++ (L.reverse.map (F (y + 1)) ++ zig F L (y + 2) k)

/-- The point at height `z` of the column `x`. -/
def V (x z : ℤ) : ℤ × ℤ := (x, z)
/-- The point at position `x` of the row `z`. -/
def H (z x : ℤ) : ℤ × ℤ := (x, z)
/-- The point `(x, z)` of a layer, placed in the layer `y`. -/
def L3 (y : ℤ) (q : ℤ × ℤ) : Site := pt q.1 y q.2

/-- The path `Δ` without the edge `pr`, from `p = (2, N - 1)` to `r = (1, N - 1)`: the
columns `2, …, N - 1` restricted to `2 ≤ z ≤ N - 1`, the row `z = 1` back to `x = 2`, and
the column `x = 1` upwards. -/
def deltaRev (m : ℕ) : List (ℤ × ℤ) :=
  zig V (zr 2 (2 * m + 3)).reverse 2 (m + 1) ++
  ((zr 2 (2 * m + 3)).reverse.map (V (2 * m + 4)) ++
  ((zr 2 (2 * m + 3)).reverse.map (H 1) ++
  (zr 1 (2 * m + 4)).map (V 1)))

/-- The end of `Γ` without `pp'`: the column `x = N - 1` downwards with the detours through
`x = N`, the row `z = 0`, the column `x = 1` upwards with the detours through `x = 0`, and
`(1, N), (2, N)`. -/
def gammaTail (m : ℕ) : List (ℤ × ℤ) :=
  [((2 * m + 4 : ℤ), (2 * m + 5 : ℤ))] ++
  ((zig H (zr (2 * m + 4) 2) 1 (m + 2)).reverse ++
  ([((2 * m + 4 : ℤ), (0 : ℤ))] ++
  ((zr 1 (2 * m + 3)).reverse.map (H 0) ++
  (zig H (zr 0 2).reverse 1 (m + 2) ++
  [((1 : ℤ), (2 * m + 5 : ℤ)), ((2 : ℤ), (2 * m + 5 : ℤ))]))))

/-- The path `Γ` without the edge `pp'`, from `p = (2, N - 1)` to `p' = (2, N)`. -/
def gamma (m : ℕ) : List (ℤ × ℤ) :=
  (zr 1 (2 * m + 4)).reverse.map (V 2) ++
  ((zr 1 (2 * m + 5)).map (V 3) ++
  (zig V (zr 1 (2 * m + 5)).reverse 4 m ++ gammaTail m))

/-- The whole core path: the layer `y = 0`, the middle layers, the layer `y = N`. -/
def core (m : ℕ) : List Site :=
  (deltaRev m).reverse.map (L3 0) ++
  (zig L3 (gamma m) 1 (m + 2) ++ (deltaRev m).map (L3 (2 * m + 5)))

/-- Adjacent integers. -/
def Adj1 (a b : ℤ) : Prop := (a - b).natAbs = 1
/-- Adjacent points of the plane. -/
def Adj2 (p q : ℤ × ℤ) : Prop := (p.1 - q.1).natAbs + (p.2 - q.2).natAbs = 1

theorem mem_zr {a b : ℤ} {len : ℕ} : b ∈ zr a len ↔ a ≤ b ∧ b < a + len := by
  induction len generalizing a with
  | zero => simp [zr]
  | succ len ih => simp only [zr, List.mem_cons, ih]; push_cast; omega

theorem nodup_zr (a : ℤ) (len : ℕ) : (zr a len).Nodup := by
  induction len generalizing a with
  | zero => simp [zr]
  | succ len ih => simp only [zr, List.nodup_cons, mem_zr]; exact ⟨by omega, ih _⟩

theorem chain_zr (a : ℤ) (len : ℕ) : (zr a len).IsChain Adj1 := by
  induction len generalizing a with
  | zero => simp [zr]
  | succ len ih =>
    cases len with
    | zero => simp [zr]
    | succ len =>
      exact List.IsChain.cons_cons (by simp [Adj1]) (ih (a + 1))

theorem head?_zr (a : ℤ) (len : ℕ) : (zr a (len + 1)).head? = some a := rfl

theorem getLast?_zr (a : ℤ) (len : ℕ) : (zr a (len + 1)).getLast? = some (a + len) := by
  induction len generalizing a with
  | zero => simp [zr]
  | succ len ih =>
    rw [show zr a (len + 1 + 1) = [a] ++ zr (a + 1) (len + 1) from rfl, List.getLast?_append,
      ih]
    simp; ring

theorem zig_nil {α β : Type} (F : ℤ → β → α) (y : ℤ) (k : ℕ) : zig F [] y k = [] := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih => simp [zig, ih]

theorem mem_zig {α β : Type} {F : ℤ → β → α} {L : List β} {y : ℤ} {k : ℕ} {a : α}
    (h : a ∈ zig F L y k) : ∃ t b, y ≤ t ∧ t < y + 2 * k ∧ b ∈ L ∧ a = F t b := by
  induction k generalizing y with
  | zero => simp [zig] at h
  | succ k ih =>
    simp only [zig, List.mem_append, List.mem_map, List.mem_reverse] at h
    rcases h with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ | h
    · exact ⟨y, b, by omega, by omega, hb, rfl⟩
    · exact ⟨y + 1, b, by omega, by omega, hb, rfl⟩
    · obtain ⟨t, b, h1, h2, hb, rfl⟩ := ih h
      exact ⟨t, b, by omega, by push_cast at h2 ⊢; omega, hb, rfl⟩

theorem nodup_zig {α β : Type} {F : ℤ → β → α} {L : List β} (hL : L.Nodup)
    (hF : ∀ t t' b b', F t b = F t' b' → t = t' ∧ b = b') (y : ℤ) (k : ℕ) :
    (zig F L y k).Nodup := by
  have hinj : ∀ t, Function.Injective (F t) := fun t b b' h => (hF t t b b' h).2
  induction k generalizing y with
  | zero => simp [zig]
  | succ k ih =>
    simp only [zig]
    rw [List.nodup_append, List.nodup_append]
    refine ⟨hL.map (hinj y), ⟨(List.nodup_reverse.2 hL).map (hinj _), ih _, ?_⟩, ?_⟩
    · intro a ha b hb hab
      obtain ⟨t, c, h1, h2, hc, rfl⟩ := mem_zig hb
      simp only [List.mem_map, List.mem_reverse] at ha
      obtain ⟨d, hd, rfl⟩ := ha
      have := (hF _ _ _ _ hab).1; omega
    · intro a ha b hb hab
      simp only [List.mem_map] at ha
      obtain ⟨d, hd, rfl⟩ := ha
      rw [List.mem_append] at hb
      rcases hb with hb | hb
      · simp only [List.mem_map, List.mem_reverse] at hb
        obtain ⟨c, hc, rfl⟩ := hb
        have := (hF _ _ _ _ hab).1; omega
      · obtain ⟨t, c, h1, h2, hc, rfl⟩ := mem_zig hb
        have := (hF _ _ _ _ hab).1; omega

theorem head?_zig {α β : Type} (F : ℤ → β → α) (L : List β) (y : ℤ) (k : ℕ) :
    (zig F L y (k + 1)).head? = L.head?.map (F y) := by
  cases L with
  | nil => simp [zig_nil]
  | cons b L => simp [zig]

theorem getLast?_zig {α β : Type} (F : ℤ → β → α) (L : List β) (y : ℤ) (k : ℕ) :
    (zig F L y (k + 1)).getLast? = L.head?.map (F (y + 2 * k + 1)) := by
  cases L with
  | nil => simp [zig_nil]
  | cons b L =>
    induction k generalizing y with
    | zero =>
      rw [zig, zig, List.append_nil, List.getLast?_append, List.getLast?_map,
        List.getLast?_reverse]
      simp
    | succ k ih =>
      rw [zig, List.getLast?_append, List.getLast?_append, ih]
      simp only [List.head?_cons, Option.map_some, Option.some_or]
      congr 2; push_cast; ring

theorem chain_zig {α β : Type} {F : ℤ → β → α} {L : List β} {S : β → β → Prop}
    {R : α → α → Prop} (hL : L.IsChain S) (hS : ∀ b b', S b b' → S b' b)
    (hR : ∀ t b b', S b b' → R (F t b) (F t b')) (hU : ∀ t b, R (F t b) (F (t + 1) b))
    (y : ℤ) (k : ℕ) : (zig F L y k).IsChain R := by
  induction k generalizing y with
  | zero => simp [zig]
  | succ k ih =>
    simp only [zig]
    rw [List.isChain_append, List.isChain_append]
    refine ⟨List.isChain_map_of_isChain (F y) (hR y) hL,
      ⟨List.isChain_map_of_isChain (F (y + 1)) (hR (y + 1))
        (List.isChain_reverse.2 (hL.imp fun a b h => hS _ _ h)), ih _, ?_⟩, ?_⟩
    · cases k with
      | zero => simp [zig]
      | succ k =>
        rw [head?_zig]
        intro a ha c hc
        rw [List.getLast?_map, List.getLast?_reverse] at ha
        obtain ⟨b, hb, rfl⟩ := Option.mem_map.1 ha
        obtain ⟨b', hb', rfl⟩ := Option.mem_map.1 hc
        rw [Option.mem_def] at hb hb'
        rw [hb] at hb'; cases hb'
        have := hU (y + 1) b
        rwa [show y + 1 + 1 = y + 2 by ring] at this
    · intro a ha c hc
      rw [List.getLast?_map] at ha
      obtain ⟨b, hb, rfl⟩ := Option.mem_map.1 ha
      rw [Option.mem_def] at hb
      rw [List.head?_append, List.head?_map, List.head?_reverse, hb] at hc
      simp only [Option.map_some, Option.some_or, Option.mem_def, Option.some.injEq] at hc
      subst hc
      exact hU y b


theorem head?_zr' {a : ℤ} {len : ℕ} (h : 0 < len) : (zr a len).head? = some a := by
  obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
  rfl

theorem getLast?_zr' {a : ℤ} {len : ℕ} (h : 0 < len) :
    (zr a len).getLast? = some (a + len - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
  rw [getLast?_zr]; push_cast; ring_nf

theorem mem_zig_iff {α β : Type} {F : ℤ → β → α} {L : List β} {y : ℤ} {k : ℕ} {a : α} :
    a ∈ zig F L y k ↔ ∃ t b, y ≤ t ∧ t < y + 2 * k ∧ b ∈ L ∧ F t b = a := by
  constructor
  · intro h
    obtain ⟨t, b, h1, h2, hb, rfl⟩ := mem_zig h
    exact ⟨t, b, h1, h2, hb, rfl⟩
  · rintro ⟨t, b, h1, h2, hb, rfl⟩
    induction k generalizing y with
    | zero => omega
    | succ k ih =>
      simp only [zig, List.mem_append, List.mem_map, List.mem_reverse]
      by_cases ht : t = y
      · subst ht; exact Or.inl ⟨b, hb, rfl⟩
      by_cases ht' : t = y + 1
      · subst ht'; exact Or.inr (Or.inl ⟨b, hb, rfl⟩)
      exact Or.inr (Or.inr (ih (by omega) (by push_cast at h2; omega)))

theorem adj1_symm {a b : ℤ} (h : Adj1 a b) : Adj1 b a := by
  unfold Adj1 at *; omega

theorem adj2_symm {p q : ℤ × ℤ} (h : Adj2 p q) : Adj2 q p := by
  unfold Adj2 at *; omega

theorem chain_zr_rev (a : ℤ) (len : ℕ) : (zr a len).reverse.IsChain Adj1 :=
  List.isChain_reverse.2 ((chain_zr a len).imp fun _ _ h => adj1_symm h)

theorem chain_map_V (x : ℤ) {L : List ℤ} (h : L.IsChain Adj1) : (L.map (V x)).IsChain Adj2 :=
  List.isChain_map_of_isChain _ (fun a b hab => by simp only [Adj2, V, Adj1] at *; omega) h

theorem chain_map_H (z : ℤ) {L : List ℤ} (h : L.IsChain Adj1) : (L.map (H z)).IsChain Adj2 :=
  List.isChain_map_of_isChain _ (fun a b hab => by simp only [Adj2, H, Adj1] at *; omega) h

theorem chain_zig_V (x : ℤ) (k : ℕ) {L : List ℤ} (h : L.IsChain Adj1) :
    (zig V L x k).IsChain Adj2 :=
  chain_zig h (fun _ _ => adj1_symm) (fun t a b hab => by simp only [Adj2, V, Adj1] at *; omega)
    (fun t b => by simp [Adj2, V]) x k

theorem chain_zig_H (x : ℤ) (k : ℕ) {L : List ℤ} (h : L.IsChain Adj1) :
    (zig H L x k).IsChain Adj2 :=
  chain_zig h (fun _ _ => adj1_symm) (fun t a b hab => by simp only [Adj2, H, Adj1] at *; omega)
    (fun t b => by simp [Adj2, H]) x k

theorem nodup_zig_V (x : ℤ) (k : ℕ) {L : List ℤ} (h : L.Nodup) : (zig V L x k).Nodup :=
  nodup_zig h (fun t t' b b' hh => by simpa [V] using hh) x k

theorem nodup_zig_H (x : ℤ) (k : ℕ) {L : List ℤ} (h : L.Nodup) : (zig H L x k).Nodup :=
  nodup_zig h (fun t t' b b' hh => by simp only [H, Prod.mk.injEq] at hh; exact ⟨hh.2, hh.1⟩) x k

theorem nodup_map_V (x : ℤ) {L : List ℤ} (h : L.Nodup) : (L.map (V x)).Nodup :=
  h.map fun a b hh => by simpa [V] using hh

theorem nodup_map_H (x : ℤ) {L : List ℤ} (h : L.Nodup) : (L.map (H x)).Nodup :=
  h.map fun a b hh => by simpa [H] using hh

theorem nodup_zr_rev (a : ℤ) (len : ℕ) : (zr a len).reverse.Nodup :=
  List.nodup_reverse.2 (nodup_zr a len)

theorem nodup_deltaRev (m : ℕ) : (deltaRev m).Nodup := by
  simp only [deltaRev, List.nodup_append]
  refine ⟨nodup_zig_V _ _ (nodup_zr_rev _ _), ⟨nodup_map_V _ (nodup_zr_rev _ _),
    ⟨nodup_map_H _ (nodup_zr_rev _ _), nodup_map_V _ (nodup_zr _ _), ?_⟩, ?_⟩, ?_⟩ <;>
  · rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [mem_zig_iff, List.mem_append, List.mem_map, List.mem_reverse, mem_zr, V, H,
      Prod.mk.injEq] at ha hb
    omega


theorem chain_deltaRev (m : ℕ) : (deltaRev m).IsChain Adj2 := by
  have h2 := getLast?_zig V (zr 2 (2 * m + 3)).reverse 2 m
  have h3 : (zr 2 (2 * m + 3)).head? = some 2 := head?_zr' (by omega)
  have h4 : (zr 2 (2 * m + 3)).getLast? = some (2 + ((2 * m + 3 : ℕ) : ℤ) - 1) :=
    getLast?_zr' (by omega)
  have h5 : (zr 1 (2 * m + 4)).head? = some 1 := head?_zr' (by omega)
  simp only [deltaRev, List.isChain_append, List.head?_append,
    List.head?_map, List.getLast?_map, List.head?_reverse, List.getLast?_reverse, h2, h3, h4,
    h5, Option.map_some, Option.some_or, Option.mem_def, Option.some.injEq, forall_eq']
  refine ⟨chain_zig_V _ _ (chain_zr_rev _ _), ⟨chain_map_V _ (chain_zr_rev _ _),
    ⟨chain_map_H _ (chain_zr_rev _ _), chain_map_V _ (chain_zr _ _), ?_⟩, ?_⟩, ?_⟩ <;>
  · simp only [Adj2, V, H]; push_cast <;> omega


theorem chain_gammaTail (m : ℕ) : (gammaTail m).IsChain Adj2 := by
  have h1 := head?_zig H (zr (2 * m + 4 : ℤ) 2) 1 (m + 1)
  have h2 := getLast?_zig H (zr (2 * m + 4 : ℤ) 2) 1 (m + 1)
  have h1' := head?_zig H (zr 0 2).reverse 1 (m + 1)
  have h2' := getLast?_zig H (zr 0 2).reverse 1 (m + 1)
  have h3 : (zr 1 (2 * m + 3)).head? = some 1 := head?_zr' (by omega)
  have h4 : (zr 1 (2 * m + 3)).getLast? = some (1 + ((2 * m + 3 : ℕ) : ℤ) - 1) :=
    getLast?_zr' (by omega)
  have h5 : (zr (2 * m + 4 : ℤ) 2).head? = some (2 * m + 4 : ℤ) := rfl
  have h6 : (zr 0 2).reverse.head? = some 1 := rfl
  have hp : [((1 : ℤ), (2 * m + 5 : ℤ)), ((2 : ℤ), (2 * m + 5 : ℤ))].IsChain Adj2 :=
    List.IsChain.cons_cons (by simp [Adj2]) (List.isChain_singleton _)
  simp only [gammaTail, List.isChain_append, List.head?_append,
    List.head?_map, List.getLast?_map, List.head?_reverse, List.getLast?_reverse, h1, h2, h3, h4,
    h5, h6, h1', h2', Option.map_some, Option.some_or, Option.mem_def, Option.some.injEq,
    forall_eq', List.head?_cons, List.getLast?_singleton]
  refine ⟨List.isChain_singleton _, ⟨List.isChain_reverse.2 ((chain_zig_H _ _ (chain_zr _ _)).imp
    fun _ _ h => adj2_symm h), ⟨List.isChain_singleton _, ⟨chain_map_H _ (chain_zr_rev _ _),
    ⟨chain_zig_H _ _ (chain_zr_rev _ _), hp, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
  · simp only [Adj2, H]; push_cast <;> omega


theorem head?_gammaTail (m : ℕ) :
    (gammaTail m).head? = some ((2 * m + 4 : ℤ), (2 * m + 5 : ℤ)) := rfl

theorem chain_gamma_mid (m : ℕ) :
    (zig V (zr 1 (2 * m + 5)).reverse 4 m ++ gammaTail m).IsChain Adj2 ∧
    (zig V (zr 1 (2 * m + 5)).reverse 4 m ++ gammaTail m).head? =
      some ((4 : ℤ), (2 * m + 5 : ℤ)) := by
  rcases m with _ | k
  · exact ⟨chain_gammaTail 0, by simp [zig, head?_gammaTail]⟩
  · have h4 : (zr 1 (2 * (k + 1) + 5)).getLast? = some (1 + ((2 * (k + 1) + 5 : ℕ) : ℤ) - 1) :=
      getLast?_zr' (by omega)
    refine ⟨?_, ?_⟩
    · rw [List.isChain_append]
      refine ⟨chain_zig_V _ _ (chain_zr_rev _ _), chain_gammaTail _, ?_⟩
      rw [getLast?_zig, head?_gammaTail, List.head?_reverse, h4]
      simp only [Option.map_some, Option.mem_def, Option.some.injEq, forall_eq', Adj2, V]
      push_cast; omega
    · rw [List.head?_append, head?_zig, List.head?_reverse, h4]
      simp only [Option.map_some, Option.some_or, V]
      push_cast; congr 2; ring

theorem chain_gamma (m : ℕ) : (gamma m).IsChain Adj2 := by
  obtain ⟨hc, hh⟩ := chain_gamma_mid m
  have h3 : (zr 1 (2 * m + 4)).head? = some 1 := head?_zr' (by omega)
  have h4 : (zr 1 (2 * m + 5)).head? = some 1 := head?_zr' (by omega)
  have h5 : (zr 1 (2 * m + 5)).getLast? = some (1 + ((2 * m + 5 : ℕ) : ℤ) - 1) :=
    getLast?_zr' (by omega)
  rw [gamma, List.isChain_append, List.isChain_append]
  simp only [List.head?_append, List.head?_map, List.getLast?_map,
    List.getLast?_reverse, hh, h3, h4, h5, Option.map_some, Option.some_or, Option.mem_def,
    Option.some.injEq, forall_eq']
  refine ⟨chain_map_V _ (chain_zr_rev _ _), ⟨chain_map_V _ (chain_zr _ _), hc, ?_⟩, ?_⟩ <;>
  · simp only [Adj2, V]; push_cast <;> omega

theorem nodup_gamma (m : ℕ) : (gamma m).Nodup := by
  simp only [gamma, gammaTail, List.nodup_append]
  refine ⟨nodup_map_V _ (nodup_zr_rev _ _), ⟨nodup_map_V _ (nodup_zr _ _),
    ⟨nodup_zig_V _ _ (nodup_zr_rev _ _), ⟨List.nodup_singleton _,
    ⟨List.nodup_reverse.2 (nodup_zig_H _ _ (nodup_zr _ _)), ⟨List.nodup_singleton _,
    ⟨nodup_map_H _ (nodup_zr_rev _ _), ⟨nodup_zig_H _ _ (nodup_zr_rev _ _), by simp, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
  · rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [mem_zig_iff, mem_zr, V, H] at ha hb
    omega

theorem box_deltaRev {m : ℕ} {q : ℤ × ℤ} (h : q ∈ deltaRev m) :
    1 ≤ q.1 ∧ q.1 ≤ 2 * m + 4 ∧ 1 ≤ q.2 ∧ q.2 ≤ 2 * m + 4 := by
  obtain ⟨a, b⟩ := q
  simp [deltaRev, mem_zig_iff, mem_zr, V, H] at h
  omega

theorem box_gamma {m : ℕ} {q : ℤ × ℤ} (h : q ∈ gamma m) :
    0 ≤ q.1 ∧ q.1 ≤ 2 * m + 5 ∧ 0 ≤ q.2 ∧ q.2 ≤ 2 * m + 5 ∧
      ¬ ((q.1 = 0 ∨ q.1 = 2 * m + 5) ∧ (q.2 = 0 ∨ q.2 = 2 * m + 5)) := by
  obtain ⟨a, b⟩ := q
  simp [gamma, gammaTail, mem_zig_iff, mem_zr, V, H] at h
  omega


theorem L3_inj {t t' : ℤ} {q q' : ℤ × ℤ} (h : L3 t q = L3 t' q') : t = t' ∧ q = q' := by
  simp only [L3, pt_eq_iff] at h
  exact ⟨h.2.1, Prod.ext h.1 h.2.2⟩

theorem adj_L3 (t : ℤ) {q q' : ℤ × ℤ} (h : Adj2 q q') : cubicLattice.Adj (L3 t q) (L3 t q') := by
  rw [L3, L3, adj_pt]; unfold Adj2 at h; simpa using h

theorem adj_L3_up (t : ℤ) (q : ℤ × ℤ) : cubicLattice.Adj (L3 t q) (L3 (t + 1) q) := by
  rw [L3, L3, adj_pt]; simp

theorem length_zr (a : ℤ) (len : ℕ) : (zr a len).length = len := by
  induction len generalizing a with
  | zero => rfl
  | succ len ih => simp [zr, ih]

theorem length_zig {α β : Type} (F : ℤ → β → α) (L : List β) (y : ℤ) (k : ℕ) :
    (zig F L y k).length = 2 * k * L.length := by
  induction k generalizing y with
  | zero => simp [zig]
  | succ k ih => simp [zig, ih]; ring

theorem length_deltaRev (m : ℕ) : (deltaRev m).length = 4 * m ^ 2 + 16 * m + 16 := by
  simp [deltaRev, length_zig, length_zr]; ring

theorem length_gamma (m : ℕ) : (gamma m).length = 4 * m ^ 2 + 24 * m + 32 := by
  simp [gamma, gammaTail, length_zig, length_zr]; ring

theorem head?_deltaRev (m : ℕ) : (deltaRev m).head? = some ((2 : ℤ), (2 * m + 4 : ℤ)) := by
  have h4 : (zr 2 (2 * m + 3)).getLast? = some (2 + ((2 * m + 3 : ℕ) : ℤ) - 1) :=
    getLast?_zr' (by omega)
  rw [deltaRev, List.head?_append, head?_zig, List.head?_reverse, h4]
  simp only [Option.map_some, Option.some_or, V]
  push_cast; congr 2; ring

theorem getLast?_deltaRev (m : ℕ) :
    (deltaRev m).getLast? = some ((1 : ℤ), (2 * m + 4 : ℤ)) := by
  have h4 : (zr 1 (2 * m + 4)).getLast? = some (1 + ((2 * m + 4 : ℕ) : ℤ) - 1) :=
    getLast?_zr' (by omega)
  simp only [deltaRev, List.getLast?_append, List.getLast?_map, h4, Option.map_some,
    Option.some_or, V]
  push_cast; congr 2; ring

theorem head?_gamma (m : ℕ) : (gamma m).head? = some ((2 : ℤ), (2 * m + 4 : ℤ)) := by
  have h4 : (zr 1 (2 * m + 4)).getLast? = some (1 + ((2 * m + 4 : ℕ) : ℤ) - 1) :=
    getLast?_zr' (by omega)
  rw [gamma, List.head?_append, List.head?_map, List.head?_reverse, h4]
  simp only [Option.map_some, Option.some_or, V]
  push_cast; congr 2; ring

theorem length_core (m : ℕ) : (core m).length = coreLength (2 * m + 6) := by
  have := twelve_mul_le (2 * m + 6)
  simp only [core, List.length_append, List.length_map, List.length_reverse, length_zig,
    length_deltaRev, length_gamma, coreLength]
  apply Nat.eq_sub_of_add_eq
  ring

theorem nodup_core (m : ℕ) : (core m).Nodup := by
  have hinj : ∀ t, Function.Injective (L3 t) := fun t _ _ h => (L3_inj h).2
  rw [core, List.nodup_append, List.nodup_append]
  refine ⟨(List.nodup_reverse.2 (nodup_deltaRev m)).map (hinj 0),
    ⟨nodup_zig (nodup_gamma m) (fun _ _ _ _ h => L3_inj h) _ _, (nodup_deltaRev m).map (hinj _),
      ?_⟩, ?_⟩
  · intro a ha b hb hab
    obtain ⟨t, q, h1, h2, -, rfl⟩ := mem_zig ha
    obtain ⟨q', -, rfl⟩ := List.mem_map.1 hb
    have := (L3_inj hab).1
    push_cast at h2; omega
  · intro a ha b hb hab
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 ha
    rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨t, q', h1, h2, -, rfl⟩ := mem_zig hb
      have := (L3_inj hab).1
      omega
    · obtain ⟨q', -, rfl⟩ := List.mem_map.1 hb
      have := (L3_inj hab).1
      omega

theorem chain_core (m : ℕ) : (core m).IsChain cubicLattice.Adj := by
  rw [core, List.isChain_append, List.isChain_append]
  refine ⟨List.isChain_map_of_isChain (L3 0) (fun _ _ h => adj_L3 0 h)
      (List.isChain_reverse.2 ((chain_deltaRev m).imp fun _ _ h => adj2_symm h)),
    ⟨chain_zig (chain_gamma m) (fun _ _ => adj2_symm) (fun t _ _ h => adj_L3 t h) adj_L3_up _ _,
      List.isChain_map_of_isChain _ (fun _ _ h => adj_L3 _ h) (chain_deltaRev m), ?_⟩, ?_⟩
  · rw [getLast?_zig, List.head?_map, head?_gamma, head?_deltaRev]
    simp only [Option.map_some, Option.mem_def, Option.some.injEq, forall_eq', L3, adj_pt]
    push_cast; omega
  · rw [List.getLast?_map, List.getLast?_reverse, head?_deltaRev, List.head?_append, head?_zig,
      head?_gamma]
    simp only [Option.map_some, Option.some_or, Option.mem_def, Option.some.injEq, forall_eq', L3,
      adj_pt]
    omega

theorem good_pt {m : ℕ} {x y z : ℤ} (hx : 0 ≤ x ∧ x ≤ 2 * m + 5) (hy : 0 ≤ y ∧ y ≤ 2 * m + 5)
    (hz : 0 ≤ z ∧ z ≤ 2 * m + 5)
    (hxy : ¬ ((x = 0 ∨ x = 2 * m + 5) ∧ (y = 0 ∨ y = 2 * m + 5)))
    (hxz : ¬ ((x = 0 ∨ x = 2 * m + 5) ∧ (z = 0 ∨ z = 2 * m + 5)))
    (hyz : ¬ ((y = 0 ∨ y = 2 * m + 5) ∧ (z = 0 ∨ z = 2 * m + 5))) :
    pt x y z ∈ Q (2 * m + 6) ∧ ¬ CubicPackingGeometry.EdgeSkeleton 0 (2 * m + 6) (pt x y z) := by
  refine ⟨pt_mem_Q.2 ⟨⟨by omega, by push_cast; omega⟩, ⟨by omega, by push_cast; omega⟩,
    ⟨by omega, by push_cast; omega⟩⟩, ?_⟩
  rintro ⟨-, i, j, hij, hi, hj⟩
  simp only [CubicPackingGeometry.BoundaryCoordinate, Pi.zero_apply] at hi hj
  push_cast at hi hj
  fin_cases i <;> fin_cases j <;> simp at hi hj hij <;> omega

theorem mem_core {m : ℕ} {p : Site} (hp : p ∈ core m) :
    p ∈ Q (2 * m + 6) ∧ ¬ CubicPackingGeometry.EdgeSkeleton 0 (2 * m + 6) p := by
  rcases List.mem_append.1 hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have := box_deltaRev (List.mem_reverse.1 hq)
    exact good_pt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rcases List.mem_append.1 hp with hp | hp
  · obtain ⟨t, q, h1, h2, hq, rfl⟩ := mem_zig hp
    have := box_gamma hq
    push_cast at h2
    exact good_pt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have := box_deltaRev hq
    exact good_pt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem getLast?_core (m : ℕ) :
    (core m).getLast? = some (pt 1 (2 * m + 5) (2 * m + 4)) := by
  rw [core, List.getLast?_append, List.getLast?_append, List.getLast?_map, getLast?_deltaRev]
  rfl

end ProteinFolding.Shelf.Core

namespace ProteinFolding.Shelf

open ProteinFolding CubicPackingGeometry

/-- **Lemma 14 (Core Lemma).** For even `n ≥ 6` there is a path through `n³ - 12n + 16`
different points of the cube that are not on the skeleton, consecutive ones adjacent,
ending at `(1, N, N - 1)`. -/
theorem corePath (n : ℕ) (hn : 6 ≤ n) (heven : Even n) :
    ∃ ps : List Site,
      ps.length = coreLength n ∧ ps.Nodup ∧ ps.IsChain cubicLattice.Adj ∧
      (∀ p ∈ ps, p ∈ Q n ∧ ¬ EdgeSkeleton 0 n p) ∧
      ps.getLast? = some (pt 1 ((n : ℤ) - 1) ((n : ℤ) - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 6 := by
    obtain ⟨h, rfl⟩ := heven
    exact ⟨h - 3, by omega⟩
  refine ⟨Core.core m, Core.length_core m, Core.nodup_core m, Core.chain_core m,
    fun p hp => Core.mem_core hp, ?_⟩
  rw [Core.getLast?_core]
  congr 2 <;> push_cast <;> ring

end ProteinFolding.Shelf

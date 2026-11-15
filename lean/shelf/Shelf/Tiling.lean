import Mathlib
import Shelf.Source

/-!
# Placing the items on the shelf

First paragraph of Section 5.2 of the paper ("The fold"): an exact packing places the
items of each class one after the other inside one bin of the shelf.
-/

namespace ProteinFolding.Shelf.Tiling

/-- Two intervals of columns are disjoint when one ends before the other starts. -/
lemma disjoint_Ico_of {a b c d : ℕ} (h : b ≤ c ∨ d ≤ a) :
    Disjoint (Finset.Ico a b) (Finset.Ico c d) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_Ico] at hx hx'
  omega

/-- Prefix sums of a list of naturals grow with the length of the prefix. -/
lemma sum_take_mono (l : List ℕ) {a b : ℕ} (h : a ≤ b) :
    (l.take a).sum ≤ (l.take b).sum := by
  induction l generalizing a b with
  | nil => simp
  | cons x l ih =>
    cases a with
    | zero => simp
    | succ a =>
      cases b with
      | zero => omega
      | succ b => simpa using ih (by omega : a ≤ b)

/-- The entry at position `t` ends no later than the offset of any later position. -/
lemma sum_take_add_le (l : List ℕ) {t t' : ℕ} (ht : t < t') (ht' : t < l.length) :
    (l.take t).sum + l[t] ≤ (l.take t').sum := by
  rw [← List.sum_take_succ l t ht']
  exact sum_take_mono l ht

/-- The entry at position `t` ends inside the list. -/
lemma sum_take_add_le_sum (l : List ℕ) {t : ℕ} (ht : t < l.length) :
    (l.take t).sum + l[t] ≤ l.sum := by
  rw [← List.sum_take_succ l t ht]
  conv_rhs => rw [← List.take_length (l := l)]
  exact sum_take_mono l (by omega)

/-- The first column of bin `b` on a shelf of capacity `B`. -/
def start (B b : ℕ) : ℕ := 2 + b * (B + 1)

/-- Placement of the entries of a list of parts, the parts going into consecutive bins
from bin `b₀` on. -/
lemma exists_placement (B : ℕ) (parts : List (List ℕ)) (hp : ∀ p ∈ parts, p.sum ≤ B)
    (b₀ : ℕ) :
    ∃ lo : ℕ → ℕ,
      (∀ t (ht : t < parts.flatten.length), ∃ b, b₀ ≤ b ∧ b < b₀ + parts.length ∧
        start B b ≤ lo t ∧ lo t + parts.flatten[t] ≤ start B b + B) ∧
      (∀ t t' (ht : t < parts.flatten.length) (ht' : t' < parts.flatten.length), t ≠ t' →
        lo t + parts.flatten[t] ≤ lo t' ∨ lo t' + parts.flatten[t'] ≤ lo t) := by
  induction parts generalizing b₀ with
  | nil => exact ⟨fun _ => 0, fun t ht => by simp at ht, fun t _ ht => by simp at ht⟩
  | cons p ps ih =>
    obtain ⟨lo', hbin, hdis⟩ := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq)) (b₀ + 1)
    have hpB : p.sum ≤ B := hp p List.mem_cons_self
    have hstart : start B b₀ + B < start B (b₀ + 1) := by
      unfold start; rw [Nat.add_mul]; omega
    have hmono : ∀ b, b₀ + 1 ≤ b → start B (b₀ + 1) ≤ start B b := by
      intro b hb; unfold start; have := Nat.mul_le_mul_right (B + 1) hb; omega
    refine ⟨fun t => if t < p.length then start B b₀ + (p.take t).sum
      else lo' (t - p.length), ?_, ?_⟩
    · intro t ht
      simp only [List.flatten_cons, List.length_append] at ht
      simp only [List.flatten_cons, List.getElem_append, List.length_cons]
      by_cases h : t < p.length
      · simp only [h, ↓reduceIte, ↓reduceDIte]
        have := sum_take_add_le_sum p h
        exact ⟨b₀, le_rfl, by omega, by omega, by omega⟩
      · simp only [h, ↓reduceIte, ↓reduceDIte]
        obtain ⟨b, hb1, hb2, hb3, hb4⟩ := hbin (t - p.length) (by omega)
        exact ⟨b, by omega, by omega, hb3, hb4⟩
    · intro t t' ht ht' htt
      simp only [List.flatten_cons, List.length_append] at ht ht'
      simp only [List.flatten_cons, List.getElem_append]
      by_cases h : t < p.length <;> by_cases h' : t' < p.length
      · simp only [h, h', ↓reduceIte, ↓reduceDIte]
        rcases Nat.lt_or_gt_of_ne htt with hl | hl
        · have := sum_take_add_le p hl h; omega
        · have := sum_take_add_le p hl h'; omega
      · simp only [h, h', ↓reduceIte, ↓reduceDIte]
        have := sum_take_add_le_sum p h
        obtain ⟨b, hb1, -, hb3, -⟩ := hbin (t' - p.length) (by omega)
        have := hmono b hb1
        omega
      · simp only [h, h', ↓reduceIte, ↓reduceDIte]
        have := sum_take_add_le_sum p h'
        obtain ⟨b, hb1, -, hb3, -⟩ := hbin (t - p.length) (by omega)
        have := hmono b hb1
        omega
      · simp only [h, h', ↓reduceIte, ↓reduceDIte]
        exact hdis _ _ (by omega) (by omega) (by omega)

/-- A permutation of lists gives an injection between the positions that keeps the
entries. -/
lemma exists_index_injection {α : Type*} {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    ∃ σ : ℕ → ℕ, (∀ i, i < l₁.length → l₂[σ i]? = l₁[i]?) ∧
      ∀ i j, i < l₁.length → j < l₁.length → σ i = σ j → i = j := by
  induction h with
  | nil => exact ⟨id, fun i hi => by simp at hi, fun i j hi => by simp at hi⟩
  | cons x _ ih =>
    obtain ⟨σ, he, hσ⟩ := ih
    refine ⟨fun i => if i = 0 then 0 else σ (i - 1) + 1, ?_, ?_⟩
    · intro i hi
      rcases i with _ | i
      · simp
      · simp only [List.length_cons] at hi
        simpa using he i (by omega)
    · intro i j hi hj hij
      simp only [List.length_cons] at hi hj
      rcases i with _ | i <;> rcases j with _ | j <;> simp at hij ⊢
      exact hσ i j (by omega) (by omega) hij
  | swap x y l =>
    refine ⟨fun i => if i = 0 then 1 else if i = 1 then 0 else i, ?_, ?_⟩
    · intro i hi
      rcases i with _ | _ | i <;> simp
    · intro i j hi hj hij
      rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp at hij ⊢
      omega
  | trans h₁ _ ih₁ ih₂ =>
    obtain ⟨σ, he, hσ⟩ := ih₁
    obtain ⟨τ, he', hτ⟩ := ih₂
    have hlt : ∀ i, i < _ → σ i < _ := fun i hi => by
      have := he i hi
      rw [List.getElem?_eq_getElem hi] at this
      exact (List.getElem?_eq_some_iff.mp this).1
    refine ⟨τ ∘ σ, fun i hi => ?_, fun i j hi hj hij => ?_⟩
    · simp only [Function.comp, he' _ (hlt i hi), he i hi]
    · exact hσ i j hi hj (hτ _ _ (hlt i hi) (hlt j hj) hij)

end ProteinFolding.Shelf.Tiling

namespace ProteinFolding.Shelf

open Tiling in
/-- If the instance has an exact packing, the items can be placed on the shelf: item `i`
occupies the `aᵢ` consecutive columns from `lo i` on, inside one bin, and different items
occupy disjoint sets of columns. This is the first paragraph of Section 5.2. -/
theorem exists_tiling (J : Packing.Instance) (h : ∃ parts, Packing.Exact J parts) :
    ∃ lo : Fin J.sizes.length → ℕ,
      (∀ i, ∃ b, b < J.bins ∧ 2 + b * (J.capacity + 1) ≤ lo i ∧
        lo i + J.sizes.get i ≤ 2 + b * (J.capacity + 1) + J.capacity) ∧
      (∀ i i', i ≠ i' →
        Disjoint (Finset.Ico (lo i) (lo i + J.sizes.get i))
          (Finset.Ico (lo i') (lo i' + J.sizes.get i'))) := by
  obtain ⟨parts, hlen, hperm, hsum⟩ := h
  obtain ⟨lo, hbin, hdis⟩ :=
    exists_placement J.capacity parts (fun p hp => (hsum p hp).le) 0
  obtain ⟨σ, he, hσ⟩ := exists_index_injection hperm
  have key : ∀ i : Fin J.sizes.length, ∃ h : σ i < parts.flatten.length,
      parts.flatten[σ i] = J.sizes.get i := by
    intro i
    have := he i i.isLt
    rw [List.getElem?_eq_getElem i.isLt] at this
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp this
    exact ⟨h1, h2⟩
  refine ⟨fun i => lo (σ i), ?_, ?_⟩
  · intro i
    obtain ⟨hi, he'⟩ := key i
    obtain ⟨b, -, hb, h1, h2⟩ := hbin (σ i) hi
    refine ⟨b, by omega, h1, ?_⟩
    rw [← he']; exact h2
  · intro i i' hii
    obtain ⟨hi, he₁⟩ := key i
    obtain ⟨hi', he₂⟩ := key i'
    have hne : σ i ≠ σ i' := fun h => hii (Fin.ext (hσ _ _ i.isLt i'.isLt h))
    have := hdis _ _ hi hi' hne
    rw [he₁, he₂] at this
    exact disjoint_Ico_of (by omega)

end ProteinFolding.Shelf

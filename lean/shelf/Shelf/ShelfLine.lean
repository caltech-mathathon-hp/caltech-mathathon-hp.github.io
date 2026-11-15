import Mathlib
import ProteinFolding.Cubic.Proofs.PackingFromLabels
import Shelf.Source

/-!
# From a row of separators and items to a packing

Steps 5 to 7 of the proof of Theorem 12, with the geometry removed. After Steps 1
to 4 the separators and the items all sit on one edge of the cube, which we see
here as a row of nodes `1, …, d`. What is left is counting: the gaps between
separators are the bins (`packing_of_shelf_line`).

`gap_le` is Step 6: a stretch of the row without separators has at most `B + 4`
nodes, because some tether between consecutive separators has to jump over it.
-/

namespace ProteinFolding.Shelf

open ProteinFolding

/-- A walk `f 0, …, f n` of natural numbers that starts below `x₀`, ends above `x₁` and never
visits `[x₀, x₁]` has a step that jumps over the whole interval. This is the choice of `j` in
Step 6 of the proof of Theorem 12. -/
theorem exists_step_across (f : ℕ → ℕ) {x₀ x₁ : ℕ} (hx : x₀ ≤ x₁) :
    ∀ n, f 0 < x₀ → x₁ < f n → (∀ k ≤ n, f k < x₀ ∨ x₁ < f k) →
      ∃ k < n, f k < x₀ ∧ x₁ < f (k + 1) := by
  intro n
  induction n with
  | zero => intro h0 hn _; omega
  | succ n ih =>
    intro h0 hn hout
    rcases hout n (by omega) with h | h
    · exact ⟨n, by omega, h, hn⟩
    · obtain ⟨k, hk, h1, h2⟩ := ih h0 h (fun k hk => hout k (by omega))
      exact ⟨k, by omega, h1, h2⟩

/-- Step 6 of the proof of Theorem 12: a run `[x₀, x₁]` of nodes without separators, strictly
inside the shelf, has at most `B + 4` nodes, because some inner tether spans it. -/
theorem gap_le (m d C : ℕ) (sep : Fin (m + 1) → ℕ)
    (hends : (sep 0 = 1 ∧ sep (Fin.last m) = d) ∨ (sep 0 = d ∧ sep (Fin.last m) = 1))
    (htether : ∀ j : Fin m, sep j.succ ≤ sep j.castSucc + C ∧ sep j.castSucc ≤ sep j.succ + C)
    {x₀ x₁ : ℕ} (hx : x₀ ≤ x₁) (h2 : 2 ≤ x₀) (hd : x₁ < d)
    (hfree : ∀ j, sep j < x₀ ∨ x₁ < sep j) :
    x₁ + 2 ≤ x₀ + C := by
  let g : ℕ → ℕ := fun k => if h : k < m + 1 then sep ⟨k, h⟩ else 0
  have hg : ∀ k (h : k < m + 1), g k = sep ⟨k, h⟩ := fun k h => by simp [g, h]
  have ht : ∀ k (h : k < m), g (k + 1) ≤ g k + C ∧ g k ≤ g (k + 1) + C := by
    intro k h
    have := htether ⟨k, h⟩
    rw [hg k (by omega), hg (k + 1) (by omega)]
    exact this
  have hg0 : g 0 = sep 0 := hg 0 (by omega)
  have hgm : g m = sep (Fin.last m) := hg m (by omega)
  rcases hends with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · obtain ⟨k, hk, h1, h3⟩ := exists_step_across g hx m (by omega) (by omega)
      (fun k hk => by rw [hg k (by omega)]; exact hfree _)
    have := ht k hk
    omega
  · obtain ⟨k, hk, h1, h3⟩ := exists_step_across (fun k => g (m - k)) hx m
      (by simp only [Nat.sub_zero]; omega) (by simp only [Nat.sub_self]; omega)
      (fun k hk => by simp only; rw [hg (m - k) (by omega)]; exact hfree _)
    have := ht (m - (k + 1)) (by omega)
    have e : m - (k + 1) + 1 = m - k := by omega
    rw [e] at this

    omega

/-- The number of separators strictly below node `x`. -/
def sepCount {n : ℕ} (sep : Fin n → ℕ) (x : ℕ) : ℕ :=
  (Finset.univ.filter fun j => sep j < x).card

/-- A separator in `[x, y)` makes the count at `y` larger than at `x`. -/
theorem sepCount_lt {n : ℕ} (sep : Fin n → ℕ) {x y : ℕ} (j : Fin n) (h1 : x ≤ sep j)
    (h2 : sep j < y) : sepCount sep x < sepCount sep y := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.monotone_filter_right _ (fun _ hj => by omega))]
  exact ⟨j, by simp [h2], by simp; omega⟩

/-- Without a separator in `[x, y)` the counts at `x` and `y` agree. -/
theorem sepCount_eq {n : ℕ} (sep : Fin n → ℕ) {x y : ℕ} (hxy : x ≤ y)
    (h : ∀ j, sep j < x ∨ y ≤ sep j) : sepCount sep x = sepCount sep y := by
  unfold sepCount
  congr 1
  apply Finset.filter_congr
  intro j _
  have := h j
  omega

/-- Steps 5 to 7 of the proof of Theorem 12. Separators and items sit on a row of nodes `1, …, d`.
The first and the last separator are at the two ends, consecutive separators (in the order of the
string) are at most `B + 5` apart, and every item is a block of consecutive nodes that contains no
separator. Then the instance has an exact packing: the classes are the gaps between separators. -/
theorem packing_of_shelf_line (J : Packing.Instance) (hJ : Normalised J) (d : ℕ)
    (sep : Fin (J.bins + 1) → ℕ) (start : Fin J.sizes.length → ℕ)
    (hends : (sep 0 = 1 ∧ sep (Fin.last J.bins) = d) ∨ (sep 0 = d ∧ sep (Fin.last J.bins) = 1))
    (htether : ∀ j : Fin J.bins,
      sep j.succ ≤ sep j.castSucc + (J.capacity + 5) ∧
        sep j.castSucc ≤ sep j.succ + (J.capacity + 5))
    (hitem_range : ∀ i, 1 ≤ start i ∧ start i + J.sizes.get i ≤ d + 1)
    (hitem_disj : ∀ i i', i ≠ i' →
      Disjoint (Finset.Ico (start i) (start i + J.sizes.get i))
        (Finset.Ico (start i') (start i' + J.sizes.get i')))
    (hitem_sep : ∀ i j, sep j ∉ Finset.Ico (start i) (start i + J.sizes.get i)) :
    ∃ parts, Packing.Exact J parts := by
  classical
  set B := J.capacity
  -- separators at node `1` and at node `d`
  obtain ⟨j₁, hj₁⟩ : ∃ j, sep j = 1 := by
    rcases hends with h | h
    exacts [⟨0, h.1⟩, ⟨_, h.2⟩]
  obtain ⟨jd, hjd⟩ : ∃ j, sep j = d := by
    rcases hends with h | h
    exacts [⟨_, h.2⟩, ⟨0, h.1⟩]
  have hpos : ∀ i, 0 < J.sizes.get i := fun i => hJ.size_pos _ (List.get_mem _ _)
  have hsep_i : ∀ i j, sep j < start i ∨ start i + J.sizes.get i ≤ sep j := by
    intro i j
    have := hitem_sep i j
    rw [Finset.mem_Ico] at this
    omega
  -- the count at the start of an item is between `1` and `m`
  have hcnt : ∀ i, 1 ≤ sepCount sep (start i) ∧ sepCount sep (start i) ≤ J.bins := by
    intro i
    have hr := hitem_range i
    have hp := hpos i
    constructor
    · have h1 := hsep_i i j₁
      have := sepCount_lt sep (x := 0) (y := start i) j₁ (by omega) (by omega)
      omega
    · have h2 := hsep_i i jd
      have : sepCount sep (start i) < J.bins + 1 := by
        have := Finset.card_lt_card (s := Finset.univ.filter fun j => sep j < start i)
          (t := Finset.univ) (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.mpr
            ⟨jd, Finset.mem_univ _, by simp; omega⟩)
        simpa [sepCount] using this
      omega
  let label : Fin J.sizes.length → Fin J.bins := fun i =>
    ⟨sepCount sep (start i) - 1, by have := hcnt i; omega⟩
  let regions : Fin J.bins → Finset ℕ := fun b =>
    (Finset.range (d + 1)).filter fun x => sepCount sep x = b + 1 ∧ ∀ j, sep j ≠ x
  have hbound : ∀ b, (∑ i : Fin J.sizes.length with label i = b, J.sizes.get i) ≤ B + 4 := by
    refine Packing.label_sums_le_of_disjoint_sites J.sizes (d := 1) (by norm_num) label
      (fun i => Finset.Ico (start i) (start i + J.sizes.get i)) regions
      (fun i => by simp) hitem_disj ?_ ?_
    · intro i x hx
      rw [Finset.mem_Ico] at hx
      have hr := hitem_range i
      have hc := hcnt i
      simp only [regions, label, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_, fun j hj => hitem_sep i j (by rw [Finset.mem_Ico]; omega)⟩
      rw [← sepCount_eq sep hx.1 (fun j => by have := hsep_i i j; omega)]
      omega
    · intro b
      rw [one_mul]
      by_cases hne : (regions b).Nonempty
      · have mem : ∀ x, x ∈ regions b ↔ x < d + 1 ∧ sepCount sep x = b + 1 ∧ ∀ j, sep j ≠ x :=
          fun x => by simp [regions]
        obtain ⟨x₀, hx₀m, hx₀e⟩ : ∃ x₀ ∈ regions b, (regions b).min' hne = x₀ := ⟨_, Finset.min'_mem _ hne, rfl⟩
        obtain ⟨x₁, hx₁m, hx₁e⟩ : ∃ x₁ ∈ regions b, (regions b).max' hne = x₁ := ⟨_, Finset.max'_mem _ hne, rfl⟩
        have hle : x₀ ≤ x₁ := hx₀e ▸ hx₁e ▸ Finset.min'_le_max' _ hne
        have hx₀ := (mem x₀).1 hx₀m
        have hx₁ := (mem x₁).1 hx₁m
        have hsub : regions b ⊆ Finset.Icc x₀ x₁ := fun x hx =>
          Finset.mem_Icc.mpr ⟨hx₀e ▸ Finset.min'_le _ _ hx, hx₁e ▸ Finset.le_max' _ _ hx⟩
        have hfree : ∀ j, sep j < x₀ ∨ x₁ < sep j := by
          intro j
          by_contra hcon
          have hj := hx₀.2.2 j
          have hj' := hx₁.2.2 j
          have := sepCount_lt sep (x := x₀) (y := x₁) j (by omega) (by omega)
          omega
        have h2 : 2 ≤ x₀ := by
          have := hfree j₁
          have := hx₀.2.2 j₁
          have h0 : sepCount sep 0 = 0 := by simp [sepCount]
          rcases Nat.eq_zero_or_pos x₀ with hz | hz
          · rw [hz] at hx₀; omega
          · omega
        have hd : x₁ < d := by
          have := hx₁.2.2 jd
          have := hx₁.1
          omega
        have := gap_le J.bins d (B + 5) sep hends htether hle h2 hd hfree
        have := Finset.card_le_card hsub
        simp only [Nat.card_Icc] at this
        omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp
  refine ⟨_, Packing.exact_of_label_sums J label hJ.sum_eq fun b => ?_⟩
  have h6 : 6 ∣ ∑ i : Fin J.sizes.length with label i = b, J.sizes.get i :=
    Finset.dvd_sum fun i _ => hJ.six_dvd_size _ (List.get_mem _ _)
  obtain ⟨u, hu⟩ := h6
  obtain ⟨v, hv⟩ := hJ.six_dvd_capacity
  have := hbound b
  change _ ≤ B
  omega

end ProteinFolding.Shelf

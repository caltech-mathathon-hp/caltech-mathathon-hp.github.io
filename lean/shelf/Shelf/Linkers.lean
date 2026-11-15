import Shelf.LayoutPlain
import Shelf.Routing

/-!
# The linkers

The Routing Lemma (Lemma 15) gives the inner sites of the `k + 1` linkers: the
first from `p₀` to `q₀`, and for every item one from the end of the run before it
to its first site. They have the lengths the string asks for, they are pairwise
disjoint, and they stay outside the box `InBox` that holds the rest of the fold.
-/

namespace ProteinFolding.Shelf

open ProteinFolding Residue Layout

namespace Linkers

variable {J : Packing.Instance}

theorem N_eq_side (J : Packing.Instance) : N J = (side J : ℤ) - 1 := rfl

/-- The first and the last column of an item lie in `[2, N - 2]`. -/
theorem firstCol_range (hJ : Normalised J) {lo : Fin J.sizes.length → ℕ} (hlo : Placed J lo)
    (i : Fin J.sizes.length) : 2 ≤ firstCol lo i ∧ firstCol lo i ≤ N J - 2 := by
  have h1 := lo_range hlo i
  have h2 := firstCol_mem hJ lo i
  omega

theorem lastCol_range (hJ : Normalised J) {lo : Fin J.sizes.length → ℕ} (hlo : Placed J lo)
    (i : Fin J.sizes.length) : 2 ≤ lastCol lo i ∧ lastCol lo i ≤ N J - 2 := by
  have h1 := lo_range hlo i
  have h2 := lastCol_mem hJ lo i
  omega

/-- The start of the linker of the item `i`: below `(1, 0, N)` for the first item, below
the last column of the item before it otherwise. -/
theorem prevOut_cases (lo : Fin J.sizes.length → ℕ) (i : Fin J.sizes.length) :
    (i.val = 0 ∧ prevOut lo i = pt 1 (-1) (N J)) ∨
    (∃ j : Fin J.sizes.length, j.val + 1 = i.val ∧ prevOut lo i = pt (lastCol lo j) (-1) 0) := by
  by_cases h : i.val = 0
  · left
    exact ⟨h, by simp [prevOut, h]⟩
  · right
    refine ⟨⟨i.val - 1, by have := i.isLt; omega⟩, by simp; omega, ?_⟩
    simp [prevOut, h, itemOut]

/-- A site with `y ≠ N` outside the box `x ≤ N + 1, y ≥ -1, z ≥ -2` is not in `InBox`. -/
theorem not_inBox {s : Site} (h : ¬ (s 0 ≤ N J + 1 ∧ -1 ≤ s 1 ∧ -2 ≤ s 2)) (hy : s 1 ≠ N J) :
    ¬ InBox J s := by
  rintro (h' | rfl | rfl)
  · exact h h'
  · exact hy rfl
  · exact hy rfl

theorem inBox_bounds {s : Site} (h : InBox J s) : -1 ≤ s 1 ∧ -3 ≤ s 2 := by
  rcases h with h | rfl | rfl
  · omega
  · have := N_eq_side J
    simp only [p₀, pt_apply_one, pt_apply_two]; omega
  · have := N_eq_side J
    simp only [q₀, pt_apply_one, pt_apply_two]; omega

/-- The length of the route of the item `i` before the detours, as given by Lemma 15. -/
def itemBound (lo : Fin J.sizes.length → ℕ) (i : Fin J.sizes.length) : ℤ :=
  routeBound (-1) (-3) ((i : ℕ) + 1) (prevOut lo i) (itemIn lo i)

/-- The bound of the route of an item is odd and at most `λ - 1`. -/
theorem itemBound_spec (hJ : Normalised J) {lo : Fin J.sizes.length → ℕ} (hlo : Placed J lo)
    (i : Fin J.sizes.length) :
    itemBound lo i % 2 = 1 ∧
      itemBound lo i ≤ 4 * (side J : ℤ) + 2 * (J.sizes.length : ℤ) - 1 := by
  have hn := ten_le_side hJ
  obtain ⟨m, hm⟩ := side_even hJ
  have hk := i.isLt
  have hf := firstCol_range hJ hlo i
  have hfo := firstCol_odd hJ lo i
  have hN := N_eq_side J
  rcases prevOut_cases lo i with ⟨h0, hp⟩ | ⟨j, hj, hp⟩
  · simp only [itemBound, routeBound, hp, itemIn, pt_apply_zero, pt_apply_one, pt_apply_two,
      h0]
    rw [abs_of_nonpos (by omega)]
    push_cast
    omega
  · have hl := lastCol_range hJ hlo j
    have hle := lastCol_even hJ lo j
    simp only [itemBound, routeBound, hp, itemIn, pt_apply_zero, pt_apply_one, pt_apply_two]
    rcases le_total (lastCol lo j) (firstCol lo i) with h | h
    · rw [abs_of_nonpos (by omega)]
      push_cast
      omega
    · rw [abs_of_nonneg (by omega)]
      push_cast
      omega

/-- The first ports: `p₀` for the first linker, the end of the run before the item `i`
for the linker of the item `i`. -/
def pp (J : Packing.Instance) (lo : Fin J.sizes.length → ℕ) : Fin (J.sizes.length + 1) → Site :=
  Fin.cons (p₀ J) (prevOut lo)

/-- The second ports: `q₀` for the first linker, the first site of the item `i` for the
linker of the item `i`. -/
def qq (J : Packing.Instance) (lo : Fin J.sizes.length → ℕ) : Fin (J.sizes.length + 1) → Site :=
  Fin.cons (q₀ J) (itemIn lo)

/-- The detours, chosen so that the linkers get the lengths the string asks for. -/
def ee (J : Packing.Instance) (lo : Fin J.sizes.length → ℕ) : Fin (J.sizes.length + 1) → ℕ :=
  Fin.cons ((side J + 2 * J.sizes.length - 12) / 2) fun i =>
    ((4 * (side J : ℤ) + 2 * (J.sizes.length : ℤ) - 1) - itemBound lo i).toNat / 2

@[simp] theorem pp_zero (lo : Fin J.sizes.length → ℕ) : pp J lo 0 = p₀ J := rfl
@[simp] theorem pp_succ (lo : Fin J.sizes.length → ℕ) (i : Fin J.sizes.length) :
    pp J lo i.succ = prevOut lo i := rfl
@[simp] theorem qq_zero (lo : Fin J.sizes.length → ℕ) : qq J lo 0 = q₀ J := rfl
@[simp] theorem qq_succ (lo : Fin J.sizes.length → ℕ) (i : Fin J.sizes.length) :
    qq J lo i.succ = itemIn lo i := rfl
@[simp] theorem ee_zero (lo : Fin J.sizes.length → ℕ) :
    ee J lo 0 = (side J + 2 * J.sizes.length - 12) / 2 := rfl
@[simp] theorem ee_succ (lo : Fin J.sizes.length → ℕ) (i : Fin J.sizes.length) :
    ee J lo i.succ =
      ((4 * (side J : ℤ) + 2 * (J.sizes.length : ℤ) - 1) - itemBound lo i).toNat / 2 := rfl

/-- The `x`-coordinate of the start of the linker of an item: `1`, or an even column in
`[2, N - 2]`. -/
theorem prevOut_x (hJ : Normalised J) {lo : Fin J.sizes.length → ℕ} (hlo : Placed J lo)
    (i : Fin J.sizes.length) :
    prevOut lo i 0 = 1 ∨
      (2 ≤ prevOut lo i 0 ∧ prevOut lo i 0 ≤ N J - 2 ∧ prevOut lo i 0 % 2 = 0) := by
  rcases prevOut_cases lo i with ⟨-, hp⟩ | ⟨j, -, hp⟩
  · left; simp [hp]
  · right
    have := lastCol_range hJ hlo j
    have := lastCol_even hJ lo j
    simp only [hp, pt_apply_zero]
    omega

/-- The `x`-coordinate of a first port: `N + 2`, `1`, or an even column in `[2, N - 2]`. -/
theorem pp_x (hJ : Normalised J) {lo : Fin J.sizes.length → ℕ} (hlo : Placed J lo)
    (i : Fin (J.sizes.length + 1)) :
    pp J lo i 0 = N J + 2 ∨ pp J lo i 0 = 1 ∨
      (2 ≤ pp J lo i 0 ∧ pp J lo i 0 ≤ N J - 2 ∧ pp J lo i 0 % 2 = 0) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · left; simp [p₀]
  · right; exact prevOut_x hJ hlo i

/-- The `x`-coordinate of a second port: `N - 1`, or an odd column in `[2, N - 2]`. -/
theorem qq_x (hJ : Normalised J) {lo : Fin J.sizes.length → ℕ} (hlo : Placed J lo)
    (i : Fin (J.sizes.length + 1)) :
    qq J lo i 0 = N J - 1 ∨
      (2 ≤ qq J lo i 0 ∧ qq J lo i 0 ≤ N J - 2 ∧ qq J lo i 0 % 2 = 1) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · left; simp [q₀]
  · right
    have := firstCol_range hJ hlo i
    have := firstCol_odd hJ lo i
    simp only [qq_succ, itemIn, pt_apply_zero]
    omega

end Linkers

open Linkers in
theorem exists_linkers {J : Packing.Instance} (hJ : Normalised J)
    {lo : Fin J.sizes.length → ℕ} (hlo : Placed J lo) :
    ∃ mid : Fin (J.sizes.length + 1) → List Site,
      (mid 0).length + 5 = linkerLength J ∧
      (∀ i : Fin J.sizes.length, (mid i.succ).length + 2 = linkerLength J) ∧
      (p₀ J :: (mid 0 ++ [q₀ J])).IsChain cubicLattice.Adj ∧
      (∀ i : Fin J.sizes.length,
        (prevOut lo i :: (mid i.succ ++ [itemIn lo i])).IsChain cubicLattice.Adj) ∧
      (∀ i, (mid i).Nodup) ∧
      (∀ i j, i ≠ j → ∀ s ∈ mid i, s ∉ mid j) ∧
      (∀ i, ∀ s ∈ mid i, ¬ InBox J s) := by
  have hn := ten_le_side hJ
  obtain ⟨m, hm⟩ := side_even hJ
  have hk := sizes_length_pos hJ
  have hN := N_eq_side J
  have hp : ∀ i, -1 ≤ pp J lo i 1 ∧ -3 ≤ pp J lo i 2 := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [pp_zero, p₀, pt_apply_one, pt_apply_two]; omega
    · rcases prevOut_cases lo i with ⟨-, hp⟩ | ⟨j, -, hp⟩ <;>
        simp only [pp_succ, hp, pt_apply_one, pt_apply_two] <;> omega
  have hq : ∀ i, -1 ≤ qq J lo i 1 ∧ -3 ≤ qq J lo i 2 := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [qq_zero, q₀, pt_apply_one, pt_apply_two]; omega
    · simp only [qq_succ, itemIn, pt_apply_one, pt_apply_two]; omega
  have hpp : ∀ i j, i ≠ j → pp J lo i 0 ≠ pp J lo j 0 := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
    · exact absurd rfl hij
    · have := prevOut_x hJ hlo j
      simp only [pp_zero, pp_succ, p₀, pt_apply_zero]; omega
    · have := prevOut_x hJ hlo i
      simp only [pp_zero, pp_succ, p₀, pt_apply_zero]; omega
    · have hij' : i ≠ j := fun h => hij (congrArg Fin.succ h)
      simp only [pp_succ]
      rcases prevOut_cases lo i with ⟨hi, hpi⟩ | ⟨i', hi, hpi⟩ <;>
        rcases prevOut_cases lo j with ⟨hj, hpj⟩ | ⟨j', hj, hpj⟩ <;>
        rw [hpi, hpj] <;> simp only [pt_apply_zero]
      · exact absurd (Fin.ext (by omega)) hij'
      · have := lastCol_range hJ hlo j'; omega
      · have := lastCol_range hJ hlo i'; omega
      · intro h
        have := lastCol_inj hJ hlo h
        subst this
        exact hij' (Fin.ext (by omega))
  have hqq : ∀ i j, i ≠ j → qq J lo i 0 ≠ qq J lo j 0 := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
    · exact absurd rfl hij
    · have := qq_x hJ hlo j.succ
      simp only [qq_succ, itemIn, pt_apply_zero] at this
      have := firstCol_range hJ hlo j
      simp only [qq_zero, qq_succ, q₀, itemIn, pt_apply_zero]; omega
    · have := firstCol_range hJ hlo i
      simp only [qq_zero, qq_succ, q₀, itemIn, pt_apply_zero]; omega
    · have hij' : i ≠ j := fun h => hij (congrArg Fin.succ h)
      simp only [qq_succ, itemIn, pt_apply_zero]
      exact fun h => hij' (firstCol_inj hJ hlo h)
  have hpq : ∀ i j, pp J lo i 0 ≠ qq J lo j 0 := by
    intro i j
    have := pp_x hJ hlo i
    have := qq_x hJ hlo j
    omega
  have hpW : ∀ i, ∀ t : ℤ, 1 ≤ t →
      pt (pp J lo i 0) (pp J lo i 1 - t) (pp J lo i 2) ∉ {s | InBox J s} := by
    intro i t ht
    rw [Set.mem_setOf_eq]
    refine Fin.cases ?_ (fun i => ?_) i
    · apply not_inBox <;> simp only [pp_zero, p₀, pt_apply_zero, pt_apply_one] <;> omega
    · have : pp J lo i.succ 1 = -1 := by
        rcases prevOut_cases lo i with ⟨-, hp⟩ | ⟨j, -, hp⟩ <;> simp [hp]
      apply not_inBox <;> simp only [this, pt_apply_one] <;> omega
  have hqW : ∀ i, ∀ t : ℤ, 1 ≤ t →
      pt (qq J lo i 0) (qq J lo i 1 - t) (qq J lo i 2) ∉ {s | InBox J s} := by
    intro i t ht
    rw [Set.mem_setOf_eq]
    refine Fin.cases ?_ (fun i => ?_) i
    · apply not_inBox <;> simp only [qq_zero, q₀, pt_apply_two, pt_apply_one] <;> omega
    · apply not_inBox <;> simp only [qq_succ, itemIn, pt_apply_one] <;> omega
  obtain ⟨mid, hlen, hchain, hnd, hdis, hW, -⟩ :=
    routes {s | InBox J s} (-1) (-3) (fun w hw => inBox_bounds hw) (J.sizes.length + 1)
      (pp J lo) (qq J lo) (ee J lo) hp hq hpp hqq hpq hpW hqW
  refine ⟨mid, ?_, ?_, ?_, ?_, ?_, hdis, ?_⟩
  · have h := hlen 0
    simp only [Fin.val_zero, pp_zero, qq_zero, ee_zero, routeBound, p₀, q₀, pt_apply_zero,
      pt_apply_one, pt_apply_two] at h
    rw [abs_of_nonneg (by omega)] at h
    unfold linkerLength
    push_cast at h
    omega
  · intro i
    have h := hlen i.succ
    obtain ⟨h1, h2⟩ := itemBound_spec hJ hlo i
    have hb : routeBound (-1) (-3) i.succ.val (pp J lo i.succ) (qq J lo i.succ) =
        itemBound lo i := by
      simp [itemBound]
    rw [hb, ee_succ] at h
    unfold linkerLength
    omega
  · simpa using hchain 0
  · intro i; simpa using hchain i.succ
  · intro i
    have := hnd i
    rw [List.nodup_cons, List.nodup_append] at this
    exact this.2.1
  · intro i s hs
    exact hW i s hs

end ProteinFolding.Shelf

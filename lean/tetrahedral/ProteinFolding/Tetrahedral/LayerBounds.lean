import ProteinFolding.Tetrahedral.GapBoundary
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Telescoping layer bounds and the one-dimensional relaxation

The two imbalance inequalities telescope from the empty layers outside a
finite occupied set. Together with the intersecting-chain bound this gives
s_k ≤ min(x_k, C-x_k, β_(k-1) β_k), the input to Sections 4 and 5.2.
-/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

def totalRuns (S : Finset Site) : ℕ := ∑ j ∈ activeGaps S, gapRunCount S j

def runsBefore (S : Finset Site) (k : ℤ) : ℕ :=
  ∑ j ∈ (activeGaps S).filter (fun j => j < k), gapRunCount S j

def runsFrom (S : Finset Site) (k : ℤ) : ℕ :=
  ∑ j ∈ (activeGaps S).filter (fun j => k ≤ j), gapRunCount S j

theorem layer_upper_telescoping (S : Finset Site) (a : ℤ) (n : ℕ) :
    (finiteLayer S (a + n)).card ≤ (finiteLayer S a).card +
      ∑ i ∈ Finset.range n, gapRunCount S (a + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (layer_imbalance_bound S (a + n)).2
    rw [Finset.sum_range_succ]
    have heq : a + ((n + 1 : ℕ) : ℤ) = a + (n : ℤ) + 1 := by omega
    rw [heq]
    omega

theorem layer_lower_telescoping (S : Finset Site) (a : ℤ) (n : ℕ) :
    (finiteLayer S a).card ≤ (finiteLayer S (a + n)).card +
      ∑ i ∈ Finset.range n, gapRunCount S (a + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (layer_imbalance_bound S (a + n)).1
    rw [Finset.sum_range_succ]
    have heq : a + ((n + 1 : ℕ) : ℤ) = a + (n : ℤ) + 1 := by omega
    rw [heq]
    omega

theorem nat_sum_le_of_support_subset {α : Type*} [DecidableEq α]
    (A B : Finset α) (f : α → ℕ) (h : ∀ j ∈ A, j ∉ B → f j = 0) :
    (∑ j ∈ A, f j) ≤ ∑ j ∈ B, f j := by
  have heq : (∑ j ∈ A ∩ B, f j) = ∑ j ∈ A, f j :=
    Finset.sum_subset Finset.inter_subset_left (by
      intro j hj hnot
      exact h j hj (fun hB => hnot (Finset.mem_inter.mpr ⟨hj, hB⟩)))
  rw [← heq]
  exact Finset.sum_le_sum_of_subset Finset.inter_subset_right

theorem range_run_sum_le (S : Finset Site) (a : ℤ) (n : ℕ) (T : Finset ℤ)
    (hT : ∀ i ∈ Finset.range n, a + (i : ℤ) ∈ activeGaps S → a + (i : ℤ) ∈ T) :
    (∑ i ∈ Finset.range n, gapRunCount S (a + i)) ≤ ∑ j ∈ T, gapRunCount S j := by
  have heq : (∑ j ∈ (Finset.range n).image (fun i : ℕ => a + (i : ℤ)), gapRunCount S j) =
      ∑ i ∈ Finset.range n, gapRunCount S (a + i) :=
    Finset.sum_image (by
      intro i _ j _ hij
      change a + (i : ℤ) = a + (j : ℤ) at hij
      omega)
  rw [← heq]
  apply nat_sum_le_of_support_subset
  intro j hj hnot
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact gapRunCount_zero_of_not_active (fun ha => hnot (hT i hi ha))

/-- Section 4's prefix bound, telescoping from an empty layer below S. -/
theorem layer_card_le_runsBefore (S : Finset Site) (k : ℤ) :
    (finiteLayer S k).card ≤ runsBefore S k := by
  rcases (finiteLayer S k).eq_empty_or_nonempty with hnil | hne
  · simp [hnil]
  obtain ⟨q, hq⟩ := hne
  have hqS := (Finset.mem_filter.mp hq).1
  have hqk := (Finset.mem_filter.mp hq).2
  obtain ⟨p, _, hmin⟩ := Finset.exists_min_image S (fun p => p.val 0) ⟨q, hqS⟩
  let a := p.val 0 - 1
  have hbelow : ∀ r ∈ S, a < r.val 0 := by
    intro r hr
    have h := hmin r hr
    dsimp [a]
    omega
  have hzero : (finiteLayer S a).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have h := Finset.mem_filter.mp hr
    have hb := hbelow r h.1
    omega
  have ha : a ≤ k := by have h := hbelow q hqS; omega
  let n := (k - a).toNat
  have hend : a + (n : ℤ) = k := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have h := layer_upper_telescoping S a n
  rw [hend, hzero, zero_add] at h
  apply h.trans
  apply range_run_sum_le
  intro i hi hactive
  apply Finset.mem_filter.mpr
  refine ⟨hactive, ?_⟩
  have hn := Finset.mem_range.mp hi
  omega

/-- Section 4's suffix bound, telescoping to an empty layer above S. -/
theorem layer_card_le_runsFrom (S : Finset Site) (k : ℤ) :
    (finiteLayer S k).card ≤ runsFrom S k := by
  rcases (finiteLayer S k).eq_empty_or_nonempty with hnil | hne
  · simp [hnil]
  obtain ⟨q, hq⟩ := hne
  have hqS := (Finset.mem_filter.mp hq).1
  have hqk := (Finset.mem_filter.mp hq).2
  obtain ⟨p, _, hmax⟩ := Finset.exists_max_image S (fun p => p.val 0) ⟨q, hqS⟩
  let b := p.val 0 + 1
  have habove : ∀ r ∈ S, r.val 0 < b := by
    intro r hr
    have h := hmax r hr
    dsimp [b]
    omega
  have hzero : (finiteLayer S b).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have h := Finset.mem_filter.mp hr
    have hb := habove r h.1
    omega
  have hk : k ≤ b := by have h := habove q hqS; omega
  let n := (b - k).toNat
  have hend : k + (n : ℤ) = b := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have h := layer_lower_telescoping S k n
  rw [hend, hzero, zero_add] at h
  apply h.trans
  apply range_run_sum_le
  intro i _ hactive
  exact Finset.mem_filter.mpr ⟨hactive, by omega⟩

theorem runsBefore_add_runsFrom (S : Finset Site) (k : ℤ) :
    runsBefore S k + runsFrom S k = totalRuns S := by
  unfold runsBefore runsFrom totalRuns
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < k
  · have hn : ¬ k ≤ j := by omega
    simp [hj, hn]
  · have hn : k ≤ j := by omega
    simp [hj, hn]

/-- The complete layer bound used in the one-dimensional relaxation. -/
theorem layer_card_le_relaxation (S : Finset Site) (k : ℤ) :
    (finiteLayer S k).card ≤ min (runsBefore S k)
      (min (totalRuns S - runsBefore S k) (gapRunCount S (k - 1) * gapRunCount S k)) := by
  apply le_min
  · exact layer_card_le_runsBefore S k
  · apply le_min
    · have h := layer_card_le_runsFrom S k
      have heq := runsBefore_add_runsFrom S k
      omega
    · exact layer_card_le_run_product S k

def activeLayers (S : Finset Site) : Finset ℤ := S.image (fun p => p.val 0)

theorem card_eq_sum_layer_card (S : Finset Site) :
    S.card = ∑ k ∈ activeLayers S, (finiteLayer S k).card := by
  exact Finset.card_eq_sum_card_fiberwise
    (f := fun p : Site => p.val 0) (t := activeLayers S)
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)

/-- A finite-sum form of the volume relaxation before converting to compositions. -/
theorem card_le_sum_layer_relaxation (S : Finset Site) :
    S.card ≤ ∑ k ∈ activeLayers S, min (runsBefore S k)
      (min (totalRuns S - runsBefore S k) (gapRunCount S (k - 1) * gapRunCount S k)) := by
  rw [card_eq_sum_layer_card]
  exact Finset.sum_le_sum (fun k _ => layer_card_le_relaxation S k)

theorem boundaryCount_eq_twice_totalRuns (S : Finset Site) :
    boundaryCount S = 2 * totalRuns S := boundaryCount_eq_twice_sum_runs S

end ProteinFolding.Tetrahedral

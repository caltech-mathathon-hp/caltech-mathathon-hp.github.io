import ProteinFolding.Tetrahedral.OctahedralEdgeParametrization
import ProteinFolding.Tetrahedral.TetherDistance

/-!
# Direction counts for exterior links

A cancelled pair consists of one A-to-B bond and one B-to-A bond of the
same direction. Every such pair loses two units in every directed height.
-/

namespace ProteinFolding.Tetrahedral

def positivePathCount (f : ℕ → Site) (d : ℕ → Fin 4) (n : ℕ) (r : Fin 4) : ℕ :=
  ∑ i ∈ Finset.range n, if InASublattice (f i).val ∧ d i = r then 1 else 0

def negativePathCount (f : ℕ → Site) (d : ℕ → Fin 4) (n : ℕ) (r : Fin 4) : ℕ :=
  ∑ i ∈ Finset.range n, if InBSublattice (f i).val ∧ d i = r then 1 else 0

theorem positivePathCount_succ (f : ℕ → Site) (d : ℕ → Fin 4) (n : ℕ) (r : Fin 4) :
    positivePathCount f d (n + 1) r = positivePathCount f d n r +
      if InASublattice (f n).val ∧ d n = r then 1 else 0 := by
  simp only [positivePathCount, Finset.sum_range_succ]

theorem negativePathCount_succ (f : ℕ → Site) (d : ℕ → Fin 4) (n : ℕ) (r : Fin 4) :
    negativePathCount f d (n + 1) r = negativePathCount f d n r +
      if InBSublattice (f n).val ∧ d n = r then 1 else 0 := by
  simp only [negativePathCount, Finset.sum_range_succ]

theorem pathCount_total (f : ℕ → Site) (d : ℕ → Fin 4) (n : ℕ) :
    (∑ r : Fin 4, positivePathCount f d n r) +
      (∑ r : Fin 4, negativePathCount f d n r) = n := by
  induction n with
  | zero => simp [positivePathCount, negativePathCount]
  | succ n ih =>
    simp_rw [positivePathCount_succ, negativePathCount_succ]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rcases (f n).property with hpA | hpB
    · have hnB : ¬ InBSublattice (f n).val := fun h => sublattices_disjoint _ hpA h
      simp only [hpA, hnB, true_and, false_and, ite_false]
      simp only [Finset.sum_const_zero]
      have hs : (∑ r : Fin 4, if d n = r then 1 else 0) = 1 := by simp [eq_comm]
      omega
    · have hnA : ¬ InASublattice (f n).val := fun h => sublattices_disjoint _ h hpB
      simp only [hpB, hnA, true_and, false_and, ite_false]
      simp only [Finset.sum_const_zero]
      have hs : (∑ r : Fin 4, if d n = r then 1 else 0) = 1 := by simp [eq_comm]
      omega

theorem path_tetraLift_difference (f : ℕ → Site) (d : ℕ → Fin 4) (n : ℕ)
    (hstep : ∀ i < n, f (i + 1) = step (f i) (d i)) (r : Fin 4) :
    tetraLift (f n) r - tetraLift (f 0) r =
      (positivePathCount f d n r : ℤ) - (negativePathCount f d n r : ℤ) := by
  induction n with
  | zero => simp [positivePathCount, negativePathCount]
  | succ n ih =>
    have hp := ih (fun i hi => hstep i (by omega))
    rw [hstep n (by omega), positivePathCount_succ, negativePathCount_succ]
    rcases (f n).property with hpA | hpB
    · have hnB : ¬ InBSublattice (f n).val := fun h => sublattices_disjoint _ hpA h
      rw [tetraLift_step_A hpA]
      by_cases hd : d n = r
      · simp only [hpA, hnB, true_and, false_and, ite_false, hd, ite_true]
        push_cast
        omega
      · simp only [hpA, hnB, true_and, false_and, ite_false, if_neg hd, if_neg (Ne.symm hd)]
        push_cast
        omega
    · have hnA : ¬ InASublattice (f n).val := fun h => sublattices_disjoint _ h hpB
      rw [tetraLift_step_B hpB]
      by_cases hd : d n = r
      · simp only [hpB, hnA, true_and, false_and, ite_false, hd, ite_true]
        push_cast
        omega
      · simp only [hpB, hnA, true_and, false_and, ite_false, if_neg hd, if_neg (Ne.symm hd)]
        push_cast
        omega

theorem tetraCoordinate_difference_independent (m : ℕ) (p q : Coordinates) (r : Fin 4) :
    tetraCoordinate m q r - tetraCoordinate m p r =
      tetraCoordinate 1 q r - tetraCoordinate 1 p r := by
  fin_cases r <;> dsimp [tetraCoordinate, octRadius] <;> omega

theorem path_tetraCoordinate_difference (m : ℕ) (f : ℕ → Site) (d : ℕ → Fin 4) (n : ℕ)
    (hstep : ∀ i < n, f (i + 1) = step (f i) (d i)) (r : Fin 4) :
    tetraCoordinate m (f n).val r = tetraCoordinate m (f 0).val r +
      4 * ((positivePathCount f d n r : ℤ) - (negativePathCount f d n r : ℤ)) -
      (siteCharge (f n) - siteCharge (f 0)) := by
  have h := path_tetraLift_difference f d n hstep r
  have hp := tetraLift_spec (f 0) r
  have hq := tetraLift_spec (f n) r
  have hm := tetraCoordinate_difference_independent m (f 0).val (f n).val r
  omega

theorem positivePathCount_ge_one (f : ℕ → Site) (d : ℕ → Fin 4) {n i : ℕ}
    (hi : i < n) (hp : InASublattice (f i).val) : 1 ≤ positivePathCount f d n (d i) := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.range n) =>
    Nat.zero_le (if InASublattice (f j).val ∧ d j = d i then 1 else 0))
      (Finset.mem_range.mpr hi)
  simpa only [positivePathCount, hp, eq_self_iff_true, and_self, ite_true] using h

theorem negativePathCount_ge_one (f : ℕ → Site) (d : ℕ → Fin 4) {n i : ℕ}
    (hi : i < n) (hp : InBSublattice (f i).val) : 1 ≤ negativePathCount f d n (d i) := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.range n) =>
    Nat.zero_le (if InBSublattice (f j).val ∧ d j = d i then 1 else 0))
      (Finset.mem_range.mpr hi)
  simpa only [negativePathCount, hp, eq_self_iff_true, and_self, ite_true] using h

theorem positivePathCount_ge_two (f : ℕ → Site) (d : ℕ → Fin 4) {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j)
    (hp : InASublattice (f i).val) (hq : InASublattice (f j).val) (hd : d i = d j) :
    2 ≤ positivePathCount f d n (d i) := by
  have hsub : ({i, j} : Finset ℕ) ⊆ Finset.range n := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact Finset.mem_range.mpr hi
    · exact Finset.mem_range.mpr ((Finset.mem_singleton.mp hk) ▸ hj)
  have h := Finset.sum_le_sum_of_subset hsub (f := fun k =>
    if InASublattice (f k).val ∧ d k = d i then 1 else 0)
  rw [Finset.sum_pair hij] at h
  simpa [positivePathCount, hij, hp, hq, hd] using h

theorem negativePathCount_ge_two (f : ℕ → Site) (d : ℕ → Fin 4) {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j)
    (hp : InBSublattice (f i).val) (hq : InBSublattice (f j).val) (hd : d i = d j) :
    2 ≤ negativePathCount f d n (d i) := by
  have hsub : ({i, j} : Finset ℕ) ⊆ Finset.range n := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact Finset.mem_range.mpr hi
    · exact Finset.mem_range.mpr ((Finset.mem_singleton.mp hk) ▸ hj)
  have h := Finset.sum_le_sum_of_subset hsub (f := fun k =>
    if InBSublattice (f k).val ∧ d k = d i then 1 else 0)
  rw [Finset.sum_pair hij] at h
  simpa [negativePathCount, hij, hp, hq, hd] using h

def directionLoss (a b : Fin 4) (P Q : Fin 4 → ℕ) (r : Fin 4) : ℤ :=
  (P r : ℤ) + (Q r : ℤ) - (if r = a then (P r : ℤ) - (Q r : ℤ) else 0) +
    (if r = b then (P r : ℤ) - (Q r : ℤ) else 0)

theorem directionLoss_ge_min {a b : Fin 4} (_hab : a ≠ b) (P Q : Fin 4 → ℕ) (r : Fin 4) :
    2 * (min (P r) (Q r) : ℕ) ≤ directionLoss a b P Q r := by
  have hp := Nat.min_le_left (P r) (Q r)
  have hq := Nat.min_le_right (P r) (Q r)
  dsimp [directionLoss]
  split_ifs <;> omega

theorem sum_directionLoss (a b : Fin 4) (P Q : Fin 4 → ℕ) :
    (∑ r : Fin 4, directionLoss a b P Q r) =
      (∑ r : Fin 4, (P r : ℤ)) + (∑ r : Fin 4, (Q r : ℤ)) -
      (((P a : ℤ) - (Q a : ℤ)) - ((P b : ℤ) - (Q b : ℤ))) := by
  simp [directionLoss, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  omega

theorem sum_directionLoss_ge_cancellation {a b : Fin 4} (hab : a ≠ b) (P Q : Fin 4 → ℕ) :
    2 * (∑ r : Fin 4, ((min (P r) (Q r) : ℕ) : ℤ)) ≤ ∑ r : Fin 4, directionLoss a b P Q r := by
  have h := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin 4))) =>
    directionLoss_ge_min hab P Q r)
  simpa only [Finset.mul_sum] using h

theorem neutral_counts_eq_of_loss_eq {a b : Fin 4} (hab : a ≠ b) (P Q : Fin 4 → ℕ)
    (heq : (∑ r : Fin 4, directionLoss a b P Q r) =
      2 * (∑ r : Fin 4, ((min (P r) (Q r) : ℕ) : ℤ))) {r : Fin 4} (hra : r ≠ a) (hrb : r ≠ b) :
    P r = Q r := by
  let slack : Fin 4 → ℤ := fun s => directionLoss a b P Q s - 2 * (min (P s) (Q s) : ℕ)
  have hnonneg : ∀ s, 0 ≤ slack s := by
    intro s
    have h := directionLoss_ge_min hab P Q s
    dsimp [slack]
    omega
  have hsum : (∑ s : Fin 4, slack s) = 0 := by
    simp only [slack, Finset.sum_sub_distrib, ← Finset.mul_sum]
    omega
  have hle := Finset.single_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin 4))) =>
    hnonneg s) (Finset.mem_univ r)
  rw [hsum] at hle
  dsimp [slack, directionLoss] at hle
  rw [if_neg hra, if_neg hrb] at hle
  have hp := Nat.min_le_left (P r) (Q r)
  have hq := Nat.min_le_right (P r) (Q r)
  omega

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.FarFieldApproachBounds

namespace ProteinFolding.Tetrahedral.FarField

theorem quarter_time_div (u j r : ℤ) (hu : 0 < u) (hr : 0 ≤ r) (hr' : r < u) :
    (j * u + r) / u = j := by
  rw [Int.mul_add_ediv_right _ _ (by omega : u ≠ 0), Int.ediv_eq_zero_of_lt hr hr', add_zero]

theorem approach_interval_profile (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (humin : 3 ≤ u)
    (j r a t : ℤ) (hr : 0 ≤ r) (hr' : r < u) (ha : a % 2 = 1) (hroom : |a| + 8 < u)
    (ht0 : j * u + r ≤ t) (ht1 : t ≤ nextPositiveQuarter j * u + targetRadius u a) :
    let p := levelWalk R u x₀ hR hu hx hs t
    (X (levelPoint R u x₀ hR hu hx hs j r) - 4 ≤ X p ∧
      X p ≤ X (levelPoint R u x₀ hR hu hx hs j r) + 1) ∧
    (PositiveQuadrant R p → alpha R p ≤ a) ∧
    (PositiveQuadrant R p → alpha R p = a →
      p = levelPoint R u x₀ hR hu hx hs (nextPositiveQuarter j) (targetRadius u a)) := by
  have hu0 : 0 < u := by omega
  have hJ := nextPositiveQuarter_spec j
  have hrad := targetRadius_spec u a hu ha hroom
  have hdiv0 := Int.ediv_le_ediv hu0 ht0
  have hdiv1 := Int.ediv_le_ediv hu0 ht1
  rw [quarter_time_div u j r hu0 hr hr'] at hdiv0
  rw [quarter_time_div u (nextPositiveQuarter j) (targetRadius u a) hu0 (by omega) (by omega)] at hdiv1
  have hrem0 := Int.emod_nonneg t (by omega : u ≠ 0)
  have hrem1 := Int.emod_lt_of_pos t hu0
  have hxw := levelPoint_x_window R u x₀ hR hu hx hs j (t / u) (t % u) hdiv0 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [levelWalk]
    simp only [levelPoint_x] at hxw ⊢
    omega
  · intro hp
    have hp' := (levelPoint_positive_iff R u x₀ hR hu hx hs (t / u) (t % u) hrem0 hrem1).1 hp
    have hq : t / u = nextPositiveQuarter j := by omega
    have htime := Int.ediv_mul_add_emod t u
    rw [hq] at htime
    have hrem : t % u ≤ targetRadius u a := by omega
    change alpha R (levelPoint R u x₀ hR hu hx hs (t / u) (t % u)) ≤ a
    rw [levelPoint_alpha_zero_quarter R u x₀ hR hu hx hs (t / u) (t % u) hp'.1 hrem0 (by omega)]
    omega
  · intro hp hα
    have hp' := (levelPoint_positive_iff R u x₀ hR hu hx hs (t / u) (t % u) hrem0 hrem1).1 hp
    have hq : t / u = nextPositiveQuarter j := by omega
    have halpha := levelPoint_alpha_zero_quarter R u x₀ hR hu hx hs (t / u) (t % u) hp'.1 hrem0 (by omega)
    change alpha R (levelPoint R u x₀ hR hu hx hs (t / u) (t % u)) = a at hα
    have hrem : t % u = targetRadius u a := by omega
    simp only [levelWalk, hq, hrem]

structure ApproachData (R u a : ℤ) (T : Site) where
  sites : ℕ
  path : Fold tetrahedralLattice sites
  sites_pos : 0 < sites
  target : Site
  first : ∀ i, i.val = 0 → path.pos i = T
  last : ∀ i, i.val + 1 = sites → path.pos i = target
  level : ∀ i, rho R (path.pos i) = u
  window : ∀ i, X T - 4 ≤ X (path.pos i) ∧ X (path.pos i) ≤ X T + 1
  target_positive : PositiveQuadrant R target
  target_alpha : alpha R target = a
  length_bound : (sites : ℤ) ≤ 4 * u + 5
  alpha_limit : ∀ i, PositiveQuadrant R (path.pos i) → alpha R (path.pos i) ≤ a
  hits_target : ∀ i, PositiveQuadrant R (path.pos i) → alpha R (path.pos i) = a → path.pos i = target

/-- Part C's level-curve approach is an actual finite injective lattice path.
The explicit quarter construction crosses at most three bends, and in (+,+)
it reaches alpha=a for the first time at its final site. -/
theorem levelApproach_exists (R u x₀ a : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (humin : 3 ≤ u)
    (ha : a % 2 = 1) (hroom : |a| + 8 < u) (T : Site) (hT : rho R T = u)
    (hα : |alpha R T| + 4 ≤ a) : Nonempty (ApproachData R u a T) := by
  have hu0 : 0 < u := by omega
  obtain ⟨j, r, hr, hr', heT⟩ := levelPoint_exhaustive R u x₀ hR hu hx hs hu0 T hT
  have hα' : |alpha R (levelPoint R u x₀ hR hu hx hs j r)| + 4 ≤ a := by rw [heT]; exact hα
  have htime := approach_time_bounds R u x₀ hR hu hx hs humin j r a hr hr' ha hroom hα'
  have hrad := targetRadius_spec u a hu ha hroom
  have hJ := nextPositiveQuarter_spec j
  let start := j * u + r
  let stop := nextPositiveQuarter j * u + targetRadius u a
  let edges := (stop - start).toNat
  have he : (edges : ℤ) = stop - start := Int.toNat_of_nonneg (by dsimp only [start, stop]; omega)
  let f := intervalFold (levelWalk R u x₀ hR hu hx hs)
    (levelWalk_injective R u x₀ hR hu hx hs hu0)
    (levelWalk_adj R u x₀ hR hu hx hs humin) start edges true
  let S := levelPoint R u x₀ hR hu hx hs (nextPositiveQuarter j) (targetRadius u a)
  have hprofile (i : Fin (edges + 1)) := approach_interval_profile R u x₀ hR hu hx hs humin
    j r a (start + i.val) hr hr' ha hroom (by dsimp only [start]; omega)
    (by have hi := i.isLt; dsimp only [start, stop] at he ⊢; omega)
  refine ⟨{
    sites := edges + 1
    path := f
    sites_pos := by omega
    target := S
    first := ?_
    last := ?_
    level := ?_
    window := ?_
    target_positive := ?_
    target_alpha := ?_
    length_bound := ?_
    alpha_limit := ?_
    hits_target := ?_
  }⟩
  · intro i hi
    change levelWalk R u x₀ hR hu hx hs (start + i.val) = T
    rw [hi, Int.natCast_zero, add_zero]
    rw [levelWalk_at R u x₀ hR hu hx hs hu0 j r hr hr', heT]
  · intro i hi
    change levelWalk R u x₀ hR hu hx hs (start + i.val) = S
    have hstop : start + (i.val : ℤ) = stop := by omega
    rw [hstop]
    exact levelWalk_at R u x₀ hR hu hx hs hu0 (nextPositiveQuarter j) (targetRadius u a) (by omega) (by omega)
  · intro i
    exact levelWalk_rho R u x₀ hR hu hx hs hu0 (start + i.val)
  · intro i
    have h := (hprofile i).1
    rw [heT] at h
    exact h
  · exact (levelPoint_positive_iff R u x₀ hR hu hx hs _ _ (by omega) (by omega)).2 ⟨hJ.2.2, by omega⟩
  · have h := levelPoint_alpha_zero_quarter R u x₀ hR hu hx hs
      (nextPositiveQuarter j) (targetRadius u a) hJ.2.2 (by omega) (by omega)
    change alpha R (levelPoint R u x₀ hR hu hx hs (nextPositiveQuarter j) (targetRadius u a)) = a
    rw [h]
    omega
  · dsimp only [start, stop] at he
    omega
  · intro i hp
    exact (hprofile i).2.1 hp
  · intro i hp halpha
    exact (hprofile i).2.2 hp halpha

end ProteinFolding.Tetrahedral.FarField

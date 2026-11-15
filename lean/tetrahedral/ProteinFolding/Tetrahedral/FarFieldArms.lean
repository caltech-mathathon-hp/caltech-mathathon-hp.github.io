import ProteinFolding.Tetrahedral.FarFieldLevelCurves

/-! Explicit outward radial arms. Each step increases both positive
transformed coordinates by one, preserves alpha, and raises rho by two.
The X coordinate alternates on two consecutive integers. -/

namespace ProteinFolding.Tetrahedral.FarField

def armCoordinates (p : Site) (t : ℤ) : Coordinates :=
  ![p.val 0 + (if InASublattice p.val then t % 2 else -(t % 2)), p.val 1 + t, p.val 2 + t]

theorem armCoordinates_site (p : Site) (t : ℤ) : IsLatticeSite (armCoordinates p t) := by
  have ht : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases p.property with hp | hp
  · have h0 := hp.1 0
    have h1 := hp.1 1
    have h2 := hp.1 2
    have hs := hp.2
    dsimp only [coordinateSum] at hs
    rcases ht with ht | ht
    · left; constructor
      · intro k; fin_cases k <;> simp [armCoordinates, hp, ht] <;> omega
      · simp [armCoordinates, coordinateSum, hp, ht]; omega
    · right; constructor
      · intro k; fin_cases k <;> simp [armCoordinates, hp, ht] <;> omega
      · simp [armCoordinates, coordinateSum, hp, ht]; omega
  · have hA := (inB_iff_not_inA p).1 hp
    have h0 := hp.1 0
    have h1 := hp.1 1
    have h2 := hp.1 2
    have hs := hp.2
    dsimp only [coordinateSum] at hs
    rcases ht with ht | ht
    · right; constructor
      · intro k; fin_cases k <;> simp [armCoordinates, hA, ht] <;> omega
      · simp [armCoordinates, coordinateSum, hA, ht]; omega
    · left; constructor
      · intro k; fin_cases k <;> simp [armCoordinates, hA, ht] <;> omega
      · simp [armCoordinates, coordinateSum, hA, ht]; omega

def arm (p : Site) (t : ℤ) : Site := ⟨armCoordinates p t, armCoordinates_site p t⟩

@[simp] theorem arm_zero (p : Site) : arm p 0 = p := by
  apply Subtype.ext
  funext k
  fin_cases k <;> simp [arm, armCoordinates]

theorem arm_injective (p : Site) : Function.Injective (arm p) := by
  intro t s h
  have hy := congrArg (fun q : Site => q.val 1) h
  change p.val 1 + t = p.val 1 + s at hy
  omega

theorem arm_adj (p : Site) (t : ℤ) : tetrahedralLattice.Adj (arm p t) (arm p (t + 1)) := by
  apply unit_coordinate_adj
  intro k
  have ht : t % 2 = 0 ∨ t % 2 = 1 := by omega
  have hnext : (t + 1) % 2 = 1 - t % 2 := by omega
  fin_cases k
  · by_cases hp : InASublattice p.val <;> rcases ht with ht | ht <;>
      simp [arm, armCoordinates, hp, ht, hnext] <;> omega
  · simp [arm, armCoordinates]
  · simp [arm, armCoordinates]

def armBaseX (p : Site) : ℤ := p.val 0 - if InASublattice p.val then 0 else 1

theorem arm_x_band (p : Site) (t : ℤ) :
    armBaseX p ≤ X (arm p t) ∧ X (arm p t) ≤ armBaseX p + 1 := by
  by_cases hp : InASublattice p.val <;> simp [armBaseX, X, arm, armCoordinates, hp] <;> omega

theorem arm_positive (R : ℤ) (p : Site) (t : ℤ) (hp : PositiveQuadrant R p) (ht : 0 ≤ t) :
    PositiveQuadrant R (arm p t) := by
  rcases hp with ⟨hy, hz⟩
  dsimp only [PositiveQuadrant, Y, Z] at *
  change 0 < p.val 1 + t - R ∧ 0 < p.val 2 + t - 1
  omega

theorem arm_rho_alpha (R : ℤ) (p : Site) (t : ℤ) (hp : PositiveQuadrant R p) (ht : 0 ≤ t) :
    rho R (arm p t) = rho R p + 2 * t ∧ alpha R (arm p t) = alpha R p := by
  have hq := arm_positive R p t hp ht
  simp only [rho, alpha, abs_of_pos hp.1, abs_of_pos hp.2, abs_of_pos hq.1, abs_of_pos hq.2]
  change (p.val 1 + t - R) + (p.val 2 + t - 1) = (p.val 1 - R) + (p.val 2 - 1) + 2 * t ∧
    (p.val 1 + t - R) - (p.val 2 + t - 1) = (p.val 1 - R) - (p.val 2 - 1)
  omega

theorem arms_disjoint_of_strip (R : ℤ) (p q : Site)
    (hp : PositiveQuadrant R p) (hq : PositiveQuadrant R q) (hα : alpha R p ≠ alpha R q)
    (t s : ℤ) (ht : 0 ≤ t) (hs : 0 ≤ s) : arm p t ≠ arm q s := by
  intro h
  have hpt := (arm_rho_alpha R p t hp ht).2
  have hqs := (arm_rho_alpha R q s hq hs).2
  rw [h] at hpt
  exact hα (hpt.symm.trans hqs)

def quadrantArm (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) (t : ℤ) : Site :=
  quadrantMap R hR q (arm p t)

theorem quadrantArm_adj (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) (t : ℤ) :
    tetrahedralLattice.Adj (quadrantArm R hR q p t) (quadrantArm R hR q p (t + 1)) :=
  (quadrantMap_adj_iff R hR q _ _).2 (arm_adj p t)

theorem quadrantArm_injective (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) :
    Function.Injective (quadrantArm R hR q p) :=
  (quadrantMap_injective R hR q).comp (arm_injective p)

theorem quadrantArm_rho_alpha (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) (t : ℤ)
    (hp : PositiveQuadrant R p) (ht : 0 ≤ t) :
    rho R (quadrantArm R hR q p t) = rho R p + 2 * t ∧
      alpha R (quadrantArm R hR q p t) = alpha R p := by
  simpa only [quadrantArm, quadrantMap_rho, quadrantMap_alpha] using arm_rho_alpha R p t hp ht

end ProteinFolding.Tetrahedral.FarField

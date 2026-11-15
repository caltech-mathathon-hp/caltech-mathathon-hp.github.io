import ProteinFolding.Tetrahedral.FarFieldArms
import ProteinFolding.Tetrahedral.FarFieldArbitraryAvenues

namespace ProteinFolding.Tetrahedral.FarField

def quadrantArmBaseX (q : Quadrant) (p : Site) : ℤ :=
  if q.1 then (if q.2 then armBaseX p - 2 else -armBaseX p - 1)
  else (if q.2 then 1 - armBaseX p else armBaseX p)

theorem quadrantArm_x_band (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) (t : ℤ) :
    quadrantArmBaseX q p ≤ X (quadrantArm R hR q p t) ∧
      X (quadrantArm R hR q p t) ≤ quadrantArmBaseX q p + 1 := by
  have h := arm_x_band p t
  obtain ⟨a, b⟩ := q
  cases a <;> cases b
  all_goals
    simp only [quadrantArmBaseX, quadrantArm, quadrantMap, Bool.false_eq_true, ite_false, ite_true]
    change _ ≤ _ ∧ _ ≤ _
    dsimp only [X, flipY, flipZ, flipYCoordinates, flipZCoordinates] at *
    try simp only [Matrix.cons_val_zero] at *
    omega

theorem quadrantArmBaseX_eq_iff (q : Quadrant) (p v : Site) :
    quadrantArmBaseX q p = quadrantArmBaseX q v ↔ armBaseX p = armBaseX v := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp [quadrantArmBaseX] <;> omega

theorem arm_alpha_mod (R : ℤ) (p : Site) (hp : PositiveQuadrant R p) :
    (armBaseX p + R + alpha R p - 1) % 4 = 0 := by
  have hY := hp.1
  have hZ := hp.2
  simp only [alpha, abs_of_pos hY, abs_of_pos hZ]
  rcases p.property with h | h
  · have h0 := h.1 0
    have h1 := h.1 1
    have h2 := h.1 2
    have hs := h.2
    dsimp only [coordinateSum] at hs
    simp [armBaseX, h, Y, Z]
    omega
  · have hA := (inB_iff_not_inA p).1 h
    have h0 := h.1 0
    have h1 := h.1 1
    have h2 := h.1 2
    have hs := h.2
    dsimp only [coordinateSum] at hs
    simp [armBaseX, hA, Y, Z]
    omega

theorem same_arm_band_alpha_mod (R : ℤ) (q : Quadrant) (p v : Site)
    (hp : PositiveQuadrant R p) (hv : PositiveQuadrant R v)
    (hb : quadrantArmBaseX q p = quadrantArmBaseX q v) : alpha R p % 4 = alpha R v % 4 := by
  have hb' := (quadrantArmBaseX_eq_iff q p v).1 hb
  have hp' := arm_alpha_mod R p hp
  have hv' := arm_alpha_mod R v hv
  omega

theorem separated_arm_strips (R : ℤ) (q : Quadrant) (p v : Site)
    (hp : PositiveQuadrant R p) (hv : PositiveQuadrant R v)
    (hb : quadrantArmBaseX q p = quadrantArmBaseX q v) (hne : alpha R p ≠ alpha R v) :
    alpha R p + 4 ≤ alpha R v ∨ alpha R v + 4 ≤ alpha R p := by
  have hmod := same_arm_band_alpha_mod R q p v hp hv hb
  omega

theorem quadrant_unique (R : ℤ) (q v : Quadrant) (p : Site)
    (hq : InQuadrant R q p) (hv : InQuadrant R v p) : q = v := by
  obtain ⟨a, b⟩ := q
  obtain ⟨c, d⟩ := v
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [InQuadrant] <;> omega

theorem site_eq_of_level_strip_band (R b : ℤ) (q : Quadrant) (p v : Site)
    (hp : InQuadrant R q p) (hv : InQuadrant R q v)
    (hρ : rho R p = rho R v) (hα : alpha R p = alpha R v)
    (hpx : b ≤ X p ∧ X p ≤ b + 1) (hvx : b ≤ X v ∧ X v ≤ b + 1) : p = v := by
  have hpParity : p.val 0 % 2 = p.val 1 % 2 := by
    rcases p.property with h | h <;> rw [h.1 0, h.1 1]
  have hvParity : v.val 0 % 2 = v.val 1 % 2 := by
    rcases v.property with h | h <;> rw [h.1 0, h.1 1]
  have hyz : p.val 1 = v.val 1 ∧ p.val 2 = v.val 2 := by
    obtain ⟨a, c⟩ := q
    cases a <;> cases c
    all_goals
      simp only [InQuadrant, Bool.false_eq_true, ite_false, ite_true] at hp hv
      simp only [rho, alpha] at hρ hα
      first
      | simp only [abs_of_pos hp.1, abs_of_pos hp.2, abs_of_pos hv.1, abs_of_pos hv.2] at hρ hα
      | simp only [abs_of_pos hp.1, abs_of_neg hp.2, abs_of_pos hv.1, abs_of_neg hv.2] at hρ hα
      | simp only [abs_of_neg hp.1, abs_of_pos hp.2, abs_of_neg hv.1, abs_of_pos hv.2] at hρ hα
      | simp only [abs_of_neg hp.1, abs_of_neg hp.2, abs_of_neg hv.1, abs_of_neg hv.2] at hρ hα
      dsimp only [Y, Z] at hρ hα
      omega
  have hxx : p.val 0 = v.val 0 := by
    dsimp only [X] at hpx hvx
    rw [hyz.1] at hpParity
    omega
  apply Subtype.ext
  funext k
  match k with
  | 0 => exact hxx
  | 1 => exact hyz.1
  | 2 => exact hyz.2

end ProteinFolding.Tetrahedral.FarField

import ProteinFolding.Tetrahedral.FarFieldArmStrips

namespace ProteinFolding.Tetrahedral.FarField

theorem armBaseX_even (p : Site) : armBaseX p % 2 = 0 := by
  rcases p.property with hp | hp
  · have hx := hp.1 0
    simp [armBaseX, hp]
    omega
  · have hx := hp.1 0
    have hA := (inB_iff_not_inA p).1 hp
    simp [armBaseX, hA]
    omega

theorem quadrantArmBaseX_parity (q : Quadrant) (p : Site) :
    quadrantArmBaseX q p % 2 = if q.1 = q.2 then 0 else 1 := by
  have hp := armBaseX_even p
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp [quadrantArmBaseX] <;> omega

theorem quadrantArm_quadrant (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) (t : ℤ)
    (hp : PositiveQuadrant R p) (ht : 0 ≤ t) : InQuadrant R q (quadrantArm R hR q p t) :=
  (quadrantMap_positive_iff R hR q _).2 (arm_positive R p t hp ht)

def armIdentity (R : ℤ) (q : Quadrant) (p : Site) : Quadrant × ℤ × ℤ :=
  (q, quadrantArmBaseX q p, alpha R p)

theorem arm_identity_of_intersect (R : ℤ) (hR : R % 2 = 0) (q v : Quadrant) (p s : Site)
    (hp : PositiveQuadrant R p) (hs : PositiveQuadrant R s) (t z : ℤ) (ht : 0 ≤ t) (hz : 0 ≤ z)
    (heq : quadrantArm R hR q p t = quadrantArm R hR v s z) : armIdentity R q p = armIdentity R v s := by
  have hq := quadrantArm_quadrant R hR q p t hp ht
  have hv := quadrantArm_quadrant R hR v s z hs hz
  rw [← heq] at hv
  have hquad := quadrant_unique R q v _ hq hv
  subst v
  have hbp := quadrantArm_x_band R hR q p t
  have hbs := quadrantArm_x_band R hR q s z
  rw [← heq] at hbs
  have hpp := quadrantArmBaseX_parity q p
  have hsp := quadrantArmBaseX_parity q s
  have hband : quadrantArmBaseX q p = quadrantArmBaseX q s := by omega
  have hαp := (quadrantArm_rho_alpha R hR q p t hp ht).2
  have hαs := (quadrantArm_rho_alpha R hR q s z hs hz).2
  rw [← heq] at hαs
  have hα : alpha R p = alpha R s := by omega
  simp only [armIdentity, hband, hα]

theorem positive_rho_odd (R : ℤ) (hR : R % 2 = 0) (p : Site) (hp : PositiveQuadrant R p) :
    rho R p % 2 = 1 := by
  simp only [rho, abs_of_pos hp.1, abs_of_pos hp.2]
  dsimp only [Y, Z]
  rcases p.property with h | h
  all_goals
    have hy := h.1 1
    have hz := h.1 2
    omega

theorem arm_identity_iff_rays_meet (R : ℤ) (hR : R % 2 = 0) (q v : Quadrant) (p s : Site)
    (hp : PositiveQuadrant R p) (hs : PositiveQuadrant R s) :
    armIdentity R q p = armIdentity R v s ↔
      ∃ t z : ℤ, 0 ≤ t ∧ 0 ≤ z ∧ quadrantArm R hR q p t = quadrantArm R hR v s z := by
  constructor
  · intro he
    have he' : q = v ∧ quadrantArmBaseX q p = quadrantArmBaseX v s ∧ alpha R p = alpha R s := by
      simpa only [armIdentity, Prod.mk.injEq] using he
    rcases he' with ⟨rfl, hband, hα⟩
    let U := max (rho R p) (rho R s)
    let t := (U - rho R p) / 2
    let z := (U - rho R s) / 2
    have hpodd := positive_rho_odd R hR p hp
    have hsodd := positive_rho_odd R hR s hs
    have hUodd : U % 2 = 1 := by dsimp only [U]; omega
    have ht : 0 ≤ t := by dsimp only [t, U]; omega
    have hz : 0 ≤ z := by dsimp only [z, U]; omega
    have hρp := (quadrantArm_rho_alpha R hR q p t hp ht).1
    have hρs := (quadrantArm_rho_alpha R hR q s z hs hz).1
    have hρ : rho R (quadrantArm R hR q p t) = rho R (quadrantArm R hR q s z) := by
      dsimp only [t, z] at hρp hρs ⊢
      omega
    refine ⟨t, z, ht, hz, ?_⟩
    apply site_eq_of_level_strip_band R (quadrantArmBaseX q p) q
    · exact quadrantArm_quadrant R hR q p t hp ht
    · exact quadrantArm_quadrant R hR q s z hs hz
    · exact hρ
    · rw [(quadrantArm_rho_alpha R hR q p t hp ht).2,
        (quadrantArm_rho_alpha R hR q s z hs hz).2, hα]
    · exact quadrantArm_x_band R hR q p t
    · rw [hband]
      exact quadrantArm_x_band R hR q s z
  · rintro ⟨t, z, ht, hz, he⟩
    exact arm_identity_of_intersect R hR q v p s hp hs t z ht hz he

end ProteinFolding.Tetrahedral.FarField

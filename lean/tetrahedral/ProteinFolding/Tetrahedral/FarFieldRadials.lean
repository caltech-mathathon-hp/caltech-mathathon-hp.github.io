import ProteinFolding.Tetrahedral.FarFieldArmIdentity
import ProteinFolding.Tetrahedral.FarFieldPathTools

namespace ProteinFolding.Tetrahedral.FarField

def radialPosition (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (E : Site) (t : ℤ) : Site :=
  quadrantArm R hR q (quadrantUnmap R hR q E) t

@[simp] theorem radialPosition_zero (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (E : Site) :
    radialPosition R hR q E 0 = E := by
  simp [radialPosition, quadrantArm, arm_zero]

theorem radialPosition_positive_base (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (E : Site)
    (hq : InQuadrant R q E) : PositiveQuadrant R (quadrantUnmap R hR q E) :=
  (quadrantMap_positive_iff R hR q _).1 (by simpa only [quadrantMap_unmap] using hq)

theorem radialPosition_profile (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (E : Site) (t : ℤ)
    (hq : InQuadrant R q E) (ht : 0 ≤ t) :
    InQuadrant R q (radialPosition R hR q E t) ∧
      rho R (radialPosition R hR q E t) = rho R E + 2 * t ∧
      alpha R (radialPosition R hR q E t) = alpha R E ∧
      (X E - 1 ≤ X (radialPosition R hR q E t) ∧ X (radialPosition R hR q E t) ≤ X E + 1) := by
  have hp := radialPosition_positive_base R hR q E hq
  have ha := quadrantArm_rho_alpha R hR q (quadrantUnmap R hR q E) t hp ht
  have hb := quadrantArm_x_band R hR q (quadrantUnmap R hR q E) t
  have hzero := quadrantArm_x_band R hR q (quadrantUnmap R hR q E) 0
  change _ ≤ X (radialPosition R hR q E 0) ∧ X (radialPosition R hR q E 0) ≤ _ at hzero
  rw [radialPosition_zero] at hzero
  simp only [quadrantUnmap_rho, quadrantUnmap_alpha] at ha
  refine ⟨quadrantArm_quadrant R hR q _ t hp ht, ha.1, ha.2, ?_⟩
  change X E - 1 ≤ X (quadrantArm R hR q (quadrantUnmap R hR q E) t) ∧
    X (quadrantArm R hR q (quadrantUnmap R hR q E) t) ≤ X E + 1
  omega

def radialHeight (R u : ℤ) (E : Site) : ℕ := ((u - rho R E) / 2).toNat

theorem radialHeight_exact (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (E : Site)
    (hq : InQuadrant R q E) (u : ℤ) (hu : u % 2 = 1) (hup : rho R E ≤ u) :
    rho R E + 2 * (radialHeight R u E : ℤ) = u := by
  have hp := radialPosition_positive_base R hR q E hq
  have hodd := positive_rho_odd R hR (quadrantUnmap R hR q E) hp
  rw [quadrantUnmap_rho] at hodd
  unfold radialHeight
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ (u - rho R E) / 2)]
  omega

def radialTop (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (E : Site) (u : ℤ) : Site :=
  radialPosition R hR q E (radialHeight R u E)

theorem radialTop_level (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (E : Site)
    (hq : InQuadrant R q E) (u : ℤ) (hu : u % 2 = 1) (hup : rho R E ≤ u) :
    rho R (radialTop R hR q E u) = u := by
  have h := (radialPosition_profile R hR q E (radialHeight R u E) hq (by omega)).2.1
  have he := radialHeight_exact R hR q E hq u hu hup
  change rho R (radialPosition R hR q E (radialHeight R u E)) = u
  omega

def radialFold (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (E : Site) (u : ℤ) :
    Fold tetrahedralLattice (radialHeight R u E + 1) :=
  intervalFold (radialPosition R hR q E)
    (quadrantArm_injective R hR q (quadrantUnmap R hR q E))
    (quadrantArm_adj R hR q (quadrantUnmap R hR q E)) 0 (radialHeight R u E) true

theorem radialFold_first (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (E : Site) (u : ℤ)
    (i : Fin (radialHeight R u E + 1)) (hi : i.val = 0) :
    (radialFold R hR q E u).pos i = E := by
  change radialPosition R hR q E (0 + i.val) = E
  simp only [hi, Int.natCast_zero, add_zero, radialPosition_zero]

theorem radialFold_last (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (E : Site) (u : ℤ)
    (i : Fin (radialHeight R u E + 1)) (hi : i.val = radialHeight R u E) :
    (radialFold R hR q E u).pos i = radialTop R hR q E u := by
  change radialPosition R hR q E (0 + i.val) = _
  simp only [hi, zero_add, radialTop]

theorem radialFold_profile (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (E : Site)
    (hq : InQuadrant R q E) (u : ℤ) (hu : u % 2 = 1) (hup : rho R E ≤ u)
    (i : Fin (radialHeight R u E + 1)) :
    let p := (radialFold R hR q E u).pos i
    InQuadrant R q p ∧ (rho R E ≤ rho R p ∧ rho R p ≤ u) ∧
      alpha R p = alpha R E ∧ (X E - 1 ≤ X p ∧ X p ≤ X E + 1) := by
  have hi := i.isLt
  have hp := radialPosition_profile R hR q E i.val hq (by omega)
  have he := radialHeight_exact R hR q E hq u hu hup
  change InQuadrant R q (radialPosition R hR q E (0 + i.val)) ∧
    (rho R E ≤ rho R (radialPosition R hR q E (0 + i.val)) ∧ rho R (radialPosition R hR q E (0 + i.val)) ≤ u) ∧
    alpha R (radialPosition R hR q E (0 + i.val)) = alpha R E ∧
    (X E - 1 ≤ X (radialPosition R hR q E (0 + i.val)) ∧ X (radialPosition R hR q E (0 + i.val)) ≤ X E + 1)
  simp only [zero_add]
  exact ⟨hp.1, by omega, hp.2.2.1, hp.2.2.2⟩

end ProteinFolding.Tetrahedral.FarField

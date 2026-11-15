import ProteinFolding.Tetrahedral.FarFieldLevelCurves

namespace ProteinFolding.Tetrahedral.FarField

theorem level_index_mod (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0)
    (p : Site) (q r : ℤ) (hq : 0 ≤ q ∧ q < 4)
    (hY : p.val 1 = R + ringY u q r) (hZ : p.val 2 = 1 + ringZ u q r) :
    (x₀ - p.val 0 - r % 2) % 4 = q := by
  have hq' : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  have hr : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases p.property with hp | hp
  all_goals
    have hp0 := hp.1 0
    have hp1 := hp.1 1
    have hp2 := hp.1 2
    have hps := hp.2
    dsimp only [coordinateSum] at hps
    rcases hq' with hq' | hq' | hq' | hq' <;> rcases hr with hr | hr
    all_goals
      subst q
      simp [ringY, ringZ] at hY hZ
      omega

theorem levelPoint_of_ringCoordinates (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0)
    (p : Site) (q r : ℤ) (hq : 0 ≤ q ∧ q < 4)
    (hY : p.val 1 = R + ringY u q r) (hZ : p.val 2 = 1 + ringZ u q r) :
    levelPoint R u x₀ hR hu hx hs (x₀ - p.val 0 - r % 2) r = p := by
  have hj := level_index_mod R u x₀ hR hu hx hs p q r hq hY hZ
  have hqq : q % 4 = q := by omega
  have hy : ringY u (x₀ - p.val 0 - r % 2) r = ringY u q r := by simp [ringY, hj, hqq]
  have hz : ringZ u (x₀ - p.val 0 - r % 2) r = ringZ u q r := by simp [ringZ, hj, hqq]
  apply Subtype.ext
  funext k
  match k with
  | 0 => change x₀ - (x₀ - p.val 0 - r % 2) - r % 2 = p.val 0; omega
  | 1 => change R + ringY u (x₀ - p.val 0 - r % 2) r = p.val 1; rw [hy, hY]
  | 2 => change 1 + ringZ u (x₀ - p.val 0 - r % 2) r = p.val 2; rw [hz, hZ]

/-- Every actual site on rho=u occurs in the explicit level curve. The
quarter coordinate uses r<u, so bends belong to exactly one quarter. -/
theorem levelPoint_exhaustive (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (hupos : 0 < u)
    (p : Site) (hp : rho R p = u) :
    ∃ j r : ℤ, 0 ≤ r ∧ r < u ∧ levelPoint R u x₀ hR hu hx hs j r = p := by
  have hnon : ¬(Y R p = 0 ∧ Z p = 0) := by
    rintro ⟨hy, hz⟩
    simp [rho, hy, hz] at hp
    omega
  have hq : (0 ≤ Y R p ∧ 0 < Z p) ∨ (0 < Y R p ∧ Z p ≤ 0) ∨
      (Y R p ≤ 0 ∧ Z p < 0) ∨ (Y R p < 0 ∧ 0 ≤ Z p) := by omega
  rcases hq with hq | hq | hq | hq
  · have hρ : Y R p + Z p = u := by simpa only [rho, abs_of_nonneg hq.1, abs_of_pos hq.2] using hp
    refine ⟨x₀ - p.val 0 - (Y R p) % 2, Y R p, hq.1, by omega, ?_⟩
    apply levelPoint_of_ringCoordinates R u x₀ hR hu hx hs p 0 (Y R p) (by omega)
    · simp [ringY, Y]
    · simp [ringZ]
      dsimp [Y, Z] at hρ ⊢
      omega
  · have hρ : Y R p - Z p = u := by
      simpa only [rho, abs_of_pos hq.1, abs_of_nonpos hq.2, sub_eq_add_neg] using hp
    refine ⟨x₀ - p.val 0 - (-Z p) % 2, -Z p, by omega, by omega, ?_⟩
    apply levelPoint_of_ringCoordinates R u x₀ hR hu hx hs p 1 (-Z p) (by omega)
    · simp [ringY]
      dsimp [Y, Z] at hρ ⊢
      omega
    · simp [ringZ, Z]
  · have hρ : -Y R p - Z p = u := by
      simpa only [rho, abs_of_nonpos hq.1, abs_of_neg hq.2, sub_eq_add_neg] using hp
    refine ⟨x₀ - p.val 0 - (-Y R p) % 2, -Y R p, by omega, by omega, ?_⟩
    apply levelPoint_of_ringCoordinates R u x₀ hR hu hx hs p 2 (-Y R p) (by omega)
    · simp [ringY, Y]
    · simp [ringZ]
      dsimp [Y, Z] at hρ ⊢
      omega
  · have hρ : -Y R p + Z p = u := by
      simpa only [rho, abs_of_neg hq.1, abs_of_nonneg hq.2] using hp
    refine ⟨x₀ - p.val 0 - (Z p) % 2, Z p, hq.2, by omega, ?_⟩
    apply levelPoint_of_ringCoordinates R u x₀ hR hu hx hs p 3 (Z p) (by omega)
    · simp [ringY]
      dsimp [Y, Z] at hρ ⊢
      omega
    · simp [ringZ, Z]

end ProteinFolding.Tetrahedral.FarField


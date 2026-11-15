import ProteinFolding.Tetrahedral.FarFieldArmIdentity
import ProteinFolding.Tetrahedral.FarFieldWireOrdering
import ProteinFolding.Tetrahedral.FarFieldPathTools
import ProteinFolding.Tetrahedral.FarFieldWireAvenues

namespace ProteinFolding.Tetrahedral.FarField

def wireBaseXs {w : ℕ} (quadrants : Fin w → Quadrant) (bases : Fin w → Site) : Fin w → ℤ :=
  fun i => quadrantArmBaseX (quadrants i) (bases i)

def wireLevels {w : ℕ} (H : ℤ) (quadrants : Fin w → Quadrant) (bases : Fin w → Site) : Fin w → ℤ :=
  assignedLevel H (wireBaseXs quadrants bases)

def columnHeight {w : ℕ} (R H : ℤ) (quadrants : Fin w → Quadrant) (bases : Fin w → Site) (i : Fin w) : ℕ :=
  ((wireLevels H quadrants bases i - rho R (bases i)) / 2).toNat

def columnTop {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site) (i : Fin w) : Site :=
  quadrantArm R hR (quadrants i) (bases i) (columnHeight R H quadrants bases i)

theorem wireLevels_odd {w : ℕ} (H : ℤ) (hH : H % 2 = 1)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site) (i : Fin w) :
    wireLevels H quadrants bases i % 2 = 1 := by
  unfold wireLevels assignedLevel
  omega

theorem columnHeight_exact {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ) (hH : H % 2 = 1)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site) (i : Fin w)
    (hp : PositiveQuadrant R (bases i)) (hbelow : rho R (bases i) ≤ H) :
    rho R (bases i) + 2 * (columnHeight R H quadrants bases i : ℤ) = wireLevels H quadrants bases i := by
  have hodd := positive_rho_odd R hR (bases i) hp
  have hlevOdd := wireLevels_odd H hH quadrants bases i
  have hlev := (assignedLevel_bounds H (wireBaseXs quadrants bases) i).1
  change H ≤ wireLevels H quadrants bases i at hlev
  unfold columnHeight
  have hnon : 0 ≤ (wireLevels H quadrants bases i - rho R (bases i)) / 2 := by omega
  rw [Int.toNat_of_nonneg hnon]
  omega

theorem columnTop_profile {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ) (hH : H % 2 = 1)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site) (i : Fin w)
    (hp : PositiveQuadrant R (bases i)) (hbelow : rho R (bases i) ≤ H) :
    InQuadrant R (quadrants i) (columnTop R hR H quadrants bases i) ∧
      rho R (columnTop R hR H quadrants bases i) = wireLevels H quadrants bases i ∧
      alpha R (columnTop R hR H quadrants bases i) = alpha R (bases i) ∧
      (wireBaseXs quadrants bases i ≤ X (columnTop R hR H quadrants bases i) ∧
        X (columnTop R hR H quadrants bases i) ≤ wireBaseXs quadrants bases i + 1) := by
  have hh := columnHeight_exact R hR H hH quadrants bases i hp hbelow
  have ha := quadrantArm_rho_alpha R hR (quadrants i) (bases i)
    (columnHeight R H quadrants bases i) hp (by omega)
  refine ⟨quadrantArm_quadrant R hR _ _ _ hp (by omega), ?_, ha.2, quadrantArm_x_band R hR _ _ _⟩
  dsimp only [columnTop]
  omega

def columnFold {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site) (i : Fin w) :
    Fold tetrahedralLattice (columnHeight R H quadrants bases i + 1) :=
  intervalFold (quadrantArm R hR (quadrants i) (bases i))
    (quadrantArm_injective R hR _ _) (quadrantArm_adj R hR _ _)
    0 (columnHeight R H quadrants bases i) true

theorem columnFold_profile {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ) (hH : H % 2 = 1)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site) (i : Fin w)
    (hp : PositiveQuadrant R (bases i)) (hbelow : rho R (bases i) ≤ H)
    (k : Fin (columnHeight R H quadrants bases i + 1)) :
    let p := (columnFold R hR H quadrants bases i).pos k
    InQuadrant R (quadrants i) p ∧
      rho R p ≤ wireLevels H quadrants bases i ∧
      alpha R p = alpha R (bases i) ∧
      (wireBaseXs quadrants bases i ≤ X p ∧ X p ≤ wireBaseXs quadrants bases i + 1) := by
  have hk := k.isLt
  have hh := columnHeight_exact R hR H hH quadrants bases i hp hbelow
  have ha := quadrantArm_rho_alpha R hR (quadrants i) (bases i) k.val hp (by omega)
  change InQuadrant R (quadrants i) (quadrantArm R hR (quadrants i) (bases i) (0 + k.val)) ∧
    rho R (quadrantArm R hR (quadrants i) (bases i) (0 + k.val)) ≤ wireLevels H quadrants bases i ∧
    alpha R (quadrantArm R hR (quadrants i) (bases i) (0 + k.val)) = alpha R (bases i) ∧
    (wireBaseXs quadrants bases i ≤ X (quadrantArm R hR (quadrants i) (bases i) (0 + k.val)) ∧
      X (quadrantArm R hR (quadrants i) (bases i) (0 + k.val)) ≤ wireBaseXs quadrants bases i + 1)
  simp only [zero_add]
  refine ⟨quadrantArm_quadrant R hR _ _ _ hp (by omega), ?_, ha.2, quadrantArm_x_band R hR _ _ _⟩
  omega

theorem columnFolds_disjoint {w : ℕ} (R : ℤ) (hR : R % 2 = 0) (H : ℤ)
    (quadrants : Fin w → Quadrant) (bases : Fin w → Site)
    (hp : ∀ i, PositiveQuadrant R (bases i))
    (hids : Function.Injective (fun i => armIdentity R (quadrants i) (bases i)))
    (i j : Fin w) (hne : i ≠ j) :
    Disjoint (Set.range (columnFold R hR H quadrants bases i).pos)
      (Set.range (columnFold R hR H quadrants bases j).pos) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨a, rfl⟩ ⟨b, heq⟩
  have h : quadrantArm R hR (quadrants i) (bases i) a.val =
      quadrantArm R hR (quadrants j) (bases j) b.val := by
    simpa only [columnFold, intervalFold, ite_true, zero_add] using heq.symm
  have hid := arm_identity_of_intersect R hR (quadrants i) (quadrants j) (bases i) (bases j)
    (hp i) (hp j) a.val b.val (by omega) (by omega) h
  exact hne (hids hid)

end ProteinFolding.Tetrahedral.FarField

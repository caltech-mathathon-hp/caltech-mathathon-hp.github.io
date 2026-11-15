import ProteinFolding.Tetrahedral.FarFieldAvenues

/-! The manuscript's transformed coordinates and the private levels/strips
occupied by both explicit padding avenues. -/

namespace ProteinFolding.Tetrahedral.FarField

def X (p : Site) : ℤ := p.val 0
def Y (R : ℤ) (p : Site) : ℤ := p.val 1 - R
def Z (p : Site) : ℤ := p.val 2 - 1
def rho (R : ℤ) (p : Site) : ℤ := |Y R p| + |Z p|
def alpha (R : ℤ) (p : Site) : ℤ := |Y R p| - |Z p|
def PositiveQuadrant (R : ℤ) (p : Site) : Prop := 0 < Y R p ∧ 0 < Z p

theorem avenue_offsets (up : Bool) (n : ℤ) :
    -2 ≤ avenueY up n ∧ avenueY up n ≤ 1 ∧
      -1 ≤ avenueZ up n ∧ avenueZ up n ≤ 2 ∧
      (avenueY up n - avenueZ up n = 0 ∨ avenueY up n - avenueZ up n = -2) ∧
      (if up then
        avenueY up n + avenueZ up n = 0 ∨ avenueY up n + avenueZ up n = 2
       else avenueY up n + avenueZ up n = 0 ∨ avenueY up n + avenueZ up n = -2) := by
  have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr with hr | hr | hr | hr <;> cases up <;> simp [avenueY, avenueZ, hr]

theorem avenue_positive (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) : PositiveQuadrant R (avenue c hc up n) := by
  have h := avenue_offsets up n
  constructor
  · change 0 < c.val 1 + avenueY up n - R
    dsimp [Y] at hy
    omega
  · change 0 < c.val 2 + avenueZ up n - 1
    dsimp [Z] at hz
    omega

theorem secondAvenue_positive (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) : PositiveQuadrant R (secondAvenue c hc up n) := by
  have h := avenue_offsets up n
  constructor
  · change 0 < (c.val 1 + 2) + avenueY up n - R
    dsimp [Y] at hy
    omega
  · change 0 < (c.val 2 - 2) + avenueZ up n - 1
    dsimp [Z] at hz
    omega

theorem avenue_rho_alpha (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) :
    rho R (avenue c hc up n) = rho R c + avenueY up n + avenueZ up n ∧
      alpha R (avenue c hc up n) = alpha R c + avenueY up n - avenueZ up n := by
  have hpos := avenue_positive R c hc up n hy hz
  have hy0 : 0 ≤ Y R c := by omega
  have hz0 : 0 ≤ Z c := by omega
  simp only [rho, alpha, abs_of_nonneg hy0, abs_of_nonneg hz0,
    abs_of_pos hpos.1, abs_of_pos hpos.2]
  change (c.val 1 + avenueY up n - R) + (c.val 2 + avenueZ up n - 1) =
      (c.val 1 - R) + (c.val 2 - 1) + avenueY up n + avenueZ up n ∧
    (c.val 1 + avenueY up n - R) - (c.val 2 + avenueZ up n - 1) =
      (c.val 1 - R) - (c.val 2 - 1) + avenueY up n - avenueZ up n
  omega

theorem secondAvenue_rho_alpha (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) :
    rho R (secondAvenue c hc up n) = rho R (avenue c hc up n) ∧
      alpha R (secondAvenue c hc up n) = alpha R (avenue c hc up n) + 4 := by
  have hp := avenue_positive R c hc up n hy hz
  have hq := secondAvenue_positive R c hc up n hy hz
  simp only [rho, alpha, abs_of_pos hp.1, abs_of_pos hp.2,
    abs_of_pos hq.1, abs_of_pos hq.2]
  change ((c.val 1 + 2) + avenueY up n - R) + ((c.val 2 - 2) + avenueZ up n - 1) =
      (c.val 1 + avenueY up n - R) + (c.val 2 + avenueZ up n - 1) ∧
    ((c.val 1 + 2) + avenueY up n - R) - ((c.val 2 - 2) + avenueZ up n - 1) =
      (c.val 1 + avenueY up n - R) - (c.val 2 + avenueZ up n - 1) + 4
  omega

def privateLevel (R : ℤ) (c : Site) (up : Bool) : ℤ := rho R c - if up then 0 else 2
def privateStrip (R : ℤ) (c : Site) : ℤ := alpha R c - 2

theorem avenueSite_private (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool)
    (v : Bool × ℤ) (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) :
    PositiveQuadrant R (avenueSite c hc up v) ∧
    (rho R (avenueSite c hc up v) = privateLevel R c up ∨
      rho R (avenueSite c hc up v) = privateLevel R c up + 2) ∧
    (alpha R (avenueSite c hc up v) = privateStrip R c ∨
      alpha R (avenueSite c hc up v) = privateStrip R c + 2 ∨
      alpha R (avenueSite c hc up v) = privateStrip R c + 4 ∨
      alpha R (avenueSite c hc up v) = privateStrip R c + 6) := by
  obtain ⟨tag, n⟩ := v
  have ho := avenue_offsets up n
  have ha := avenue_rho_alpha R c hc up n hy hz
  have hb := secondAvenue_rho_alpha R c hc up n hy hz
  cases tag
  · simp only [avenueSite, Bool.false_eq_true, ↓reduceIte]
    refine ⟨avenue_positive R c hc up n hy hz, ?_, ?_⟩
    · cases up
      · have hsum : avenueY false n + avenueZ false n = 0 ∨ avenueY false n + avenueZ false n = -2 :=
          (avenue_offsets false n).2.2.2.2.2
        simp only [privateLevel, Bool.false_eq_true, ite_false]
        omega
      · have hsum : avenueY true n + avenueZ true n = 0 ∨ avenueY true n + avenueZ true n = 2 :=
          (avenue_offsets true n).2.2.2.2.2
        simp only [privateLevel, ↓reduceIte, sub_zero]
        omega
    · unfold privateStrip
      omega
  · simp only [avenueSite, ↓reduceIte]
    refine ⟨secondAvenue_positive R c hc up n hy hz, ?_, ?_⟩
    · cases up
      · have hsum : avenueY false n + avenueZ false n = 0 ∨ avenueY false n + avenueZ false n = -2 :=
          (avenue_offsets false n).2.2.2.2.2
        simp only [privateLevel, Bool.false_eq_true, ite_false]
        omega
      · have hsum : avenueY true n + avenueZ true n = 0 ∨ avenueY true n + avenueZ true n = 2 :=
          (avenue_offsets true n).2.2.2.2.2
        simp only [privateLevel, ↓reduceIte, sub_zero]
        omega
    · unfold privateStrip
      omega

end ProteinFolding.Tetrahedral.FarField

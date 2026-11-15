import ProteinFolding.Tetrahedral.FarFieldCoordinates

/-! The explicit positive-quadrant avenue is exactly the manuscript's
two-level/two-strip set. In particular there is one and only one lattice site
for every X coordinate; membership does not merely give a walk subset. -/

namespace ProteinFolding.Tetrahedral.FarField

set_option maxHeartbeats 1200000

theorem avenue_private (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) :
    PositiveQuadrant R (avenue c hc up n) ∧
      (rho R (avenue c hc up n) = privateLevel R c up ∨
        rho R (avenue c hc up n) = privateLevel R c up + 2) ∧
      (alpha R (avenue c hc up n) = privateStrip R c ∨
        alpha R (avenue c hc up n) = privateStrip R c + 2) := by
  have hpos := avenue_positive R c hc up n hy hz
  have ha := avenue_rho_alpha R c hc up n hy hz
  have ho := avenue_offsets up n
  refine ⟨hpos, ?_, ?_⟩
  · cases up
    · have hs : avenueY false n + avenueZ false n = 0 ∨ avenueY false n + avenueZ false n = -2 :=
        (avenue_offsets false n).2.2.2.2.2
      simp only [privateLevel, Bool.false_eq_true, ite_false]
      omega
    · have hs : avenueY true n + avenueZ true n = 0 ∨ avenueY true n + avenueZ true n = 2 :=
        (avenue_offsets true n).2.2.2.2.2
      simp only [privateLevel, ↓reduceIte, sub_zero]
      omega
  · unfold privateStrip
    omega

theorem avenue_exhaustive (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool) (p : Site)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) (hpq : PositiveQuadrant R p)
    (hrho : rho R p = privateLevel R c up ∨ rho R p = privateLevel R c up + 2)
    (halpha : alpha R p = privateStrip R c ∨ alpha R p = privateStrip R c + 2) :
    p = avenue c hc up (X p - X c) := by
  have hcy : 0 < Y R c := by omega
  have hcz : 0 < Z c := by omega
  simp only [rho, alpha, privateLevel, privateStrip, abs_of_pos hpq.1,
    abs_of_pos hpq.2, abs_of_pos hcy, abs_of_pos hcz] at hrho halpha
  dsimp only [Y, Z] at hrho halpha
  have hc0 := hc.1 0
  have hc1 := hc.1 1
  have hc2 := hc.1 2
  have hcs := hc.2
  dsimp only [coordinateSum] at hcs
  let n := X p - X c
  have hn : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have hcoords : p.val 1 = c.val 1 + avenueY up n ∧
      p.val 2 = c.val 2 + avenueZ up n := by
    rcases p.property with hp | hp
    all_goals
      have hp0 := hp.1 0
      have hp1 := hp.1 1
      have hp2 := hp.1 2
      have hps := hp.2
      dsimp only [coordinateSum] at hps
      rcases hrho with hrho | hrho <;> rcases halpha with halpha | halpha <;>
        rcases hn with hn | hn | hn | hn <;> cases up
      all_goals
        simp only [Bool.false_eq_true, ite_false, ite_true] at hrho halpha
        simp [avenueY, avenueZ, hn]
        dsimp only [n, X] at hn
        omega
  apply Subtype.ext
  funext k
  match k with
  | 0 => simp [avenue, avenueCoordinates, X]
  | 1 => exact hcoords.1
  | 2 => exact hcoords.2

theorem avenue_one_per_x (R : ℤ) (c : Site) (hc : InASublattice c.val) (up : Bool)
    (hy : 4 ≤ Y R c) (hz : 4 ≤ Z c) (x : ℤ) :
    ∃! p : Site, X p = x ∧ PositiveQuadrant R p ∧
      (rho R p = privateLevel R c up ∨ rho R p = privateLevel R c up + 2) ∧
      (alpha R p = privateStrip R c ∨ alpha R p = privateStrip R c + 2) := by
  refine ⟨avenue c hc up (x - X c), ?_, ?_⟩
  · have h := avenue_private R c hc up (x - X c) hy hz
    refine ⟨?_, h⟩
    change c.val 0 + (x - c.val 0) = x
    omega
  · intro p hp
    have he := avenue_exhaustive R c hc up p hy hz hp.2.1 hp.2.2.1 hp.2.2.2
    rw [hp.1] at he
    exact he

end ProteinFolding.Tetrahedral.FarField

import ProteinFolding.Tetrahedral.FarFieldLevelWalk
import Mathlib.Tactic.Linarith

namespace ProteinFolding.Tetrahedral.FarField

def nextPositiveQuarter (j : ℤ) : ℤ := j + (-j) % 4
def targetRadius (u a : ℤ) : ℤ := (u + a) / 2

theorem nextPositiveQuarter_spec (j : ℤ) :
    j ≤ nextPositiveQuarter j ∧ nextPositiveQuarter j ≤ j + 3 ∧ nextPositiveQuarter j % 4 = 0 := by
  unfold nextPositiveQuarter
  omega

theorem targetRadius_spec (u a : ℤ) (hu : u % 2 = 1) (ha : a % 2 = 1)
    (hroom : |a| + 8 < u) :
    5 ≤ targetRadius u a ∧ targetRadius u a + 5 ≤ u ∧ 2 * targetRadius u a = u + a := by
  have hplus : a ≤ |a| := le_abs_self _
  have hminus : -a ≤ |a| := neg_le_abs _
  unfold targetRadius
  omega

theorem levelPoint_positive_iff (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (j r : ℤ)
    (hr : 0 ≤ r) (hr' : r < u) :
    PositiveQuadrant R (levelPoint R u x₀ hR hu hx hs j r) ↔ j % 4 = 0 ∧ 0 < r := by
  have hj : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases hj with hj | hj | hj | hj <;>
    simp [PositiveQuadrant, Y, Z, levelPoint, levelCoordinates, ringY, ringZ, hj] <;> omega

theorem levelPoint_alpha_zero_quarter (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (j r : ℤ)
    (hj : j % 4 = 0) (hr : 0 ≤ r) (hr' : r ≤ u) :
    alpha R (levelPoint R u x₀ hR hu hx hs j r) = 2 * r - u := by
  have hy : Y R (levelPoint R u x₀ hR hu hx hs j r) = r := by
    simp [Y, levelPoint, levelCoordinates, ringY, hj]
  have hz : Z (levelPoint R u x₀ hR hu hx hs j r) = u - r := by
    simp [Z, levelPoint, levelCoordinates, ringZ, hj]
  rw [alpha, hy, hz, abs_of_nonneg hr, abs_of_nonneg (by omega : 0 ≤ u - r)]
  omega

theorem approach_time_bounds (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (humin : 3 ≤ u)
    (j r a : ℤ) (hr : 0 ≤ r) (hr' : r < u) (ha : a % 2 = 1) (hroom : |a| + 8 < u)
    (hα : |alpha R (levelPoint R u x₀ hR hu hx hs j r)| + 4 ≤ a) :
    j * u + r ≤ nextPositiveQuarter j * u + targetRadius u a ∧
      nextPositiveQuarter j * u + targetRadius u a - (j * u + r) ≤ 4 * u + 4 := by
  have hJ := nextPositiveQuarter_spec j
  have ht := targetRadius_spec u a hu ha hroom
  constructor
  · by_cases hsame : nextPositiveQuarter j = j
    · have hj : j % 4 = 0 := by omega
      have hapos := le_abs_self (alpha R (levelPoint R u x₀ hR hu hx hs j r))
      rw [levelPoint_alpha_zero_quarter R u x₀ hR hu hx hs j r hj hr (by omega)] at hapos hα
      rw [hsame]
      omega
    · have hj : j + 1 ≤ nextPositiveQuarter j := by omega
      have hmul := mul_le_mul_of_nonneg_right hj (show 0 ≤ u by omega)
      nlinarith
  · have hmul := mul_le_mul_of_nonneg_right hJ.2.1 (show 0 ≤ u by omega)
    nlinarith

end ProteinFolding.Tetrahedral.FarField

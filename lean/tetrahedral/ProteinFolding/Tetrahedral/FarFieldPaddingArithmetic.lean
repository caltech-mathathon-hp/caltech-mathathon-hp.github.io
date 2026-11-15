import ProteinFolding.Tetrahedral.FarFieldAvenues

/-! Exact parameter selection for Lemma F(D). These arithmetic facts are
used with the actual avenue paths, rather than standing in for geometry. -/

namespace ProteinFolding.Tetrahedral.FarField

def bit (b : Bool) : ℤ := if b then 1 else 0

def lowCrossing (δ : Bool) (d : ℕ) : ℤ := bit δ - 4 * d
def highCrossing (δ : Bool) : ℤ := bit δ + 4
def crossingSign (δ : Bool) : ℤ := 1 - 2 * bit δ

def paddingIncrease (r : ℤ) (δ η : Bool) (d : ℕ) : ℤ :=
  2 + 2 * (r - bit δ) + 4 * bit η + 8 * d

theorem padding_parameters (r Δ : ℤ) (hr : r = 2 ∨ r = 3)
    (hΔ : 6 ≤ Δ) (heven : Δ % 2 = 0) :
    ∃ (δ η : Bool) (d : ℕ), paddingIncrease r δ η d = Δ := by
  let t := (Δ - 2 * r) / 2
  have ht : 0 ≤ t := by dsimp [t]; omega
  have hdecomp : Δ = 2 * r + 2 * t := by dsimp [t]; omega
  refine ⟨decide (t % 4 % 2 = 0), decide (2 ≤ t % 4), (t / 4).toNat, ?_⟩
  have hd : ((t / 4).toNat : ℤ) = t / 4 := Int.toNat_of_nonneg (by omega)
  have hj : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases hj with hj | hj | hj | hj <;>
    simp [paddingIncrease, bit, hd, hj] <;> omega

theorem padding_interval_separation (r b : ℤ) (δ : Bool) (d : ℕ)
    (hr : r = 2 ∨ r = 3) (hb : r + 47 ≤ b) :
    lowCrossing δ d < r ∧ r < highCrossing δ ∧
      highCrossing δ ≤ 8 ∧ 9 ≤ b ∧
      highCrossing δ - crossingSign δ < 7 := by
  cases δ <;> simp [lowCrossing, highCrossing, crossingSign, bit] <;> omega

theorem crossing_residues (δ : Bool) (d : ℕ) :
    lowCrossing δ d % 4 = bit δ ∧ highCrossing δ % 4 = bit δ := by
  cases δ <;> simp [lowCrossing, highCrossing, bit] <;> omega

end ProteinFolding.Tetrahedral.FarField

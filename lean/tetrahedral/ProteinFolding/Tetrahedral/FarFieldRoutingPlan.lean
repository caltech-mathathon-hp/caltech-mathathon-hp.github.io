import ProteinFolding.Tetrahedral.FarFieldWires
import ProteinFolding.Tetrahedral.FarFieldApproachSeparation
import Mathlib.Data.Finset.Max

namespace ProteinFolding.Tetrahedral.FarField

structure RoutingPlan {w : ℕ} (d : WireData w) where
  a : ℤ
  a_odd : a % 2 = 1
  a_above : ∀ i, |alpha d.R (d.bases i)| + 6 ≤ a
  heights : Fin w → ℤ
  heights_odd : ∀ i, heights i % 2 = 1
  heights_above : ∀ i j, d.levels j + 4 ≤ heights i
  heights_room : ∀ i, |a| + 8 < heights i

namespace WireData

variable {w : ℕ} (d : WireData w)

theorem base_alpha_odd (i : Fin w) : alpha d.R (d.bases i) % 2 = 1 := by
  have hp := d.positive i
  have hR := d.R_even
  simp only [alpha, abs_of_pos hp.1, abs_of_pos hp.2]
  dsimp only [Y, Z]
  rcases (d.bases i).property with h | h
  all_goals
    have hy := h.1 1
    have hz := h.1 2
    omega

theorem base_abs_alpha_odd (i : Fin w) : |alpha d.R (d.bases i)| % 2 = 1 := by
  have h := d.base_alpha_odd i
  by_cases hp : 0 ≤ alpha d.R (d.bases i)
  · rwa [abs_of_nonneg hp]
  · rw [abs_of_neg (by omega : alpha d.R (d.bases i) < 0)]
    omega

def alphaValues : Finset ℤ := insert 1 (Finset.univ.image (fun i : Fin w => |alpha d.R (d.bases i)|))
def alphaMax : ℤ := d.alphaValues.max' (by simp [alphaValues])
def joiningAlpha : ℤ := d.alphaMax + 6

theorem alphaMax_mem : d.alphaMax ∈ d.alphaValues := Finset.max'_mem _ _

theorem alphaMax_ge_one : 1 ≤ d.alphaMax := by
  exact Finset.le_max' d.alphaValues 1 (by simp [alphaValues])

theorem alphaMax_odd : d.alphaMax % 2 = 1 := by
  have hm := d.alphaMax_mem
  simp only [alphaValues, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hm
  rcases hm with hm | ⟨i, hi⟩
  · rw [hm]; decide
  · rw [← hi]
    exact d.base_abs_alpha_odd i

theorem alpha_le_max (i : Fin w) : |alpha d.R (d.bases i)| ≤ d.alphaMax := by
  apply Finset.le_max'
  simp [alphaValues]

theorem alphaMax_high (i : Fin w) : d.alphaMax + 8 < d.H := by
  have hi := d.high i
  have hodd := d.base_abs_alpha_odd i
  have hnon := abs_nonneg (alpha d.R (d.bases i))
  have hm := d.alphaMax_mem
  simp only [alphaValues, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hm
  rcases hm with hm | ⟨j, hj⟩
  · rw [hm]
    omega
  · rw [← hj]
    exact d.high j

def pairedHeight {k : ℕ} (pairIndex : Fin w → Fin k) (i : Fin w) : ℤ :=
  d.H + 4 * w + 8 + 4 * (pairIndex i).val + 4

def defaultPlan {k : ℕ} (pairIndex : Fin w → Fin k) : RoutingPlan d where
  a := d.joiningAlpha
  a_odd := by have h := d.alphaMax_odd; unfold joiningAlpha; omega
  a_above i := by have h := d.alpha_le_max i; unfold joiningAlpha; omega
  heights := d.pairedHeight pairIndex
  heights_odd i := by have h := d.H_odd; unfold pairedHeight; omega
  heights_above i j := by
    have h := (assignedLevel_bounds d.H (wireBaseXs d.quadrants d.bases) j).2
    change d.levels j ≤ d.H + 4 * (w - 1 : ℕ) at h
    unfold pairedHeight
    omega
  heights_room i := by
    have hm := d.alphaMax_high i
    have hp := d.alphaMax_ge_one
    have hapos : 0 ≤ d.joiningAlpha := by unfold joiningAlpha; omega
    rw [abs_of_nonneg hapos]
    unfold joiningAlpha pairedHeight
    omega

theorem pairedHeight_bound {k : ℕ} (pairIndex : Fin w → Fin k) (hw : w = 2 * k) (i : Fin w) :
    d.pairedHeight pairIndex i ≤ d.H + 6 * w + 8 := by
  have hi := (pairIndex i).isLt
  unfold pairedHeight
  omega

end WireData

end ProteinFolding.Tetrahedral.FarField

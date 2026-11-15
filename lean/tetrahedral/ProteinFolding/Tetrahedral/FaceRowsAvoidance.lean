import ProteinFolding.Tetrahedral.FaceRowsMargins
import ProteinFolding.Tetrahedral.FaceRowsSegments

/-! The column-free row margins used by the explicit near-field tethers. -/

namespace ProteinFolding.Tetrahedral

theorem faceRowA_avoids_columns (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j)
    (hj : 1 ≤ j) (ha : 1 ≤ a) (haj : a < j) (r : ℕ) (hr : r ≤ 2 * c) :
    ¬ OnDanglingColumn m (faceRowPoint 0 m j a b c hs r) := by
  by_cases hmod : r % 2 = 0
  · have heq : r = 2 * (r / 2) := by omega
    rw [heq, faceRowA_even m j a b c hs (r / 2) (by omega)]
    exact faceSurface_not_on_column_of_a_lt hj _ haj
  · have heq : r = 2 * (r / 2) + 1 := by omega
    rw [heq, faceRowA_odd m j a b c hs (r / 2) (by omega)]
    exact faceSub_not_on_column_of_a_lt hj _ ha (by omega) (by omega) haj

theorem faceRowB_avoids_columns (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j)
    (hj : 1 ≤ j) (hb : 1 ≤ b) (hbj : b < j) (r : ℕ) (hr : r ≤ 2 * a) :
    ¬ OnDanglingColumn m (faceRowPoint 1 m j a b c hs r) := by
  by_cases hmod : r % 2 = 0
  · have heq : r = 2 * (r / 2) := by omega
    rw [heq, faceRowB_even m j a b c hs (r / 2) (by omega)]
    exact faceSurface_not_on_column_of_b_lt hj _ hbj
  · have heq : r = 2 * (r / 2) + 1 := by omega
    rw [heq, faceRowB_odd m j a b c hs (r / 2) (by omega)]
    exact faceSub_not_on_column_of_b_lt hj _ (by omega) hb (by omega) hbj

/-- The c=1 row meets only the columns owned by c=0 edge sites or c=1
second-row sites of the original face. -/
theorem faceRowC_one_column_owners {m j a b n r : ℕ} (C : DanglingColumn m)
    (hs : a + b + 1 + 2 = m + 2 * j) (hj : 1 ≤ j) (hr : r ≤ 2 * b)
    (heq : C.point n = faceRowPoint 2 m j a b 1 hs r) :
    ∃ a₀ b₀ c₀ : ℕ, ∃ hs₀ : a₀ + b₀ + c₀ + 2 = m,
      C = faceDanglingColumn m a₀ b₀ c₀ hs₀ ∧ (c₀ = 0 ∨ c₀ = 1) := by
  by_cases hmod : r % 2 = 0
  · have hi : r = 2 * (r / 2) := by omega
    rw [hi, faceRowC_even m j a b 1 hs (r / 2) (by omega)] at heq
    obtain ⟨a₀, b₀, c₀, hs₀, hC, _, _, _, hc⟩ := faceSurface_column_coordinates C hj _ heq
    exact ⟨a₀, b₀, c₀, hs₀, hC, Or.inr hc.symm⟩
  · have hi : r = 2 * (r / 2) + 1 := by omega
    rw [hi, faceRowC_odd m j a b 1 hs (r / 2) (by omega)] at heq
    obtain ⟨a₀, b₀, c₀, hs₀, hC, _, _, _, hc⟩ :=
      faceSub_column_coordinates C hj _ (by omega) (by omega) (by decide) heq
    exact ⟨a₀, b₀, c₀, hs₀, hC, Or.inl (by omega)⟩

end ProteinFolding.Tetrahedral

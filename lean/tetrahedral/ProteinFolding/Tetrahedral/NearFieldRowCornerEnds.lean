import ProteinFolding.Tetrahedral.NearFieldRowCorners

/-! The endpoints and exact lengths of the two-row tether corners. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem rowCBFold_first (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ b)
    (i : Fin ((2 * l₁ + 1) + (2 * l₂ + 1) - 1)) (hi : i.val = 0) :
    (rowCBFold m j a b c l₁ l₂ hs h₁).pos i = faceSurfaceSite m j a b c hs := by
  unfold rowCBFold
  rw [FarField.glue_first _ _ _ _ _ _ i hi]
  exact faceRowPoint_zero 2 m j a b c hs

theorem rowCBFold_last (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ b) (h₂ : l₂ ≤ a + l₁)
    (i : Fin ((2 * l₁ + 1) + (2 * l₂ + 1) - 1))
    (hi : i.val + 1 = (2 * l₁ + 1) + (2 * l₂ + 1) - 1) :
    (rowCBFold m j a b c l₁ l₂ hs h₁).pos i =
      faceSurfaceSite m j (a + l₁ - l₂) (b - l₁) (c + l₂) (by omega) := by
  unfold rowCBFold
  rw [FarField.glue_last _ _ _ _ _ _ i hi]
  change faceRowPoint 1 m j (a + l₁) (b - l₁) c (by omega) (2 * l₂ + 1 - 1) = _
  rw [show 2 * l₂ + 1 - 1 = 2 * l₂ by omega]
  exact faceRowB_even m j (a + l₁) (b - l₁) c (by omega) l₂ h₂

theorem rowBAFold_first (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ a)
    (i : Fin ((2 * l₁ + 1) + (2 * l₂ + 1) - 1)) (hi : i.val = 0) :
    (rowBAFold m j a b c l₁ l₂ hs h₁).pos i = faceSurfaceSite m j a b c hs := by
  unfold rowBAFold
  rw [FarField.glue_first _ _ _ _ _ _ i hi]
  exact faceRowPoint_zero 1 m j a b c hs

theorem rowBAFold_last (m j a b c l₁ l₂ : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (h₁ : l₁ ≤ a) (h₂ : l₂ ≤ c + l₁)
    (i : Fin ((2 * l₁ + 1) + (2 * l₂ + 1) - 1))
    (hi : i.val + 1 = (2 * l₁ + 1) + (2 * l₂ + 1) - 1) :
    (rowBAFold m j a b c l₁ l₂ hs h₁).pos i =
      faceSurfaceSite m j (a - l₁) (b + l₂) (c + l₁ - l₂) (by omega) := by
  unfold rowBAFold
  rw [FarField.glue_last _ _ _ _ _ _ i hi]
  change faceRowPoint 0 m j (a - l₁) b (c + l₁) (by omega) (2 * l₂ + 1 - 1) = _
  rw [show 2 * l₂ + 1 - 1 = 2 * l₂ by omega]
  exact faceRowA_even m j (a - l₁) b (c + l₁) (by omega) l₂ h₂

theorem rowCorner_length (l₁ l₂ : ℕ) :
    (2 * l₁ + 1) + (2 * l₂ + 1) - 1 = 2 * (l₁ + l₂) + 1 := by omega

end ProteinFolding.Tetrahedral.NearField

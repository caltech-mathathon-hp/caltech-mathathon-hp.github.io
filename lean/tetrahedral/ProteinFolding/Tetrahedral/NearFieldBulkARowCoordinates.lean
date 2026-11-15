import ProteinFolding.Tetrahedral.OctahedralTrackGeometry

/-! The A second row on big face 2, used by the borrowed frame linker caps. -/

namespace ProteinFolding.Tetrahedral.NearField

def aSecondRowCoordinates (m t : ℕ) (k : Fin 3) : ℤ :=
  if k = 0 then -2 else if k = 1 then octRadius m + 2 * t else -octRadius m + 2 * t + 2

theorem aSecondRowCoordinates_inA (m t : ℕ) : InASublattice (aSecondRowCoordinates m t) := by
  constructor
  · intro k; fin_cases k <;> dsimp [aSecondRowCoordinates, octRadius] <;> omega
  · dsimp [coordinateSum, aSecondRowCoordinates, octRadius]
    omega

def aSecondRowSite (m t : ℕ) : Site :=
  ⟨aSecondRowCoordinates m t, Or.inl (aSecondRowCoordinates_inA m t)⟩

end ProteinFolding.Tetrahedral.NearField

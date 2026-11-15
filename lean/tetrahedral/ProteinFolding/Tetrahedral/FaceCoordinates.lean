import ProteinFolding.Tetrahedral.OctahedralBoundary

/-! Exact triangular coordinates for the F' bilayers in Section 8.2.
The face centre stays at c_m while its size is m+2j. -/

namespace ProteinFolding.Tetrahedral

def faceSurfaceCoordinates (m a b c : ℕ) : Coordinates := fun k =>
  if k = 0 then 2 * (c : ℤ) + 1
  else if k = 1 then octRadius m + 2 * (b : ℤ) + 1
  else -2 * (a : ℤ) - 1

def faceSubCoordinates (m a b c : ℕ) : Coordinates := fun k =>
  if k = 0 then 2 * (c : ℤ)
  else if k = 1 then octRadius m + 2 * (b : ℤ)
  else -2 * (a : ℤ)

theorem faceSurfaceCoordinates_inB (m j a b c : ℕ)
    (hsum : a + b + c + 2 = m + 2 * j) :
    InBSublattice (faceSurfaceCoordinates m a b c) := by
  constructor
  · intro k
    fin_cases k <;> dsimp [faceSurfaceCoordinates, octRadius] <;> omega
  · dsimp [coordinateSum, faceSurfaceCoordinates, octRadius]
    omega

theorem faceSubCoordinates_inA (m j a b c : ℕ)
    (hsum : a + b + c + 1 = m + 2 * j) :
    InASublattice (faceSubCoordinates m a b c) := by
  constructor
  · intro k
    fin_cases k <;> dsimp [faceSubCoordinates, octRadius] <;> omega
  · dsimp [coordinateSum, faceSubCoordinates, octRadius]
    omega

def faceSurfaceSite (m j a b c : ℕ) (hsum : a + b + c + 2 = m + 2 * j) : Site :=
  ⟨faceSurfaceCoordinates m a b c, Or.inr (faceSurfaceCoordinates_inB m j a b c hsum)⟩

def faceSubSite (m j a b c : ℕ) (hsum : a + b + c + 1 = m + 2 * j) : Site :=
  ⟨faceSubCoordinates m a b c, Or.inl (faceSubCoordinates_inA m j a b c hsum)⟩

theorem tetraCoordinate_faceSurface (m j a b c : ℕ)
    (hsum : a + b + c + 2 = m + 2 * j) (i : Fin 4) :
    tetraCoordinate m (faceSurfaceSite m j a b c hsum).val i =
      if i = 0 then 2 * ((m + 2 * j : ℕ) : ℤ) - 3 - 4 * a
      else if i = 1 then 2 * ((m + 2 * j : ℕ) : ℤ) - 3 - 4 * b
      else if i = 2 then 2 * ((m + 2 * j : ℕ) : ℤ) - 3 - 4 * c
      else -(2 * ((m + 2 * j : ℕ) : ℤ) - 1) := by
  fin_cases i <;> dsimp [tetraCoordinate, faceSurfaceSite, faceSurfaceCoordinates] <;>
    push_cast <;> omega

theorem tetraCoordinate_faceSub (m j a b c : ℕ)
    (hsum : a + b + c + 1 = m + 2 * j) (i : Fin 4) :
    tetraCoordinate m (faceSubSite m j a b c hsum).val i =
      if i = 0 then 2 * ((m + 2 * j : ℕ) : ℤ) - 2 - 4 * a
      else if i = 1 then 2 * ((m + 2 * j : ℕ) : ℤ) - 2 - 4 * b
      else if i = 2 then 2 * ((m + 2 * j : ℕ) : ℤ) - 2 - 4 * c
      else -(2 * ((m + 2 * j : ℕ) : ℤ) - 2) := by
  fin_cases i <;> dsimp [tetraCoordinate, faceSubSite, faceSubCoordinates] <;>
    push_cast <;> omega

theorem faceSurfaceSite_injective (m j : ℕ) {a b c a' b' c' : ℕ}
    (hsum : a + b + c + 2 = m + 2 * j) (hsum' : a' + b' + c' + 2 = m + 2 * j)
    (heq : faceSurfaceSite m j a b c hsum = faceSurfaceSite m j a' b' c' hsum') :
    a = a' ∧ b = b' ∧ c = c' := by
  have hx := congrArg (fun p : Site => p.val 0) heq
  have hy := congrArg (fun p : Site => p.val 1) heq
  have hz := congrArg (fun p : Site => p.val 2) heq
  dsimp [faceSurfaceSite, faceSurfaceCoordinates] at hx hy hz
  omega

theorem faceSubSite_injective (m j : ℕ) {a b c a' b' c' : ℕ}
    (hsum : a + b + c + 1 = m + 2 * j) (hsum' : a' + b' + c' + 1 = m + 2 * j)
    (heq : faceSubSite m j a b c hsum = faceSubSite m j a' b' c' hsum') :
    a = a' ∧ b = b' ∧ c = c' := by
  have hx := congrArg (fun p : Site => p.val 0) heq
  have hy := congrArg (fun p : Site => p.val 1) heq
  have hz := congrArg (fun p : Site => p.val 2) heq
  dsimp [faceSubSite, faceSubCoordinates] at hx hy hz
  omega

end ProteinFolding.Tetrahedral

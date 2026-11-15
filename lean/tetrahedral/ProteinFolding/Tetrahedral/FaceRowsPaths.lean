import ProteinFolding.Tetrahedral.FaceRowsGeometry

/-!
# Explicit F' row paths

The kind is 0 for a constant-a row, 1 for constant b, and 2 for constant c.
Each path is indexed by bonds; index 2u is a surface site and 2u+1 a
sub-surface site. The functions continue on the full lattice, while the
triangle bounds below select the required finite segments.
-/

namespace ProteinFolding.Tetrahedral

def faceRowCoordinates (kind : Fin 3) (m a b c r : ℕ) (k : Fin 3) : ℤ :=
  if kind = 0 then
    if k = 0 then 2 * (c : ℤ) + 1 - r
    else if k = 1 then octRadius m + 2 * (b : ℤ) + 1 + r
    else -2 * (a : ℤ) - 1 + (r % 2 : ℕ)
  else if kind = 1 then
    if k = 0 then 2 * (c : ℤ) + 1 + r
    else if k = 1 then octRadius m + 2 * (b : ℤ) + 1 - (r % 2 : ℕ)
    else -2 * (a : ℤ) - 1 + r
  else
    if k = 0 then 2 * (c : ℤ) + 1 - (r % 2 : ℕ)
    else if k = 1 then octRadius m + 2 * (b : ℤ) + 1 - r
    else -2 * (a : ℤ) - 1 - r

theorem faceRowCoordinates_inB (kind : Fin 3) (m j a b c r : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (hr : r % 2 = 0) :
    InBSublattice (faceRowCoordinates kind m a b c r) := by
  constructor
  · intro k
    fin_cases kind <;> fin_cases k <;>
      dsimp [faceRowCoordinates, octRadius] <;> omega
  · fin_cases kind <;> dsimp [coordinateSum, faceRowCoordinates, octRadius] <;> omega

theorem faceRowCoordinates_inA (kind : Fin 3) (m j a b c r : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (hr : r % 2 = 1) :
    InASublattice (faceRowCoordinates kind m a b c r) := by
  constructor
  · intro k
    fin_cases kind <;> fin_cases k <;>
      dsimp [faceRowCoordinates, octRadius] <;> omega
  · fin_cases kind <;> dsimp [coordinateSum, faceRowCoordinates, octRadius] <;> omega

def faceRowPoint (kind : Fin 3) (m j a b c : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (r : ℕ) : Site :=
  ⟨faceRowCoordinates kind m a b c r, by
    by_cases hr : r % 2 = 0
    · exact Or.inr (faceRowCoordinates_inB kind m j a b c r hs hr)
    · exact Or.inl (faceRowCoordinates_inA kind m j a b c r hs (by omega))⟩

def faceRowDirection (kind : Fin 3) (r : ℕ) : Fin 4 :=
  if r % 2 = 0 then (if kind = 0 then 1 else if kind = 1 then 2 else 0)
  else (if kind = 0 then 2 else if kind = 1 then 0 else 1)

theorem faceRowPoint_step (kind : Fin 3) (m j a b c : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (r : ℕ) :
    faceRowPoint kind m j a b c hs (r + 1) =
      step (faceRowPoint kind m j a b c hs r) (faceRowDirection kind r) := by
  by_cases hr : r % 2 = 0
  · have hpB := faceRowCoordinates_inB kind m j a b c r hs hr
    apply Subtype.ext
    rw [step_val_of_B _ hpB]
    funext k
    simp_rw [bondVector_eq_bondComponent]
    fin_cases kind <;> fin_cases k <;>
      dsimp [faceRowPoint, faceRowCoordinates, faceRowDirection, bondComponent] <;>
      simp only [hr, ite_true] <;> omega
  · have hr1 : r % 2 = 1 := by omega
    have hpA := faceRowCoordinates_inA kind m j a b c r hs hr1
    apply Subtype.ext
    rw [step_val_of_A _ hpA]
    funext k
    simp_rw [bondVector_eq_bondComponent]
    fin_cases kind <;> fin_cases k <;>
      dsimp [faceRowPoint, faceRowCoordinates, faceRowDirection, bondComponent] <;>
      simp [hr1] <;> omega

theorem faceRowPoint_adj (kind : Fin 3) (m j a b c : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) (r : ℕ) :
    tetrahedralLattice.Adj (faceRowPoint kind m j a b c hs r)
      (faceRowPoint kind m j a b c hs (r + 1)) := by
  rw [faceRowPoint_step]
  exact step_adj _ _

theorem faceRowPoint_injective (kind : Fin 3) (m j a b c : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) : Function.Injective (faceRowPoint kind m j a b c hs) := by
  intro r s heq
  fin_cases kind
  · have h := congrArg (fun p : Site => p.val 1) heq
    dsimp [faceRowPoint, faceRowCoordinates] at h
    omega
  · have h := congrArg (fun p : Site => p.val 0) heq
    dsimp [faceRowPoint, faceRowCoordinates] at h
    omega
  · have h := congrArg (fun p : Site => p.val 1) heq
    dsimp [faceRowPoint, faceRowCoordinates] at h
    omega

theorem faceRowPoint_zero (kind : Fin 3) (m j a b c : ℕ)
    (hs : a + b + c + 2 = m + 2 * j) :
    faceRowPoint kind m j a b c hs 0 = faceSurfaceSite m j a b c hs := by
  apply Subtype.ext
  funext k
  fin_cases kind <;> fin_cases k <;>
    dsimp [faceRowPoint, faceRowCoordinates, faceSurfaceSite, faceSurfaceCoordinates] <;> omega

theorem faceRowA_even (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j)
    (u : ℕ) (hu : u ≤ c) : faceRowPoint 0 m j a b c hs (2 * u) =
      faceSurfaceSite m j a (b + u) (c - u) (by omega) := by
  apply Subtype.ext
  funext k
  fin_cases k <;> dsimp [faceRowPoint, faceRowCoordinates, faceSurfaceSite,
    faceSurfaceCoordinates] <;> omega

theorem faceRowA_odd (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j)
    (u : ℕ) (hu : u < c) : faceRowPoint 0 m j a b c hs (2 * u + 1) =
      faceSubSite m j a (b + u + 1) (c - u) (by omega) := by
  apply Subtype.ext
  funext k
  fin_cases k <;> dsimp [faceRowPoint, faceRowCoordinates, faceSubSite,
    faceSubCoordinates] <;> omega

theorem faceRowB_even (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j)
    (u : ℕ) (hu : u ≤ a) : faceRowPoint 1 m j a b c hs (2 * u) =
      faceSurfaceSite m j (a - u) b (c + u) (by omega) := by
  apply Subtype.ext
  funext k
  fin_cases k <;> dsimp [faceRowPoint, faceRowCoordinates, faceSurfaceSite,
    faceSurfaceCoordinates] <;> omega

theorem faceRowB_odd (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j)
    (u : ℕ) (hu : u < a) : faceRowPoint 1 m j a b c hs (2 * u + 1) =
      faceSubSite m j (a - u) b (c + u + 1) (by omega) := by
  apply Subtype.ext
  funext k
  fin_cases k <;> dsimp [faceRowPoint, faceRowCoordinates, faceSubSite,
    faceSubCoordinates] <;> omega

theorem faceRowC_even (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j)
    (u : ℕ) (hu : u ≤ b) : faceRowPoint 2 m j a b c hs (2 * u) =
      faceSurfaceSite m j (a + u) (b - u) c (by omega) := by
  apply Subtype.ext
  funext k
  fin_cases k <;> dsimp [faceRowPoint, faceRowCoordinates, faceSurfaceSite,
    faceSurfaceCoordinates] <;> omega

theorem faceRowC_odd (m j a b c : ℕ) (hs : a + b + c + 2 = m + 2 * j)
    (u : ℕ) (hu : u < b) : faceRowPoint 2 m j a b c hs (2 * u + 1) =
      faceSubSite m j (a + u + 1) (b - u) c (by omega) := by
  apply Subtype.ext
  funext k
  fin_cases k <;> dsimp [faceRowPoint, faceRowCoordinates, faceSubSite,
    faceSubCoordinates] <;> omega

end ProteinFolding.Tetrahedral

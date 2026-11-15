import ProteinFolding.Tetrahedral.FarFieldQuadrants

/-! Explicit level-curve coordinates. A quarter index j records successive
bends and r runs from zero to u-1 inside that quarter. The X pair drops by one
at every bend, as in Lemma V. -/

namespace ProteinFolding.Tetrahedral.FarField

def ringY (u j r : ℤ) : ℤ :=
  if j % 4 = 0 then r else if j % 4 = 1 then u - r
  else if j % 4 = 2 then -r else -(u - r)

def ringZ (u j r : ℤ) : ℤ :=
  if j % 4 = 0 then u - r else if j % 4 = 1 then -r
  else if j % 4 = 2 then -(u - r) else r

def levelCoordinates (R u x₀ j r : ℤ) : Coordinates :=
  ![x₀ - j - r % 2, R + ringY u j r, 1 + ringZ u j r]

theorem levelCoordinates_site (R u x₀ j r : ℤ)
    (hR : R % 2 = 0) (hu : u % 2 = 1) (hx : x₀ % 2 = 0)
    (hs : (x₀ + R + u + 1) % 4 = 0) : IsLatticeSite (levelCoordinates R u x₀ j r) := by
  have hj : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  have hr : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hj with hj | hj | hj | hj <;> rcases hr with hr | hr
  all_goals
    first
    | left; constructor
      · intro k; fin_cases k <;> simp [levelCoordinates, ringY, ringZ, hj, hr] <;> omega
      · simp [coordinateSum, levelCoordinates, ringY, ringZ, hj, hr]; omega
    | right; constructor
      · intro k; fin_cases k <;> simp [levelCoordinates, ringY, ringZ, hj, hr] <;> omega
      · simp [coordinateSum, levelCoordinates, ringY, ringZ, hj, hr]; omega

def levelPoint (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (j r : ℤ) : Site :=
  ⟨levelCoordinates R u x₀ j r, levelCoordinates_site R u x₀ j r hR hu hx hs⟩

@[simp] theorem levelPoint_x (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (j r : ℤ) :
    X (levelPoint R u x₀ hR hu hx hs j r) = x₀ - j - r % 2 := rfl

theorem levelPoint_rho (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (j r : ℤ)
    (hr : 0 ≤ r) (hr' : r ≤ u) : rho R (levelPoint R u x₀ hR hu hx hs j r) = u := by
  have hj : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  have hur : 0 ≤ u - r := by omega
  have hru : r - u ≤ 0 := by omega
  have hy : Y R (levelPoint R u x₀ hR hu hx hs j r) = ringY u j r := by
    change R + ringY u j r - R = _
    omega
  have hz : Z (levelPoint R u x₀ hR hu hx hs j r) = ringZ u j r := by
    change 1 + ringZ u j r - 1 = _
    omega
  rw [rho, hy, hz]
  rcases hj with hj | hj | hj | hj <;>
    simp [ringY, ringZ, hj, abs_of_nonneg hr, abs_of_nonneg hur, abs_of_nonpos hru] <;> omega

theorem unit_coordinate_adj (p q : Site)
    (h : ∀ k, q.val k - p.val k = 1 ∨ q.val k - p.val k = -1) : tetrahedralLattice.Adj p q := by
  apply (CertificatesTM2Geometry.adj_iff_manhattan_three p q).2
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [CertificatesTM2Geometry.manhattan, h0, h1, h2]

theorem levelPoint_adj_inside (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (j r : ℤ) :
    tetrahedralLattice.Adj (levelPoint R u x₀ hR hu hx hs j r)
      (levelPoint R u x₀ hR hu hx hs j (r + 1)) := by
  apply unit_coordinate_adj
  intro k
  have hj : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  have hr : r % 2 = 0 ∨ r % 2 = 1 := by omega
  have hnext : (r + 1) % 2 = 1 - r % 2 := by omega
  fin_cases k
  · rcases hr with hr | hr <;>
      simp [levelPoint, levelCoordinates, hnext, hr] <;> omega
  · rcases hj with hj | hj | hj | hj <;>
      simp [levelPoint, levelCoordinates, ringY, hj] <;> omega
  · rcases hj with hj | hj | hj | hj <;>
      simp [levelPoint, levelCoordinates, ringZ, hj] <;> omega

theorem levelPoint_adj_bend (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (j : ℤ) :
    tetrahedralLattice.Adj (levelPoint R u x₀ hR hu hx hs j (u - 1))
      (levelPoint R u x₀ hR hu hx hs (j + 1) 0) := by
  apply unit_coordinate_adj
  intro k
  have hj : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  have hlast : (u - 1) % 2 = 0 := by omega
  fin_cases k
  · simp [levelPoint, levelCoordinates, hlast]
  · rcases hj with hj | hj | hj | hj
    all_goals
      have hnext : (j + 1) % 4 = (j % 4 + 1) % 4 := by omega
      simp only [hj] at hnext
      norm_num at hnext
      simp [levelPoint, levelCoordinates, ringY, hj, hnext] <;> omega
  · rcases hj with hj | hj | hj | hj
    all_goals
      have hnext : (j + 1) % 4 = (j % 4 + 1) % 4 := by omega
      simp only [hj] at hnext
      norm_num at hnext
      simp [levelPoint, levelCoordinates, ringZ, hj, hnext] <;> omega

theorem levelPoint_x_window (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (j₀ j r : ℤ)
    (hj : j₀ ≤ j) (hj' : j ≤ j₀ + 3) :
    x₀ - j₀ - 4 ≤ X (levelPoint R u x₀ hR hu hx hs j r) ∧
      X (levelPoint R u x₀ hR hu hx hs j r) ≤ x₀ - j₀ := by
  rw [levelPoint_x]
  omega

theorem levelPoint_injective (R u x₀ : ℤ) (hR : R % 2 = 0) (hu : u % 2 = 1)
    (hx : x₀ % 2 = 0) (hs : (x₀ + R + u + 1) % 4 = 0) (hupos : 0 < u)
    (j k r s : ℤ) (hr : 0 ≤ r) (hr' : r < u) (hs0 : 0 ≤ s) (hs' : s < u)
    (h : levelPoint R u x₀ hR hu hx hs j r = levelPoint R u x₀ hR hu hx hs k s) :
    j = k ∧ r = s := by
  have hX := congrArg (fun p : Site => p.val 0) h
  have hY := congrArg (fun p : Site => p.val 1) h
  have hZ := congrArg (fun p : Site => p.val 2) h
  change x₀ - j - r % 2 = x₀ - k - s % 2 at hX
  change R + ringY u j r = R + ringY u k s at hY
  change 1 + ringZ u j r = 1 + ringZ u k s at hZ
  have hj : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  have hk : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hj with hj | hj | hj | hj <;> rcases hk with hk | hk | hk | hk
  all_goals
    simp only [ringY, ringZ] at hY hZ
    simp [hj, hk] at hY hZ
    omega

end ProteinFolding.Tetrahedral.FarField

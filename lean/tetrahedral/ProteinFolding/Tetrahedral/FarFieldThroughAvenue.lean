import ProteinFolding.Tetrahedral.FarFieldRungs

/-! Canonical instantiation of an avenue through any given positive-quadrant
site. The two sublattice cases determine the crossing anchor and rung phase. -/

namespace ProteinFolding.Tetrahedral.FarField

def throughAnchorCoordinates (p : Site) : Coordinates :=
  if InASublattice p.val then ![p.val 0 - 2, p.val 1 + 2, p.val 2]
  else ![p.val 0 - 3, p.val 1 + 1, p.val 2 - 1]

theorem throughAnchorCoordinates_A (p : Site) : InASublattice (throughAnchorCoordinates p) := by
  rcases p.property with hp | hp
  · have h0 := hp.1 0
    have h1 := hp.1 1
    have h2 := hp.1 2
    have hs := hp.2
    dsimp only [coordinateSum] at hs
    constructor
    · intro k; fin_cases k <;> simp [throughAnchorCoordinates, hp] <;> omega
    · simp [throughAnchorCoordinates, coordinateSum, hp]; omega
  · have hA := (inB_iff_not_inA p).1 hp
    have h0 := hp.1 0
    have h1 := hp.1 1
    have h2 := hp.1 2
    have hs := hp.2
    dsimp only [coordinateSum] at hs
    constructor
    · intro k; fin_cases k <;> simp [throughAnchorCoordinates, hA] <;> omega
    · simp [throughAnchorCoordinates, coordinateSum, hA]; omega

def throughAnchor (p : Site) : Site :=
  ⟨throughAnchorCoordinates p, Or.inl (throughAnchorCoordinates_A p)⟩

theorem throughAnchor_A (p : Site) : InASublattice (throughAnchor p).val := throughAnchorCoordinates_A p

def throughUp (p : Site) : Bool := decide (¬InASublattice p.val)
def throughOffset (p : Site) : ℤ := if InASublattice p.val then 2 else 3

theorem avenue_through_site (p : Site) :
    avenue (throughAnchor p) (throughAnchor_A p) (throughUp p) (throughOffset p) = p := by
  apply Subtype.ext
  funext k
  by_cases hp : InASublattice p.val <;> fin_cases k <;>
    simp [avenue, avenueCoordinates, avenueY, avenueZ, throughAnchor, throughAnchorCoordinates,
      throughUp, throughOffset, hp] <;> omega

theorem throughAnchor_margins (R : ℤ) (p : Site) (hy : 4 ≤ Y R p) (hz : 5 ≤ Z p) :
    4 ≤ Y R (throughAnchor p) ∧ 4 ≤ Z (throughAnchor p) := by
  by_cases hp : InASublattice p.val <;>
    simp [Y, Z, throughAnchor, throughAnchorCoordinates, hp] <;> dsimp [Y, Z] at hy hz <;> omega

theorem throughAnchor_private (R : ℤ) (p : Site) (hy : 4 ≤ Y R p) (hz : 5 ≤ Z p) :
    privateLevel R (throughAnchor p) (throughUp p) = rho R p ∧
      privateStrip R (throughAnchor p) = alpha R p := by
  have hm := throughAnchor_margins R p hy hz
  have hpY : 0 < Y R p := by omega
  have hpZ : 0 < Z p := by omega
  have haY : 0 < Y R (throughAnchor p) := by omega
  have haZ : 0 < Z (throughAnchor p) := by omega
  simp only [privateLevel, privateStrip, rho, alpha, abs_of_pos hpY, abs_of_pos hpZ,
    abs_of_pos haY, abs_of_pos haZ]
  by_cases hp : InASublattice p.val <;>
    simp [Y, Z, throughAnchor, throughAnchorCoordinates, throughUp, hp] <;> omega

/-- The positive-quadrant avenue through p, indexed by absolute X. -/
def avenueThrough (p : Site) (x : ℤ) : Site :=
  avenue (throughAnchor p) (throughAnchor_A p) (throughUp p) (x - X (throughAnchor p))

@[simp] theorem avenueThrough_x (p : Site) (x : ℤ) : X (avenueThrough p x) = x := by
  change (throughAnchor p).val 0 + (x - (throughAnchor p).val 0) = x
  omega

theorem avenueThrough_injective (p : Site) : Function.Injective (avenueThrough p) := by
  intro x y h
  simpa only [avenueThrough_x] using congrArg X h

theorem avenueThrough_adj (p : Site) (x : ℤ) :
    tetrahedralLattice.Adj (avenueThrough p x) (avenueThrough p (x + 1)) := by
  have h : x - X (throughAnchor p) + 1 = (x + 1) - X (throughAnchor p) := by omega
  simpa only [avenueThrough, h] using
    avenue_adj (throughAnchor p) (throughAnchor_A p) (throughUp p) (x - X (throughAnchor p))

@[simp] theorem avenueThrough_self (p : Site) : avenueThrough p (X p) = p := by
  have hx := congrArg X (avenue_through_site p)
  have hoff : X p - X (throughAnchor p) = throughOffset p := by
    change (throughAnchor p).val 0 + throughOffset p = p.val 0 at hx
    dsimp only [X]
    omega
  simpa only [avenueThrough, hoff] using avenue_through_site p

theorem avenueThrough_member (R : ℤ) (p : Site) (x : ℤ)
    (hy : 4 ≤ Y R p) (hz : 5 ≤ Z p) :
    PositiveQuadrant R (avenueThrough p x) ∧
      (rho R (avenueThrough p x) = rho R p ∨ rho R (avenueThrough p x) = rho R p + 2) ∧
      (alpha R (avenueThrough p x) = alpha R p ∨ alpha R (avenueThrough p x) = alpha R p + 2) := by
  have hm := throughAnchor_margins R p hy hz
  have he := throughAnchor_private R p hy hz
  simpa only [avenueThrough, he.1, he.2] using
    avenue_private R (throughAnchor p) (throughAnchor_A p) (throughUp p)
      (x - X (throughAnchor p)) hm.1 hm.2

end ProteinFolding.Tetrahedral.FarField

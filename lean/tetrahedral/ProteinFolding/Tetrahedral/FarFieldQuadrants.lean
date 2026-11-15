import ProteinFolding.Tetrahedral.FarFieldCoordinates

/-! Lattice automorphisms that change the signs of the transformed Y/Z
coordinates. Reflecting X as well is necessary for diamond-lattice membership.
The z reflection also translates X by two. -/

namespace ProteinFolding.Tetrahedral.FarField

def flipYCoordinates (R : ℤ) (p : Site) : Coordinates :=
  ![-p.val 0, 2 * R - p.val 1, p.val 2]

def flipZCoordinates (p : Site) : Coordinates :=
  ![2 - p.val 0, p.val 1, 2 - p.val 2]

theorem flipY_site (R : ℤ) (hR : R % 2 = 0) (p : Site) :
    IsLatticeSite (flipYCoordinates R p) := by
  rcases p.property with hp | hp
  · left
    have h0 := hp.1 0
    have h1 := hp.1 1
    have h2 := hp.1 2
    have hs := hp.2
    dsimp only [coordinateSum] at hs
    constructor
    · intro k; fin_cases k <;> simp [flipYCoordinates] <;> omega
    · simp [coordinateSum, flipYCoordinates]; omega
  · right
    have h0 := hp.1 0
    have h1 := hp.1 1
    have h2 := hp.1 2
    have hs := hp.2
    dsimp only [coordinateSum] at hs
    constructor
    · intro k; fin_cases k <;> simp [flipYCoordinates] <;> omega
    · simp [coordinateSum, flipYCoordinates]; omega

theorem flipZ_site (p : Site) : IsLatticeSite (flipZCoordinates p) := by
  rcases p.property with hp | hp
  · left
    have h0 := hp.1 0
    have h1 := hp.1 1
    have h2 := hp.1 2
    have hs := hp.2
    dsimp only [coordinateSum] at hs
    constructor
    · intro k; fin_cases k <;> simp [flipZCoordinates] <;> omega
    · simp [coordinateSum, flipZCoordinates]; omega
  · right
    have h0 := hp.1 0
    have h1 := hp.1 1
    have h2 := hp.1 2
    have hs := hp.2
    dsimp only [coordinateSum] at hs
    constructor
    · intro k; fin_cases k <;> simp [flipZCoordinates] <;> omega
    · simp [coordinateSum, flipZCoordinates]; omega

def flipY (R : ℤ) (hR : R % 2 = 0) (p : Site) : Site :=
  ⟨flipYCoordinates R p, flipY_site R hR p⟩

def flipZ (p : Site) : Site := ⟨flipZCoordinates p, flipZ_site p⟩

theorem flipY_involutive (R : ℤ) (hR : R % 2 = 0) : Function.Involutive (flipY R hR) := by
  intro p
  apply Subtype.ext
  funext k
  fin_cases k <;> simp [flipY, flipYCoordinates] <;> omega

theorem flipZ_involutive : Function.Involutive flipZ := by
  intro p
  apply Subtype.ext
  funext k
  fin_cases k <;> simp [flipZ, flipZCoordinates] <;> omega

theorem natAbs_sub_comm (a b : ℤ) : (a - b).natAbs = (b - a).natAbs := by
  rw [← Int.natAbs_neg (a - b), Int.neg_sub]

theorem flipY_adj_iff (R : ℤ) (hR : R % 2 = 0) (p q : Site) :
    tetrahedralLattice.Adj (flipY R hR p) (flipY R hR q) ↔ tetrahedralLattice.Adj p q := by
  rw [CertificatesTM2Geometry.adj_iff_manhattan_three,
    CertificatesTM2Geometry.adj_iff_manhattan_three]
  have hx : -q.val 0 - -p.val 0 = -(q.val 0 - p.val 0) := by omega
  have hy : (2 * R - q.val 1) - (2 * R - p.val 1) = -(q.val 1 - p.val 1) := by omega
  simp [CertificatesTM2Geometry.manhattan, flipY, flipYCoordinates, hx, hy, natAbs_sub_comm]

theorem flipZ_adj_iff (p q : Site) :
    tetrahedralLattice.Adj (flipZ p) (flipZ q) ↔ tetrahedralLattice.Adj p q := by
  rw [CertificatesTM2Geometry.adj_iff_manhattan_three,
    CertificatesTM2Geometry.adj_iff_manhattan_three]
  have hx : (2 - q.val 0) - (2 - p.val 0) = -(q.val 0 - p.val 0) := by omega
  have hz : (2 - q.val 2) - (2 - p.val 2) = -(q.val 2 - p.val 2) := by omega
  simp [CertificatesTM2Geometry.manhattan, flipZ, flipZCoordinates, hx, hz, natAbs_sub_comm]

@[simp] theorem flipY_Y (R : ℤ) (hR : R % 2 = 0) (p : Site) :
    Y R (flipY R hR p) = -Y R p := by
  change 2 * R - p.val 1 - R = -(p.val 1 - R)
  omega

@[simp] theorem flipY_Z (R : ℤ) (hR : R % 2 = 0) (p : Site) : Z (flipY R hR p) = Z p := rfl
@[simp] theorem flipZ_Y (R : ℤ) (p : Site) : Y R (flipZ p) = Y R p := rfl
@[simp] theorem flipZ_Z (p : Site) : Z (flipZ p) = -Z p := by
  change 2 - p.val 2 - 1 = -(p.val 2 - 1)
  omega

@[simp] theorem flipY_rho (R : ℤ) (hR : R % 2 = 0) (p : Site) :
    rho R (flipY R hR p) = rho R p := by simp [rho]
@[simp] theorem flipY_alpha (R : ℤ) (hR : R % 2 = 0) (p : Site) :
    alpha R (flipY R hR p) = alpha R p := by simp [alpha]
@[simp] theorem flipZ_rho (R : ℤ) (p : Site) : rho R (flipZ p) = rho R p := by simp [rho]
@[simp] theorem flipZ_alpha (R : ℤ) (p : Site) : alpha R (flipZ p) = alpha R p := by simp [alpha]

abbrev Quadrant := Bool × Bool

def quadrantMap (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) : Site :=
  let p' := if q.2 then flipZ p else p
  if q.1 then flipY R hR p' else p'

theorem quadrantMap_injective (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) :
    Function.Injective (quadrantMap R hR q) := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b
  · exact Function.injective_id
  · exact flipZ_involutive.injective
  · exact (flipY_involutive R hR).injective
  · exact (flipY_involutive R hR).injective.comp flipZ_involutive.injective

theorem quadrantMap_adj_iff (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p v : Site) :
    tetrahedralLattice.Adj (quadrantMap R hR q p) (quadrantMap R hR q v) ↔
      tetrahedralLattice.Adj p v := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp [quadrantMap, flipY_adj_iff, flipZ_adj_iff]

@[simp] theorem quadrantMap_rho (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) :
    rho R (quadrantMap R hR q p) = rho R p := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp [quadrantMap]

@[simp] theorem quadrantMap_alpha (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) :
    alpha R (quadrantMap R hR q p) = alpha R p := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp [quadrantMap]

def quadrantAvenue (R : ℤ) (hR : R % 2 = 0) (q : Quadrant)
    (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ) : Site :=
  quadrantMap R hR q (avenue c hc up (if q.1 = q.2 then n else -n))

theorem quadrantAvenue_x (R : ℤ) (hR : R % 2 = 0) (q : Quadrant)
    (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ) :
    X (quadrantAvenue R hR q c hc up n) = X (quadrantMap R hR q c) + n := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;>
    simp [X, quadrantAvenue, quadrantMap, flipY, flipZ, flipYCoordinates, flipZCoordinates] <;> omega

theorem quadrantAvenue_injective (R : ℤ) (hR : R % 2 = 0) (q : Quadrant)
    (c : Site) (hc : InASublattice c.val) (up : Bool) :
    Function.Injective (quadrantAvenue R hR q c hc up) := by
  intro n m h
  have hx := congrArg X h
  simp only [quadrantAvenue_x] at hx
  omega

theorem quadrantAvenue_adj (R : ℤ) (hR : R % 2 = 0) (q : Quadrant)
    (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ) :
    tetrahedralLattice.Adj (quadrantAvenue R hR q c hc up n)
      (quadrantAvenue R hR q c hc up (n + 1)) := by
  apply (quadrantMap_adj_iff R hR q _ _).2
  by_cases hq : q.1 = q.2
  · simpa only [if_pos hq] using avenue_adj c hc up n
  · simp only [if_neg hq]
    have h : -(n + 1) + 1 = -n := by omega
    simpa only [h] using (avenue_adj c hc up (-(n + 1))).symm

end ProteinFolding.Tetrahedral.FarField

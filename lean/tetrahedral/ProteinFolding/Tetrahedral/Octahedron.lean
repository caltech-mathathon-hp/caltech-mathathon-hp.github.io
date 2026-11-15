import ProteinFolding.Tetrahedral.Geometry
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

/-!
# The finite octahedron of Sections 5.1 and 5.6

The definition uses all eight halfspaces from the manuscript. A generous
finite coordinate box supplies an executable enumeration; the membership
theorem proves that the box imposes no extra restriction.
-/

namespace ProteinFolding.Tetrahedral

def octRadius (m : ℕ) : ℤ := 2 * (m : ℤ) - 2

def octCentre (m : ℕ) : Coordinates := fun k => if k = 1 then octRadius m else 0

/-- The four signed face coordinates t_i dot (p-c). -/
def tetraCoordinate (m : ℕ) (p : Coordinates) (i : Fin 4) : ℤ :=
  if i = 0 then p 0 + (p 1 - octRadius m) + p 2
  else if i = 1 then p 0 - (p 1 - octRadius m) - p 2
  else if i = 2 then -p 0 + (p 1 - octRadius m) - p 2
  else -p 0 - (p 1 - octRadius m) + p 2

theorem tetraCoordinate_eq_dot (m : ℕ) (p : Coordinates) (i : Fin 4) :
    tetraCoordinate m p i =
      bondVector i 0 * (p 0 - octCentre m 0) +
      bondVector i 1 * (p 1 - octCentre m 1) +
      bondVector i 2 * (p 2 - octCentre m 2) := by
  fin_cases i
  · change p 0 + (p 1 - octRadius m) + p 2 =
      1 * (p 0 - 0) + 1 * (p 1 - octRadius m) + 1 * (p 2 - 0)
    omega
  · change p 0 - (p 1 - octRadius m) - p 2 =
      1 * (p 0 - 0) + (-1) * (p 1 - octRadius m) + (-1) * (p 2 - 0)
    omega
  · change -p 0 + (p 1 - octRadius m) - p 2 =
      (-1) * (p 0 - 0) + 1 * (p 1 - octRadius m) + (-1) * (p 2 - 0)
    omega
  · change -p 0 - (p 1 - octRadius m) + p 2 =
      (-1) * (p 0 - 0) + (-1) * (p 1 - octRadius m) + 1 * (p 2 - 0)
    omega

theorem tetraCoordinate_sum (m : ℕ) (p : Coordinates) :
    tetraCoordinate m p 0 + tetraCoordinate m p 1 +
      tetraCoordinate m p 2 + tetraCoordinate m p 3 = 0 := by
  dsimp [tetraCoordinate]
  omega

theorem tetraCoordinate_pair_x (m : ℕ) (p : Coordinates) :
    tetraCoordinate m p 0 + tetraCoordinate m p 1 = 2 * p 0 := by
  dsimp [tetraCoordinate]
  omega

theorem tetraCoordinate_pair_y (m : ℕ) (p : Coordinates) :
    tetraCoordinate m p 0 + tetraCoordinate m p 2 = 2 * (p 1 - octRadius m) := by
  dsimp [tetraCoordinate]
  omega

theorem tetraCoordinate_pair_z (m : ℕ) (p : Coordinates) :
    tetraCoordinate m p 0 + tetraCoordinate m p 3 = 2 * p 2 := by
  dsimp [tetraCoordinate]
  omega

theorem tetraCoordinate_injective (m : ℕ) : Function.Injective (tetraCoordinate m) := by
  intro p q heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  have h3 := congrFun heq 3
  have hx := tetraCoordinate_pair_x m p
  have hx' := tetraCoordinate_pair_x m q
  have hy := tetraCoordinate_pair_y m p
  have hy' := tetraCoordinate_pair_y m q
  have hz := tetraCoordinate_pair_z m p
  have hz' := tetraCoordinate_pair_z m q
  funext k
  fin_cases k
  · change p 0 = q 0; omega
  · change p 1 = q 1; omega
  · change p 2 = q 2; omega

/-- The eight halfspace inequalities, before exploiting lattice congruences. -/
def InOctahedron (m : ℕ) (p : Site) : Prop :=
  ∀ i : Fin 4, -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m p.val i ∧
    tetraCoordinate m p.val i ≤ octRadius m

instance decidableInOctahedron (m : ℕ) : DecidablePred (InOctahedron m) :=
  fun p => inferInstanceAs (Decidable (∀ i : Fin 4,
    -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m p.val i ∧
      tetraCoordinate m p.val i ≤ octRadius m))

theorem tetraCoordinate_mod_A (m : ℕ) {p : Coordinates} (hp : InASublattice p)
    (i : Fin 4) : tetraCoordinate m p i % 4 = octRadius m % 4 := by
  have h0 := hp.1 0
  have h1 := hp.1 1
  have h2 := hp.1 2
  have hs := hp.2
  change (p 0 + p 1 + p 2) % 4 = 0 at hs
  fin_cases i <;> dsimp [tetraCoordinate, octRadius] <;> omega

theorem tetraCoordinate_mod_B (m : ℕ) {p : Coordinates} (hp : InBSublattice p)
    (i : Fin 4) : tetraCoordinate m p i % 4 = (2 * (m : ℤ) + 1) % 4 := by
  have h0 := hp.1 0
  have h1 := hp.1 1
  have h2 := hp.1 2
  have hs := hp.2
  change (p 0 + p 1 + p 2) % 4 = 3 at hs
  fin_cases i <;> dsimp [tetraCoordinate, octRadius] <;> omega

theorem inOctahedron_iff_A (m : ℕ) {p : Site} (hp : InASublattice p.val) :
    InOctahedron m p ↔ ∀ i : Fin 4,
      -octRadius m ≤ tetraCoordinate m p.val i ∧ tetraCoordinate m p.val i ≤ octRadius m := by
  constructor
  · intro h i
    have hi := h i
    have hc := tetraCoordinate_mod_A m hp i
    dsimp [octRadius] at *
    exact ⟨by omega, hi.2⟩
  · intro h i
    have hi := h i
    dsimp [octRadius] at *
    exact ⟨by omega, hi.2⟩

theorem inOctahedron_iff_B (m : ℕ) {p : Site} (hp : InBSublattice p.val) :
    InOctahedron m p ↔ ∀ i : Fin 4,
      -(2 * (m : ℤ) - 1) ≤ tetraCoordinate m p.val i ∧
        tetraCoordinate m p.val i ≤ 2 * (m : ℤ) - 3 := by
  constructor
  · intro h i
    have hi := h i
    have hc := tetraCoordinate_mod_B m hp i
    dsimp [octRadius] at *
    exact ⟨hi.1, by omega⟩
  · intro h i
    have hi := h i
    dsimp [octRadius] at *
    exact ⟨hi.1, by omega⟩

theorem inOctahedron_coordinate_bound {m : ℕ} {p : Site} (hp : InOctahedron m p)
    (k : Fin 3) :
    octCentre m k - (2 * (m : ℤ) + 1) ≤ p.val k ∧
      p.val k ≤ octCentre m k + (2 * (m : ℤ) + 1) := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have hx := tetraCoordinate_pair_x m p.val
  have hy := tetraCoordinate_pair_y m p.val
  have hz := tetraCoordinate_pair_z m p.val
  dsimp only [octRadius] at h0 h1 h2 h3 hx hy hz
  fin_cases k <;> dsimp [octCentre, octRadius] <;> omega

def octCoordinateBox (m : ℕ) : Finset Coordinates :=
  Fintype.piFinset (fun k : Fin 3 =>
    Finset.Icc (octCentre m k - (2 * (m : ℤ) + 1))
      (octCentre m k + (2 * (m : ℤ) + 1)))

/-- An actual finite set of diamond-lattice sites, with no extra bounding-box input. -/
def octahedron (m : ℕ) : Finset Site :=
  ((octCoordinateBox m).subtype IsLatticeSite).filter (InOctahedron m)

@[simp] theorem mem_octahedron (m : ℕ) (p : Site) :
    p ∈ octahedron m ↔ InOctahedron m p := by
  simp only [octahedron, Finset.mem_filter, Finset.mem_subtype]
  constructor
  · exact And.right
  · intro hp
    refine ⟨?_, hp⟩
    apply Fintype.mem_piFinset.mpr
    intro k
    exact Finset.mem_Icc.mpr (inOctahedron_coordinate_bound hp k)

theorem octahedron_zero : octahedron 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := (mem_octahedron 0 p).mp hp 0
  dsimp [octRadius] at h
  omega

end ProteinFolding.Tetrahedral

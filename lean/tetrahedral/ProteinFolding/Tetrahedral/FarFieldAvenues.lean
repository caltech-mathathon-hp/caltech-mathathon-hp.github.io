import ProteinFolding.Tetrahedral.Normalization
import ProteinFolding.Tetrahedral.CertificatesTM2Geometry
import Mathlib.Tactic.NormNum

/-! Explicit periodic coordinate parametrizations of the two avenues used in
Lemma F(D). Index zero is an A-sublattice crossing site; the Boolean records
whether its next rung goes outwards or inwards. The second avenue is the
lattice translate (0,2,-2), so its strip is disjoint from the first. -/

namespace ProteinFolding.Tetrahedral.FarField

def avenueY (up : Bool) (n : ℤ) : ℤ :=
  if n % 4 = 0 then 0 else if n % 4 = 1 then (if up then 1 else -1)
  else if n % 4 = 2 then (if up then 0 else -2) else -1

def avenueZ (up : Bool) (n : ℤ) : ℤ :=
  if n % 4 = 0 then 0 else if n % 4 = 1 then (if up then 1 else -1)
  else if n % 4 = 2 then (if up then 2 else 0) else 1

def avenueCoordinates (c : Site) (up : Bool) (n : ℤ) : Coordinates :=
  ![c.val 0 + n, c.val 1 + avenueY up n, c.val 2 + avenueZ up n]

theorem avenueCoordinates_site (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ) :
    IsLatticeSite (avenueCoordinates c up n) := by
  have h0 := hc.1 0
  have h1 := hc.1 1
  have h2 := hc.1 2
  have hs := hc.2
  have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  dsimp only [coordinateSum] at hs
  rcases hr with hr | hr | hr | hr <;> cases up
  all_goals
    first
    | left; constructor
      · intro k; fin_cases k <;> simp [avenueCoordinates, avenueY, avenueZ, hr] <;> omega
      · simp [coordinateSum, avenueCoordinates, avenueY, avenueZ, hr]; omega
    | right; constructor
      · intro k; fin_cases k <;> simp [avenueCoordinates, avenueY, avenueZ, hr] <;> omega
      · simp [coordinateSum, avenueCoordinates, avenueY, avenueZ, hr]; omega

def avenue (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ) : Site :=
  ⟨avenueCoordinates c up n, avenueCoordinates_site c hc up n⟩

@[simp] theorem avenue_x (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ) :
    (avenue c hc up n).val 0 = c.val 0 + n := rfl

theorem avenue_injective (c : Site) (hc : InASublattice c.val) (up : Bool) :
    Function.Injective (avenue c hc up) := by
  intro n m h
  have hx := congrArg (fun p : Site => p.val 0) h
  simp only [avenue_x] at hx
  omega

theorem avenue_A_iff (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ) :
    InASublattice (avenue c hc up n).val ↔ n % 2 = 0 := by
  constructor
  · intro h
    have hx := h.1 0
    have hcx := hc.1 0
    simp only [avenue_x] at hx
    omega
  · intro hn
    rcases (avenue c hc up n).property with h | h
    · exact h
    · have hx := h.1 0
      have hcx := hc.1 0
      simp only [avenue_x] at hx
      omega

theorem avenue_adj (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ) :
    tetrahedralLattice.Adj (avenue c hc up n) (avenue c hc up (n + 1)) := by
  apply (CertificatesTM2Geometry.adj_iff_manhattan_three _ _).2
  have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr with hr | hr | hr | hr <;> cases up
  all_goals
    have hnext : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
    simp only [hr] at hnext
    norm_num at hnext
    simp [CertificatesTM2Geometry.manhattan, avenue, avenueCoordinates, avenueY,
      avenueZ, hr, hnext, add_sub_add_left_eq_sub]

def secondAnchor (c : Site) (hc : InASublattice c.val) : Site :=
  ⟨![c.val 0, c.val 1 + 2, c.val 2 - 2], Or.inl (by
    have h0 := hc.1 0
    have h1 := hc.1 1
    have h2 := hc.1 2
    have hs := hc.2
    simp [InASublattice, coordinateSum, Fin.forall_fin_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at *
    omega)⟩

theorem secondAnchor_A (c : Site) (hc : InASublattice c.val) :
    InASublattice (secondAnchor c hc).val := by
  rcases (secondAnchor c hc).property with h | h
  · exact h
  · have h1 := h.1 0
    have h0 := hc.1 0
    change c.val 0 % 2 = 1 at h1
    omega

def secondAvenue (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ) : Site :=
  avenue (secondAnchor c hc) (secondAnchor_A c hc) up n

theorem avenues_disjoint (c : Site) (hc : InASublattice c.val) (up : Bool) (n m : ℤ) :
    avenue c hc up n ≠ secondAvenue c hc up m := by
  intro h
  have hx := congrArg (fun p : Site => p.val 0) h
  have hy := congrArg (fun p : Site => p.val 1) h
  change c.val 0 + n = c.val 0 + m at hx
  have hnm : n = m := by omega
  subst m
  change c.val 1 + avenueY up n = (c.val 1 + 2) + avenueY up n at hy
  omega

theorem secondAvenue_injective (c : Site) (hc : InASublattice c.val) (up : Bool) :
    Function.Injective (secondAvenue c hc up) :=
  avenue_injective (secondAnchor c hc) (secondAnchor_A c hc) up

theorem secondAvenue_adj (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ) :
    tetrahedralLattice.Adj (secondAvenue c hc up n) (secondAvenue c hc up (n + 1)) :=
  avenue_adj _ _ _ _

theorem crossing_zero (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ)
    (hn : n % 4 = 0) :
    tetrahedralLattice.Adj (avenue c hc up n) (secondAvenue c hc up (n - 1)) := by
  apply (CertificatesTM2Geometry.adj_iff_manhattan_three _ _).2
  have hm : (n - 1) % 4 = 3 := by omega
  have hy : c.val 1 + 2 + -1 - c.val 1 = 1 := by omega
  have hz : c.val 2 - 2 + 1 - c.val 2 = -1 := by omega
  cases up <;>
    simp [CertificatesTM2Geometry.manhattan, secondAvenue, secondAnchor,
      avenue, avenueCoordinates, avenueY, avenueZ, hn, hm, add_sub_add_left_eq_sub, hy, hz]

theorem crossing_one (c : Site) (hc : InASublattice c.val) (up : Bool) (n : ℤ)
    (hn : n % 4 = 1) :
    tetrahedralLattice.Adj (avenue c hc up n) (secondAvenue c hc up (n + 1)) := by
  apply (CertificatesTM2Geometry.adj_iff_manhattan_three _ _).2
  have hm : (n + 1) % 4 = 2 := by omega
  have hz : c.val 2 - 2 - (c.val 2 + -1) = -1 := by omega
  cases up <;>
    simp [CertificatesTM2Geometry.manhattan, secondAvenue, secondAnchor,
      avenue, avenueCoordinates, avenueY, avenueZ, hn, hm, add_sub_add_left_eq_sub, hz]

def avenueSite (c : Site) (hc : InASublattice c.val) (up : Bool) (v : Bool × ℤ) : Site :=
  if v.1 then secondAvenue c hc up v.2 else avenue c hc up v.2

theorem avenueSite_injective (c : Site) (hc : InASublattice c.val) (up : Bool) :
    Function.Injective (avenueSite c hc up) := by
  rintro ⟨a, n⟩ ⟨b, m⟩ h
  cases a <;> cases b
  · simp only [avenueSite, Bool.false_eq_true, ↓reduceIte] at h
    exact congrArg (Prod.mk false) (avenue_injective c hc up h)
  · exact False.elim (avenues_disjoint c hc up n m h)
  · exact False.elim (avenues_disjoint c hc up m n h.symm)
  · simp only [avenueSite, ↓reduceIte] at h
    exact congrArg (Prod.mk true) (secondAvenue_injective c hc up h)

end ProteinFolding.Tetrahedral.FarField


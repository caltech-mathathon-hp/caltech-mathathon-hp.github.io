import ProteinFolding.Tetrahedral.OctahedralBoundary
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs

/-! Section 5.6 (O6): coefficient distance is a lower bound for every lattice path. -/

namespace ProteinFolding.Tetrahedral

def siteCharge (p : Site) : ℤ := if InASublattice p.val then 0 else 1

theorem siteCharge_A {p : Site} (hp : InASublattice p.val) : siteCharge p = 0 := by
  simp only [siteCharge, if_pos hp]

theorem siteCharge_B {p : Site} (hp : InBSublattice p.val) : siteCharge p = 1 := by
  simp only [siteCharge, if_neg ((inB_iff_not_inA p).mp hp)]

theorem siteCharge_eq_x_mod (p : Site) : siteCharge p = p.val 0 % 2 := by
  rcases p.property with hp | hp
  · rw [siteCharge_A hp, hp.1 0]
  · rw [siteCharge_B hp, hp.1 0]

/-- The diamond lattice embeds into the two adjacent integer hyperplanes
of Z^4 with coefficient sum zero or one. -/
def tetraLift (p : Site) (i : Fin 4) : ℤ :=
  (tetraCoordinate 1 p.val i + siteCharge p) / 4

theorem tetraLift_spec (p : Site) (i : Fin 4) :
    4 * tetraLift p i = tetraCoordinate 1 p.val i + siteCharge p := by
  rcases p.property with hp | hp
  · have hm := tetraCoordinate_mod_A 1 hp i
    have hc := siteCharge_A hp
    dsimp [octRadius] at hm
    dsimp [tetraLift]
    omega
  · have hm := tetraCoordinate_mod_B 1 hp i
    have hc := siteCharge_B hp
    change tetraCoordinate 1 p.val i % 4 = 3 at hm
    dsimp [tetraLift]
    omega

theorem tetraLift_step_A {p : Site} (hp : InASublattice p.val) (d i : Fin 4) :
    tetraLift (step p d) i = tetraLift p i + if i = d then 1 else 0 := by
  have hq := tetraLift_spec (step p d) i
  have hp' := tetraLift_spec p i
  have hstep := tetraCoordinate_step_A 1 hp d i
  rw [siteCharge_A hp] at hp'
  rw [siteCharge_B (step_in_B hp d)] at hq
  split_ifs <;> omega

theorem tetraLift_step_B {p : Site} (hp : InBSublattice p.val) (d i : Fin 4) :
    tetraLift (step p d) i = tetraLift p i - if i = d then 1 else 0 := by
  have hq := tetraLift_spec (step p d) i
  have hp' := tetraLift_spec p i
  have hstep := tetraCoordinate_step_B 1 hp d i
  rw [siteCharge_B hp] at hp'
  rw [siteCharge_A (step_in_A hp d)] at hq
  split_ifs <;> omega

def tetraCoefficientDistance (p q : Site) : ℤ :=
  ∑ i : Fin 4, |tetraLift q i - tetraLift p i|

@[simp] theorem tetraCoefficientDistance_self (p : Site) : tetraCoefficientDistance p p = 0 := by
  simp [tetraCoefficientDistance]

theorem tetraCoefficientDistance_triangle (p q r : Site) :
    tetraCoefficientDistance p r ≤ tetraCoefficientDistance p q + tetraCoefficientDistance q r := by
  unfold tetraCoefficientDistance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  calc
    |tetraLift r i - tetraLift p i| =
        |(tetraLift q i - tetraLift p i) + (tetraLift r i - tetraLift q i)| := by
      congr 1
      omega
    _ ≤ |tetraLift q i - tetraLift p i| + |tetraLift r i - tetraLift q i| := abs_add_le _ _

theorem tetraCoefficientDistance_adj {p q : Site} (hadj : tetrahedralLattice.Adj p q) :
    tetraCoefficientDistance p q = 1 := by
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp hadj
  unfold tetraCoefficientDistance
  have hcomp : ∀ i : Fin 4, |tetraLift (step p d) i - tetraLift p i| =
      if i = d then 1 else 0 := by
    intro i
    rcases p.property with hp | hp
    · rw [tetraLift_step_A hp]
      split_ifs <;> simp_all
    · rw [tetraLift_step_B hp]
      split_ifs <;> simp_all
  simp_rw [hcomp]
  simp

/-- This bound concerns arbitrary paths; intermediate sites may be anywhere. -/
theorem path_coefficient_distance_bound (f : ℕ → Site) (n : ℕ)
    (hstep : ∀ i < n, tetrahedralLattice.Adj (f i) (f (i + 1))) :
    tetraCoefficientDistance (f 0) (f n) ≤ (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun i hi => hstep i (by omega))
    have htri := tetraCoefficientDistance_triangle (f 0) (f n) (f (n + 1))
    have hs := tetraCoefficientDistance_adj (hstep n (by omega))
    push_cast
    omega

theorem tetraLift_difference_of_combination (p q : Site) (coeff : Fin 4 → ℤ)
    (hsum : ∑ i : Fin 4, coeff i = 0)
    (hcoords : ∀ k : Fin 3, q.val k - p.val k =
      ∑ i : Fin 4, coeff i * bondVector i k) :
    ∀ i : Fin 4, tetraLift q i - tetraLift p i = coeff i := by
  have hx := hcoords 0
  have hy := hcoords 1
  have hz := hcoords 2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum hx hy hz
  change coeff 0 + (coeff 1 + (coeff 2 + (coeff 3 + 0))) = 0 at hsum
  change q.val 0 - p.val 0 = coeff 0 * 1 +
    (coeff 1 * 1 + (coeff 2 * (-1) + (coeff 3 * (-1) + 0))) at hx
  change q.val 1 - p.val 1 = coeff 0 * 1 +
    (coeff 1 * (-1) + (coeff 2 * 1 + (coeff 3 * (-1) + 0))) at hy
  change q.val 2 - p.val 2 = coeff 0 * 1 +
    (coeff 1 * (-1) + (coeff 2 * (-1) + (coeff 3 * 1 + 0))) at hz
  simp only [mul_one, mul_neg_one, add_zero] at hx hy hz
  have hcharge : siteCharge q = siteCharge p := by
    rw [siteCharge_eq_x_mod, siteCharge_eq_x_mod]
    omega
  intro i
  have hp := tetraLift_spec p i
  have hq := tetraLift_spec q i
  rw [hcharge] at hq
  fin_cases i <;> dsimp [tetraCoordinate, octRadius] at hp hq ⊢ <;> omega

/-- O6, in the manuscript's notation: zero-sum bond-vector coefficients have
L1 norm no larger than the length of any path between their endpoints. -/
theorem path_length_ge_coefficient_norm (f : ℕ → Site) (n : ℕ)
    (hstep : ∀ i < n, tetrahedralLattice.Adj (f i) (f (i + 1)))
    (coeff : Fin 4 → ℤ) (hsum : ∑ i : Fin 4, coeff i = 0)
    (hcoords : ∀ k : Fin 3, (f n).val k - (f 0).val k =
      ∑ i : Fin 4, coeff i * bondVector i k) :
    (∑ i : Fin 4, |coeff i|) ≤ (n : ℤ) := by
  have hdiff := tetraLift_difference_of_combination (f 0) (f n) coeff hsum hcoords
  have hbound := path_coefficient_distance_bound f n hstep
  simpa only [tetraCoefficientDistance, hdiff] using hbound

end ProteinFolding.Tetrahedral

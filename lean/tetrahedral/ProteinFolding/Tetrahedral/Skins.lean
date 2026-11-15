import ProteinFolding.Tetrahedral.OctahedralBoundary
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-! The expanded octahedra O_j of Section 8.2 have size m+2j and keep
the original centre c_m. In particular they are not octahedron (m+2j),
whose definition moves the centre with its size. -/

namespace ProteinFolding.Tetrahedral

def InSkinSolid (m j : ℕ) (p : Site) : Prop :=
  ∀ i : Fin 4, -(2 * ((m + 2 * j : ℕ) : ℤ) - 1) ≤ tetraCoordinate m p.val i ∧
    tetraCoordinate m p.val i ≤ 2 * ((m + 2 * j : ℕ) : ℤ) - 2

instance decidableInSkinSolid (m j : ℕ) : DecidablePred (InSkinSolid m j) :=
  fun p => inferInstanceAs (Decidable (∀ i : Fin 4,
    -(2 * ((m + 2 * j : ℕ) : ℤ) - 1) ≤ tetraCoordinate m p.val i ∧
      tetraCoordinate m p.val i ≤ 2 * ((m + 2 * j : ℕ) : ℤ) - 2))

theorem inSkinSolid_l1_bound (m j : ℕ) {p : Site} (hp : InSkinSolid m j p) :
    |p.val 0| + |p.val 1 - octRadius m| + |p.val 2| ≤
      2 * ((m + 2 * j : ℕ) : ℤ) - 1 := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  dsimp [tetraCoordinate] at h0 h1 h2 h3
  by_cases hx : 0 ≤ p.val 0 <;>
    by_cases hy : 0 ≤ p.val 1 - octRadius m <;>
      by_cases hz : 0 ≤ p.val 2
  all_goals first | rw [abs_of_nonneg hx] | rw [abs_of_neg (lt_of_not_ge hx)]
  all_goals first | rw [abs_of_nonneg hy] | rw [abs_of_neg (lt_of_not_ge hy)]
  all_goals first | rw [abs_of_nonneg hz] | rw [abs_of_neg (lt_of_not_ge hz)]
  all_goals omega

theorem inSkinSolid_coordinate_bound (m j : ℕ) {p : Site} (hp : InSkinSolid m j p)
    (k : Fin 3) :
    octCentre m k - (2 * ((m + 2 * j : ℕ) : ℤ) + 1) ≤ p.val k ∧
      p.val k ≤ octCentre m k + (2 * ((m + 2 * j : ℕ) : ℤ) + 1) := by
  have h := inSkinSolid_l1_bound m j hp
  have hx := le_abs_self (p.val 0)
  have hx' := neg_le_abs (p.val 0)
  have hy := le_abs_self (p.val 1 - octRadius m)
  have hy' := neg_le_abs (p.val 1 - octRadius m)
  have hz := le_abs_self (p.val 2)
  have hz' := neg_le_abs (p.val 2)
  have ha := abs_nonneg (p.val 0)
  have hb := abs_nonneg (p.val 1 - octRadius m)
  have hc := abs_nonneg (p.val 2)
  fin_cases k <;> dsimp [octCentre] <;> omega

def skinCoordinateBox (m j : ℕ) : Finset Coordinates :=
  Fintype.piFinset fun k : Fin 3 =>
    Finset.Icc (octCentre m k - (2 * ((m + 2 * j : ℕ) : ℤ) + 1))
      (octCentre m k + (2 * ((m + 2 * j : ℕ) : ℤ) + 1))

def skinSolid (m j : ℕ) : Finset Site :=
  ((skinCoordinateBox m j).subtype IsLatticeSite).filter (InSkinSolid m j)

@[simp] theorem mem_skinSolid (m j : ℕ) (p : Site) :
    p ∈ skinSolid m j ↔ InSkinSolid m j p := by
  simp only [skinSolid, Finset.mem_filter, Finset.mem_subtype]
  constructor
  · exact And.right
  · intro hp
    refine ⟨?_, hp⟩
    apply Fintype.mem_piFinset.mpr
    intro k
    exact Finset.mem_Icc.mpr (inSkinSolid_coordinate_bound m j hp k)

theorem skinSolid_zero (m : ℕ) : skinSolid m 0 = octahedron m := by
  ext p
  simp only [mem_skinSolid, mem_octahedron, InSkinSolid, InOctahedron, octRadius,
    Nat.mul_zero, Nat.add_zero]

theorem skinSolid_mono (m : ℕ) : Monotone (skinSolid m) := by
  intro i j hij p hp
  rw [mem_skinSolid] at hp ⊢
  intro d
  have h := hp d
  push_cast at h ⊢
  omega

def skin (m j : ℕ) : Finset Site := skinSolid m j \ skinSolid m (j - 1)

theorem skin_subset_solid (m j : ℕ) : skin m j ⊆ skinSolid m j := Finset.sdiff_subset

theorem skins_disjoint (m i j : ℕ) (hij : i < j) : Disjoint (skin m i) (skin m j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := (Finset.mem_sdiff.mp hp).1
  have hq' := (Finset.mem_sdiff.mp hq).2
  exact hq' (skinSolid_mono m (show i ≤ j - 1 by omega) hp')

theorem tetraCoordinate_adj_bounds (m : ℕ) {p q : Site}
    (hadj : tetrahedralLattice.Adj p q) (i : Fin 4) :
    tetraCoordinate m p.val i - 3 ≤ tetraCoordinate m q.val i ∧
      tetraCoordinate m q.val i ≤ tetraCoordinate m p.val i + 3 := by
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp hadj
  rcases p.property with hpA | hpB
  · rw [tetraCoordinate_step_A m hpA]
    split_ifs <;> omega
  · rw [tetraCoordinate_step_B m hpB]
    split_ifs <;> omega

theorem neighbour_of_oct_mem_skinSolid_one (m : ℕ) {p q : Site}
    (hp : p ∈ octahedron m) (hadj : tetrahedralLattice.Adj p q) : q ∈ skinSolid m 1 := by
  rw [mem_skinSolid]
  intro d
  have h := ((mem_octahedron m p).mp hp) d
  have hstep := tetraCoordinate_adj_bounds m hadj d
  dsimp only [octRadius] at h
  push_cast
  omega

theorem dangling_mem_skin_one (m : ℕ) {p q : Site}
    (hp : p ∈ octahedron m) (hadj : tetrahedralLattice.Adj p q)
    (hq : q ∉ octahedron m) : q ∈ skin m 1 := by
  apply Finset.mem_sdiff.mpr
  refine ⟨neighbour_of_oct_mem_skinSolid_one m hp hadj, ?_⟩
  simpa only [Nat.sub_self, skinSolid_zero] using hq

theorem skinSolid_rho_bound (m j : ℕ) {p : Site} (hp : p ∈ skinSolid m j) :
    |p.val 1 - octRadius m| + |p.val 2 - 1| ≤ 2 * ((m + 2 * j : ℕ) : ℤ) := by
  have h := inSkinSolid_l1_bound m j ((mem_skinSolid m j p).mp hp)
  have hz := abs_sub_le (p.val 2) (0 : ℤ) (1 : ℤ)
  have hx := abs_nonneg (p.val 0)
  simp only [sub_zero, zero_sub, abs_neg, abs_one] at hz
  omega

theorem exists_mem_skinSolid (m : ℕ) (p : Site) : ∃ j, p ∈ skinSolid m j := by
  let j : ℕ := (∑ i : Fin 4, (tetraCoordinate m p.val i).natAbs) + 1
  refine ⟨j, ?_⟩
  rw [mem_skinSolid]
  intro i
  have hnat : (tetraCoordinate m p.val i).natAbs < j := by
    have h : (tetraCoordinate m p.val i).natAbs ≤
        ∑ d : Fin 4, (tetraCoordinate m p.val d).natAbs :=
      Finset.single_le_sum (fun d (_ : d ∈ Finset.univ) =>
        Nat.zero_le (tetraCoordinate m p.val d).natAbs) (Finset.mem_univ i)
    dsimp only [j]
    omega
  have hcast : ((tetraCoordinate m p.val i).natAbs : ℤ) < (j : ℤ) := by
    exact_mod_cast hnat
  rw [Int.natCast_natAbs] at hcast
  have hupper := le_abs_self (tetraCoordinate m p.val i)
  have hlower := neg_le_abs (tetraCoordinate m p.val i)
  push_cast
  omega

/-- The complement of Oct(m) is covered by the pairwise disjoint positive
skins, with the same fixed centre in every expanded solid. -/
theorem outside_mem_skin (m : ℕ) (p : Site) (hp : p ∉ octahedron m) :
    ∃ j : ℕ, 0 < j ∧ p ∈ skin m j := by
  have hex := exists_mem_skinSolid m p
  let j := Nat.find hex
  have hj : p ∈ skinSolid m j := Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra h
    have hjzero : j = 0 := by omega
    rw [hjzero, skinSolid_zero] at hj
    exact hp hj
  refine ⟨j, hjpos, Finset.mem_sdiff.mpr ⟨hj, ?_⟩⟩
  exact Nat.find_min hex (show j - 1 < j by omega)

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.ColumnsValues
import ProteinFolding.Tetrahedral.ColumnsDisjoint
import ProteinFolding.Tetrahedral.Skins

/-! Every column crosses every positive skin in exactly two sites. -/

namespace ProteinFolding.Tetrahedral

theorem twoStep_tetraCoordinate_bounds (m : ℕ) (p : Site) (d e i : Fin 4) :
    tetraCoordinate m p.val i - 4 ≤ tetraCoordinate m (step (step p d) e).val i ∧
      tetraCoordinate m (step (step p d) e).val i ≤ tetraCoordinate m p.val i + 4 := by
  rcases p.property with hpA | hpB
  · have h1 := tetraCoordinate_step_A m hpA d i
    have h2 := tetraCoordinate_step_B m (step_in_B hpA d) e i
    split_ifs at h1 h2 <;> omega
  · have h1 := tetraCoordinate_step_B m hpB d i
    have h2 := tetraCoordinate_step_A m (step_in_A hpB d) e i
    split_ifs at h1 h2 <;> omega

theorem bulkArmPoint_two_tetra_bounds (m : ℕ) (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) (p : Site) (i : Fin 4) :
    tetraCoordinate m p.val i - 4 ≤ tetraCoordinate m (bulkArmPoint sy sz p 2).val i ∧
      tetraCoordinate m (bulkArmPoint sy sz p 2).val i ≤ tetraCoordinate m p.val i + 4 := by
  have hx := bulkArmPoint_x_charge sy sz hsy hsz p 2
  have hc : siteCharge (bulkArmPoint sy sz p 2) = siteCharge p := by
    simpa only [show (2 : ℕ) % 2 = 0 from rfl, ite_true] using bulkArmPoint_charge sy sz p 2
  rw [hc] at hx
  simp only [sub_self, zero_mul, add_zero] at hx
  have hy := bulkArmPoint_y m sy sz hsy hsz p 2
  have hz := bulkArmPoint_z sy sz hsy hsz p 2
  rcases hsy with rfl | rfl <;> rcases hsz with rfl | rfl <;> fin_cases i <;>
    dsimp [tetraCoordinate, bulkY, bulkZ] at hx hy hz ⊢
  all_goals omega

theorem skinSolid_arm_two (m j : ℕ) (sy sz : ℤ)
    (hsy : sy = 1 ∨ sy = -1) (hsz : sz = 1 ∨ sz = -1) {p : Site}
    (hp : p ∈ skinSolid m j) : bulkArmPoint sy sz p 2 ∈ skinSolid m (j + 1) := by
  rw [mem_skinSolid] at hp ⊢
  intro i
  have h := hp i
  have hb := bulkArmPoint_two_tetra_bounds m sy sz hsy hsz p i
  push_cast at *
  constructor <;> omega

namespace DanglingColumn

variable {m : ℕ} (C : DanglingColumn m)

theorem point_one_eq : C.point 1 = step (step C.owner C.dir) (columnOpposite C.dir) := by
  change bulkArmNext C.sy C.sz C.seed = _
  rcases C.owner.property with hpA | hpB
  · have hsB : InBSublattice C.seed.val := step_in_B hpA C.dir
    rw [bulkArmNext, if_neg ((inB_iff_not_inA _).mp hsB), sy, sz, if_pos hpA, if_pos hpA,
      smallFace_quadrant_direction]
    rfl
  · have hsA : InASublattice C.seed.val := step_in_A hpB C.dir
    rw [bulkArmNext, if_pos hsA, sy, sz, if_neg ((inB_iff_not_inA _).mp hpB),
      if_neg ((inB_iff_not_inA _).mp hpB), smallFace_quadrant_direction]
    rfl

theorem point_zero_mem_solid_one : C.point 0 ∈ skinSolid m 1 :=
  neighbour_of_oct_mem_skinSolid_one m C.owner_mem (step_adj C.owner C.dir)

theorem point_one_mem_solid_one : C.point 1 ∈ skinSolid m 1 := by
  rw [C.point_one_eq, mem_skinSolid]
  intro i
  have hp := (mem_octahedron m C.owner).mp C.owner_mem i
  have hb := twoStep_tetraCoordinate_bounds m C.owner C.dir (columnOpposite C.dir) i
  dsimp [octRadius] at hp
  push_cast
  constructor <;> omega

theorem point_mem_own_solid (n : ℕ) : C.point n ∈ skinSolid m (n / 2 + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact C.point_zero_mem_solid_one
    by_cases hn1 : n = 1
    · subst n
      exact C.point_one_mem_solid_one
    have hn : 2 ≤ n := by omega
    have hp := ih (n - 2) (by omega)
    have hs := skinSolid_arm_two m ((n - 2) / 2 + 1) C.sy C.sz C.sy_unit C.sz_unit hp
    change bulkArmPoint C.sy C.sz (bulkArmPoint C.sy C.sz C.seed (n - 2)) 2 ∈ _ at hs
    rw [← bulkArmPoint_add] at hs
    have heq : n - 2 + 2 = n := by omega
    have hj : (n - 2) / 2 + 1 + 1 = n / 2 + 1 := by omega
    simpa only [heq, hj] using hs

theorem point_not_previous_solid (n : ℕ) : C.point n ∉ skinSolid m (n / 2) := by
  intro hp
  have h := ((mem_skinSolid m (n / 2) _).mp hp) C.dir
  rcases C.owner.property with hpA | hpB
  · have hf := C.big_point_coordinate hpA n
    dsimp [octRadius] at hf
    push_cast at h
    omega
  · have hf := C.small_point_coordinate hpB n
    push_cast at h
    omega

theorem point_mem_skin (n : ℕ) : C.point n ∈ skin m (n / 2 + 1) := by
  apply Finset.mem_sdiff.mpr
  refine ⟨C.point_mem_own_solid n, ?_⟩
  simpa only [Nat.add_sub_cancel] using C.point_not_previous_solid n

theorem point_mem_skin_iff (n j : ℕ) : C.point n ∈ skin m j ↔ j = n / 2 + 1 := by
  constructor
  · intro hp
    have hown := C.point_mem_skin n
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Finset.disjoint_left.mp (skins_disjoint m j (n / 2 + 1) hlt) hp hown
    · exact Finset.disjoint_left.mp (skins_disjoint m (n / 2 + 1) j hgt) hown hp
  · rintro rfl
    exact C.point_mem_skin n

theorem point_mem_skin_iff_two_indices (n j : ℕ) (hj : 1 ≤ j) :
    C.point n ∈ skin m j ↔ n = 2 * j - 2 ∨ n = 2 * j - 1 := by
  rw [C.point_mem_skin_iff]
  omega

end DanglingColumn
end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.ColumnsArmFacts

/-! The actual infinite dangling columns of Section 8.1, Lemma C. -/

namespace ProteinFolding.Tetrahedral

structure DanglingColumn (m : ℕ) where
  owner : Site
  dir : Fin 4
  owner_mem : owner ∈ octahedron m
  seed_outside : step owner dir ∉ octahedron m

namespace DanglingColumn

variable {m : ℕ} (C : DanglingColumn m)

def seed : Site := step C.owner C.dir
def sy : ℤ := if InASublattice C.owner.val then bigFaceY C.dir else -bigFaceY C.dir
def sz : ℤ := if InASublattice C.owner.val then bigFaceZ C.dir else -bigFaceZ C.dir
def point (n : ℕ) : Site := bulkArmPoint C.sy C.sz C.seed n
def sites : Set Site := Set.range C.point

theorem seed_dangling : IsDangling m C.seed :=
  ⟨C.seed_outside, C.owner, C.owner_mem, step_adj _ _⟩

theorem sy_unit : C.sy = 1 ∨ C.sy = -1 := by
  have h := bigFaceY_unit C.dir
  dsimp [sy]
  split_ifs <;> omega

theorem sz_unit : C.sz = 1 ∨ C.sz = -1 := by
  have h := bigFaceZ_unit C.dir
  dsimp [sz]
  split_ifs <;> omega

theorem seed_quadrant : 1 ≤ C.sy * bulkY m C.seed ∧ 0 ≤ C.sz * bulkZ C.seed := by
  rcases C.owner.property with hpA | hpB
  · rw [sy, sz, if_pos hpA, if_pos hpA]
    exact big_dangling_quadrant m hpA C.owner_mem C.dir C.seed_outside
  · rw [sy, sz, if_neg ((inB_iff_not_inA _).mp hpB), if_neg ((inB_iff_not_inA _).mp hpB)]
    exact small_dangling_quadrant m hpB C.owner_mem C.dir C.seed_outside

theorem point_adj (n : ℕ) : tetrahedralLattice.Adj (C.point n) (C.point (n + 1)) :=
  bulkArmPoint_adj C.sy C.sz C.seed n

theorem point_signed_y (n : ℕ) : 1 + (n : ℤ) ≤ C.sy * bulkY m (C.point n) := by
  have hy := C.seed_quadrant.1
  change 1 ≤ C.sy * bulkY m C.seed at hy
  change _ ≤ C.sy * bulkY m (bulkArmPoint C.sy C.sz C.seed n)
  rw [bulkArmPoint_y m C.sy C.sz C.sy_unit C.sz_unit]
  rcases C.sy_unit with hs | hs
  all_goals simp only [hs] at hy ⊢
  all_goals omega

theorem point_signed_z (n : ℕ) : (n : ℤ) ≤ C.sz * bulkZ (C.point n) := by
  have hz := C.seed_quadrant.2
  change 0 ≤ C.sz * bulkZ C.seed at hz
  change _ ≤ C.sz * bulkZ (bulkArmPoint C.sy C.sz C.seed n)
  rw [bulkArmPoint_z C.sy C.sz C.sy_unit C.sz_unit]
  rcases C.sz_unit with hs | hs
  all_goals simp only [hs] at hz ⊢
  all_goals omega

theorem point_injective : Function.Injective C.point :=
  bulkArmPoint_injective m C.sy C.sz C.sy_unit C.sz_unit C.seed
    (by have h := C.seed_quadrant.1; omega) C.seed_quadrant.2

theorem big_seed_coordinate (hpA : InASublattice C.owner.val) :
    tetraCoordinate m C.seed.val C.dir = octRadius m + 3 := by
  have hf := (step_not_mem_octahedron_A m hpA C.owner_mem C.dir).mp C.seed_outside
  change tetraCoordinate m (step C.owner C.dir).val C.dir = _
  rw [tetraCoordinate_step_A m hpA, if_pos rfl, hf]

theorem small_seed_coordinate (hpB : InBSublattice C.owner.val) :
    tetraCoordinate m C.seed.val C.dir = -(2 * (m : ℤ) - 1) - 3 := by
  have hf := (step_not_mem_octahedron_B m hpB C.owner_mem C.dir).mp C.seed_outside
  change tetraCoordinate m (step C.owner C.dir).val C.dir = _
  rw [tetraCoordinate_step_B m hpB, if_pos rfl, hf]
  omega

theorem big_point_growth (hpA : InASublattice C.owner.val) (n : ℕ) :
    octRadius m + 3 + (n : ℤ) ≤ tetraCoordinate m (C.point n).val C.dir := by
  have h := bigFace_armPoint_growth m C.dir C.seed n
  rw [C.big_seed_coordinate hpA] at h
  change _ ≤ tetraCoordinate m (bulkArmPoint C.sy C.sz C.seed n).val C.dir
  rw [sy, sz, if_pos hpA, if_pos hpA]
  exact h

theorem small_point_growth (hpB : InBSublattice C.owner.val) (n : ℕ) :
    tetraCoordinate m (C.point n).val C.dir ≤ -(2 * (m : ℤ) - 1) - 3 - (n : ℤ) := by
  have h := smallFace_armPoint_growth m C.dir C.seed n
  rw [C.small_seed_coordinate hpB] at h
  change tetraCoordinate m (bulkArmPoint C.sy C.sz C.seed n).val C.dir ≤ _
  rw [sy, sz, if_neg ((inB_iff_not_inA _).mp hpB), if_neg ((inB_iff_not_inA _).mp hpB)]
  exact h

/-- Every site of the infinite column stays outside the original octahedron. -/
theorem point_outside (n : ℕ) : C.point n ∉ octahedron m := by
  intro hp
  have h := (mem_octahedron m _).mp hp C.dir
  rcases C.owner.property with hpA | hpB
  · have hg := C.big_point_growth hpA n
    omega
  · have hg := C.small_point_growth hpB n
    omega

/-- Its starting point is the only dangling site on a column. -/
theorem point_dangling_iff_zero (n : ℕ) : IsDangling m (C.point n) ↔ n = 0 := by
  constructor
  · intro hp
    have h := dangling_tetraCoordinate_bounds m hp C.dir
    rcases C.owner.property with hpA | hpB
    · have hg := C.big_point_growth hpA n
      omega
    · have hg := C.small_point_growth hpB n
      omega
  · rintro rfl
    exact C.seed_dangling

end DanglingColumn

theorem dangling_has_column (m : ℕ) {p : Site} (hp : IsDangling m p) :
    ∃ C : DanglingColumn m, C.seed = p := by
  obtain ⟨hpout, v, hv, hadj⟩ := hp
  obtain ⟨d, hd⟩ := (adj_iff_exists_step v p).mp hadj
  exact ⟨⟨v, d, hv, by rw [hd]; exact hpout⟩, hd⟩

end ProteinFolding.Tetrahedral

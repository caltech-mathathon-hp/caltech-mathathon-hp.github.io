import ProteinFolding.Tetrahedral.FarFieldWires
import ProteinFolding.Tetrahedral.ColumnsSkins
import ProteinFolding.Tetrahedral.BulkRungs

namespace ProteinFolding.Tetrahedral.FarField

def quadrantSignY (q : Quadrant) : ℤ := if q.1 then -1 else 1
def quadrantSignZ (q : Quadrant) : ℤ := if q.2 then -1 else 1

theorem quadrantSignY_unit (q : Quadrant) : quadrantSignY q = 1 ∨ quadrantSignY q = -1 := by
  unfold quadrantSignY
  split <;> simp

theorem quadrantSignZ_unit (q : Quadrant) : quadrantSignZ q = 1 ∨ quadrantSignZ q = -1 := by
  unfold quadrantSignZ
  split <;> simp

theorem quadrantArm_bulk_next (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) (t : ℤ) :
    quadrantArm R hR q p (t + 1) =
      bulkArmNext (quadrantSignY q) (quadrantSignZ q) (quadrantArm R hR q p t) := by
  have hc := bulkArmNext_coordinates (quadrantSignY q) (quadrantSignZ q)
    (quadrantSignY_unit q) (quadrantSignZ_unit q) (quadrantArm R hR q p t)
  apply adjacent_yz_ext (quadrantArm_adj R hR q p t) (bulkArmNext_adj _ _ _)
  · rw [hc.1]
    rcases q with ⟨a, b⟩
    cases a <;> cases b <;>
      simp [quadrantSignY, quadrantArm, quadrantMap, arm, armCoordinates,
        flipY, flipYCoordinates, flipZ, flipZCoordinates] <;> omega
  · rw [hc.2.1]
    rcases q with ⟨a, b⟩
    cases a <;> cases b <;>
      simp [quadrantSignZ, quadrantArm, quadrantMap, arm, armCoordinates,
        flipY, flipYCoordinates, flipZ, flipZCoordinates] <;> omega

theorem quadrantArm_bulkPoint (R : ℤ) (hR : R % 2 = 0) (q : Quadrant) (p : Site) (n : ℕ) :
    quadrantArm R hR q (quadrantUnmap R hR q p) n =
      bulkArmPoint (quadrantSignY q) (quadrantSignZ q) p n := by
  induction n with
  | zero => simp only [Nat.cast_zero, quadrantArm, arm_zero, quadrantMap_unmap, bulkArmPoint_zero]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, quadrantArm_bulk_next, ih]
    rfl

namespace Column

variable {m : ℕ} (C : DanglingColumn m)

def quadrant : Quadrant := ⟨decide (C.sy = -1), decide (C.sz = -1)⟩

theorem signY : quadrantSignY (quadrant C) = C.sy := by
  rcases C.sy_unit with hs | hs <;> simp [quadrant, quadrantSignY, hs]

theorem signZ : quadrantSignZ (quadrant C) = C.sz := by
  rcases C.sz_unit with hs | hs <;> simp [quadrant, quadrantSignZ, hs]

theorem radius_even : octRadius m % 2 = 0 := by unfold octRadius; omega

theorem point_one_quadrant : InQuadrant (octRadius m) (quadrant C) (C.point 1) := by
  have hy := C.point_signed_y 1
  have hz := C.point_signed_z 1
  change (1 : ℤ) + 1 ≤ C.sy * Y (octRadius m) (C.point 1) at hy
  change (1 : ℤ) ≤ C.sz * Z (C.point 1) at hz
  rcases C.sy_unit with hs | hs <;> rcases C.sz_unit with ht | ht
  all_goals simp only [hs, ht, one_mul, neg_one_mul, Nat.cast_one] at hy hz
  all_goals simp [InQuadrant, quadrant, hs, ht] <;> omega

def base : Site := quadrantUnmap (octRadius m) radius_even (quadrant C) (C.point 1)

theorem base_positive : PositiveQuadrant (octRadius m) (base C) := by
  apply (quadrantMap_positive_iff (octRadius m) radius_even (quadrant C) (base C)).1
  simpa only [base, quadrantMap_unmap] using (point_one_quadrant C)

theorem arm_eq_point (n : ℕ) :
    quadrantArm (octRadius m) radius_even (quadrant C) (base C) n = C.point (1 + n) := by
  have h := quadrantArm_bulkPoint (octRadius m) radius_even (quadrant C) (C.point 1) n
  rw [(signY C), (signZ C)] at h
  change quadrantArm (octRadius m) radius_even (quadrant C) (base C) n = _ at h
  rw [h]
  exact (bulkArmPoint_add C.sy C.sz C.seed 1 n).symm

theorem arm_eq_point_int (t : ℤ) (ht : 0 ≤ t) :
    quadrantArm (octRadius m) radius_even (quadrant C) (base C) t = C.point (1 + t.toNat) := by
  have h := (arm_eq_point C) t.toNat
  simpa only [Int.toNat_of_nonneg ht] using h

theorem base_rho_bound : rho (octRadius m) (base C) ≤ 2 * m + 4 := by
  have h := skinSolid_rho_bound m 1 C.point_one_mem_solid_one
  rw [base, quadrantUnmap_rho]
  change rho (octRadius m) (C.point 1) ≤ _
  change rho (octRadius m) (C.point 1) ≤ 2 * ((m + 2 * 1 : ℕ) : ℤ) at h
  push_cast at h
  omega

theorem base_alpha_bound : |alpha (octRadius m) (base C)| ≤ 2 * m + 4 := by
  have hy := abs_nonneg (Y (octRadius m) (base C))
  have hz := abs_nonneg (Z (base C))
  have h := (base_rho_bound C)
  unfold rho alpha at *
  rw [abs_le]
  omega

theorem base_x_bounds : -(2 * (m : ℤ) + 4) ≤ quadrantArmBaseX (quadrant C) (base C) ∧
    quadrantArmBaseX (quadrant C) (base C) ≤ 2 * m + 3 := by
  have h := inSkinSolid_l1_bound m 1 ((mem_skinSolid m 1 _).1 C.point_one_mem_solid_one)
  have hx := le_abs_self ((C.point 1).val 0)
  have hx' := neg_le_abs ((C.point 1).val 0)
  have hy := abs_nonneg ((C.point 1).val 1 - octRadius m)
  have hz := abs_nonneg ((C.point 1).val 2)
  have hb := quadrantArm_x_band (octRadius m) radius_even (quadrant C) (base C) 0
  have heq := (arm_eq_point C) 0
  simp only [Nat.cast_zero, Nat.add_zero] at heq
  rw [heq] at hb
  dsimp only [X] at hb
  push_cast at h
  omega

end Column

end ProteinFolding.Tetrahedral.FarField

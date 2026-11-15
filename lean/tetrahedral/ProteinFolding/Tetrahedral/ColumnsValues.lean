import ProteinFolding.Tetrahedral.Columns

/-! Exact alternating face depths along the columns, Lemma C(ii). -/

namespace ProteinFolding.Tetrahedral

theorem bigFace_armPoint_coordinate (m : ℕ) (d : Fin 4) (p : Site) (n : ℕ) :
    tetraCoordinate m (bulkArmPoint (bigFaceY d) (bigFaceZ d) p n).val d =
      tetraCoordinate m p.val d + 2 * (n : ℤ) +
        siteCharge (bulkArmPoint (bigFaceY d) (bigFaceZ d) p n) - siteCharge p := by
  have hx := bulkArmPoint_x_charge (bigFaceY d) (bigFaceZ d)
    (bigFaceY_unit d) (bigFaceZ_unit d) p n
  have hy := bulkArmPoint_y m (bigFaceY d) (bigFaceZ d)
    (bigFaceY_unit d) (bigFaceZ_unit d) p n
  have hz := bulkArmPoint_z (bigFaceY d) (bigFaceZ d)
    (bigFaceY_unit d) (bigFaceZ_unit d) p n
  dsimp [bulkY, bulkZ] at hy hz
  fin_cases d <;> dsimp [bigFaceY, bigFaceZ, bondComponent, tetraCoordinate] at hx hy hz ⊢
  all_goals omega

theorem smallFace_armPoint_coordinate (m : ℕ) (d : Fin 4) (p : Site) (n : ℕ) :
    tetraCoordinate m (bulkArmPoint (-bigFaceY d) (-bigFaceZ d) p n).val d =
      tetraCoordinate m p.val d - 2 * (n : ℤ) +
        siteCharge (bulkArmPoint (-bigFaceY d) (-bigFaceZ d) p n) - siteCharge p := by
  have hsy : -bigFaceY d = 1 ∨ -bigFaceY d = -1 := by have h := bigFaceY_unit d; omega
  have hsz : -bigFaceZ d = 1 ∨ -bigFaceZ d = -1 := by have h := bigFaceZ_unit d; omega
  have hx := bulkArmPoint_x_charge (-bigFaceY d) (-bigFaceZ d) hsy hsz p n
  have hy := bulkArmPoint_y m (-bigFaceY d) (-bigFaceZ d) hsy hsz p n
  have hz := bulkArmPoint_z (-bigFaceY d) (-bigFaceZ d) hsy hsz p n
  dsimp [bulkY, bulkZ] at hy hz
  fin_cases d <;> dsimp [bigFaceY, bigFaceZ, bondComponent, tetraCoordinate] at hx hy hz ⊢
  all_goals omega

namespace DanglingColumn

variable {m : ℕ} (C : DanglingColumn m)

theorem big_point_coordinate (hpA : InASublattice C.owner.val) (n : ℕ) :
    tetraCoordinate m (C.point n).val C.dir =
      octRadius m + 3 + 2 * (n : ℤ) - (n % 2 : ℕ) := by
  have hf := bigFace_armPoint_coordinate m C.dir C.seed n
  have hc := bulkArmPoint_charge (bigFaceY C.dir) (bigFaceZ C.dir) C.seed n
  have hs : siteCharge C.seed = 1 := siteCharge_B (step_in_B hpA C.dir)
  rw [C.big_seed_coordinate hpA, hs] at hf
  rw [hs] at hc
  change tetraCoordinate m (bulkArmPoint C.sy C.sz C.seed n).val C.dir = _
  rw [sy, sz, if_pos hpA, if_pos hpA]
  split_ifs at hc <;> omega

theorem small_point_coordinate (hpB : InBSublattice C.owner.val) (n : ℕ) :
    tetraCoordinate m (C.point n).val C.dir =
      -(2 * (m : ℤ) - 1) - 3 - 2 * (n : ℤ) + (n % 2 : ℕ) := by
  have hf := smallFace_armPoint_coordinate m C.dir C.seed n
  have hc := bulkArmPoint_charge (-bigFaceY C.dir) (-bigFaceZ C.dir) C.seed n
  have hs : siteCharge C.seed = 0 := siteCharge_A (step_in_A hpB C.dir)
  rw [C.small_seed_coordinate hpB, hs] at hf
  rw [hs] at hc
  change tetraCoordinate m (bulkArmPoint C.sy C.sz C.seed n).val C.dir = _
  rw [sy, sz, if_neg ((inB_iff_not_inA _).mp hpB), if_neg ((inB_iff_not_inA _).mp hpB)]
  split_ifs at hc <;> omega

end DanglingColumn
end ProteinFolding.Tetrahedral

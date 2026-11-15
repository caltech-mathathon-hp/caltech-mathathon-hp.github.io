import ProteinFolding.Tetrahedral.ColumnsSkins
import ProteinFolding.Tetrahedral.FaceRowsGeometry

/-! The exact two sites of every F' column in each skin, Lemma R(b). -/

namespace ProteinFolding.Tetrahedral

def faceDanglingColumn (m a b c : ℕ) (hs : a + b + c + 2 = m) : DanglingColumn m where
  owner := faceSurfaceSite m 0 a b c hs
  dir := 3
  owner_mem := by
    rw [← skinSolid_zero m]
    exact faceSurface_mem_skinSolid m 0 a b c hs
  seed_outside := by
    have hpB := faceSurfaceCoordinates_inB m 0 a b c hs
    apply (step_not_mem_octahedron_B m hpB _ 3).mpr
    · have h := tetraCoordinate_faceSurface m 0 a b c hs 3
      dsimp at h
      exact h
    · rw [← skinSolid_zero m]
      exact faceSurface_mem_skinSolid m 0 a b c hs

theorem faceDanglingColumn_sy (m a b c : ℕ) (hs : a + b + c + 2 = m) :
    (faceDanglingColumn m a b c hs).sy = 1 := by
  have hpB := faceSurfaceCoordinates_inB m 0 a b c hs
  change (if InASublattice (faceSurfaceSite m 0 a b c hs).val then bigFaceY 3 else -bigFaceY 3) = 1
  rw [if_neg ((inB_iff_not_inA _).mp hpB)]
  rfl

theorem faceDanglingColumn_sz (m a b c : ℕ) (hs : a + b + c + 2 = m) :
    (faceDanglingColumn m a b c hs).sz = -1 := by
  have hpB := faceSurfaceCoordinates_inB m 0 a b c hs
  change (if InASublattice (faceSurfaceSite m 0 a b c hs).val then bigFaceZ 3 else -bigFaceZ 3) = -1
  rw [if_neg ((inB_iff_not_inA _).mp hpB)]
  rfl

theorem faceDanglingColumn_seed (m a b c : ℕ) (hs : a + b + c + 2 = m) :
    (faceDanglingColumn m a b c hs).seed =
      faceSubSite m 1 (a + 1) (b + 1) (c + 1) (by omega) := by
  change step (faceSurfaceSite m 0 a b c hs) 3 = _
  apply Subtype.ext
  rw [step_val_of_B _ (faceSurfaceCoordinates_inB m 0 a b c hs)]
  funext k
  rw [bondVector_eq_bondComponent]
  fin_cases k <;> dsimp [faceSurfaceSite, faceSurfaceCoordinates, faceSubSite,
    faceSubCoordinates, bondComponent] <;> omega

theorem faceDanglingColumn_point_coordinates (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (n : ℕ) (k : Fin 3) : ((faceDanglingColumn m a b c hs).point n).val k =
      if k = 0 then 2 * (c : ℤ) + 2 - (n % 2 : ℕ)
      else if k = 1 then octRadius m + 2 * (b : ℤ) + 2 + n
      else -2 * (a : ℤ) - 2 - n := by
  let C := faceDanglingColumn m a b c hs
  have hsy : C.sy = 1 := faceDanglingColumn_sy m a b c hs
  have hsz : C.sz = -1 := faceDanglingColumn_sz m a b c hs
  have hx := bulkArmPoint_x_charge C.sy C.sz C.sy_unit C.sz_unit C.seed n
  have hy := bulkArmPoint_y m C.sy C.sz C.sy_unit C.sz_unit C.seed n
  have hz := bulkArmPoint_z C.sy C.sz C.sy_unit C.sz_unit C.seed n
  have hsA : InASublattice C.seed.val := step_in_A (faceSurfaceCoordinates_inB m 0 a b c hs) 3
  have hc0 := siteCharge_A hsA
  have hcn := bulkArmPoint_charge C.sy C.sz C.seed n
  change siteCharge (C.point n) = (if n % 2 = 0 then siteCharge C.seed else 1 - siteCharge C.seed) at hcn
  rw [hc0] at hcn
  have hc : siteCharge (C.point n) = (n % 2 : ℕ) := by split_ifs at hcn <;> omega
  change (C.point n).val 0 = C.seed.val 0 +
    (siteCharge (C.point n) - siteCharge C.seed) * (C.sy * C.sz) at hx
  change (C.point n).val 1 - octRadius m = C.seed.val 1 - octRadius m + (n : ℤ) * C.sy at hy
  change (C.point n).val 2 - 1 = C.seed.val 2 - 1 + (n : ℤ) * C.sz at hz
  rw [hsy, hsz, hc0, hc] at hx
  rw [hsy] at hy
  rw [hsz] at hz
  have hseed : C.seed = faceSubSite m 1 (a + 1) (b + 1) (c + 1) (by omega) :=
    faceDanglingColumn_seed m a b c hs
  have hsx : C.seed.val 0 = 2 * (c : ℤ) + 2 := by
    rw [hseed]
    dsimp [faceSubSite, faceSubCoordinates]
    omega
  have hsy' : C.seed.val 1 = octRadius m + 2 * (b : ℤ) + 2 := by
    rw [hseed]
    dsimp [faceSubSite, faceSubCoordinates]
    omega
  have hsz' : C.seed.val 2 = -2 * (a : ℤ) - 2 := by
    rw [hseed]
    dsimp [faceSubSite, faceSubCoordinates]
    omega
  change (C.point n).val k = _
  fin_cases k <;> dsimp <;> omega

theorem faceDanglingColumn_sub_in_skin (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (j : ℕ) (hj : 1 ≤ j) : (faceDanglingColumn m a b c hs).point (2 * j - 2) =
      faceSubSite m j (a + j) (b + j) (c + 1) (by omega) := by
  apply Subtype.ext
  funext k
  rw [faceDanglingColumn_point_coordinates]
  fin_cases k <;> dsimp [faceSubSite, faceSubCoordinates] <;> omega

theorem faceDanglingColumn_surface_in_skin (m a b c : ℕ) (hs : a + b + c + 2 = m)
    (j : ℕ) (hj : 1 ≤ j) : (faceDanglingColumn m a b c hs).point (2 * j - 1) =
      faceSurfaceSite m j (a + j) (b + j) c (by omega) := by
  apply Subtype.ext
  funext k
  rw [faceDanglingColumn_point_coordinates]
  fin_cases k <;> dsimp [faceSurfaceSite, faceSurfaceCoordinates] <;> omega

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.FaceRowsColumns
import ProteinFolding.Tetrahedral.FaceCoordinateSurjectivity

/-! No column over another face meets the F' bilayers. -/

namespace ProteinFolding.Tetrahedral

theorem DanglingColumn.ext_owner_dir {m : ℕ} {C D : DanglingColumn m}
    (howner : C.owner = D.owner) (hdir : C.dir = D.dir) : C = D := by
  cases C
  cases D
  cases howner
  cases hdir
  rfl

theorem bigFace_direction_two (d : Fin 4) :
    bigFaceY d = 1 → bigFaceZ d = -1 → d = 2 := by revert d; decide

theorem smallFace_direction_three (d : Fin 4) :
    -bigFaceY d = 1 → -bigFaceZ d = -1 → d = 3 := by revert d; decide

theorem column_face_quadrant {m : ℕ} (C : DanglingColumn m) (n : ℕ)
    (hy : 1 ≤ bulkY m (C.point n)) (hz : bulkZ (C.point n) ≤ -2) :
    C.sy = 1 ∧ C.sz = -1 := by
  have hcy := C.point_signed_y n
  have hcz := C.point_signed_z n
  constructor
  · rcases C.sy_unit with h | h
    · exact h
    · rw [h] at hcy
      omega
  · rcases C.sz_unit with h | h
    · rw [h] at hcz
      omega
    · exact h

theorem column_big_owner_dir {m : ℕ} (C : DanglingColumn m)
    (hpA : InASublattice C.owner.val) (hsy : C.sy = 1) (hsz : C.sz = -1) : C.dir = 2 := by
  rw [DanglingColumn.sy, if_pos hpA] at hsy
  rw [DanglingColumn.sz, if_pos hpA] at hsz
  exact bigFace_direction_two C.dir hsy hsz

theorem column_small_owner_dir {m : ℕ} (C : DanglingColumn m)
    (hpB : InBSublattice C.owner.val) (hsy : C.sy = 1) (hsz : C.sz = -1) : C.dir = 3 := by
  rw [DanglingColumn.sy, if_neg ((inB_iff_not_inA _).mp hpB)] at hsy
  rw [DanglingColumn.sz, if_neg ((inB_iff_not_inA _).mp hpB)] at hsz
  exact smallFace_direction_three C.dir hsy hsz

theorem column_surface_owner {m j a b c n : ℕ} (C : DanglingColumn m)
    (hj : 1 ≤ j) (hs : a + b + c + 2 = m + 2 * j)
    (heq : C.point n = faceSurfaceSite m j a b c hs) :
    InBSublattice C.owner.val ∧ C.dir = 3 := by
  have hq := faceSurface_quadrant m j a b c hs
  rw [← heq] at hq
  obtain ⟨hsy, hsz⟩ := column_face_quadrant C n hq.1 hq.2
  have hskin : C.point n ∈ skin m j := by rw [heq]; exact faceSurface_mem_skin m j a b c hj hs
  have hrank := (C.point_mem_skin_iff n j).mp hskin
  rcases C.owner.property with hpA | hpB
  · have hd := column_big_owner_dir C hpA hsy hsz
    have hf2 := C.big_point_coordinate hpA n
    rw [hd] at hf2
    have hsurface2 : tetraCoordinate m (C.point n).val 2 =
        2 * ((m + 2 * j : ℕ) : ℤ) - 3 - 4 * c := by
      rw [heq]
      exact tetraCoordinate_faceSurface m j a b c hs 2
    have hmod : n % 2 = 0 := by
      dsimp [octRadius] at hf2
      push_cast at hsurface2
      omega
    have hpoint : C.point n = bulkArmPoint 1 (-1) C.seed n := by
      change bulkArmPoint C.sy C.sz C.seed n = _
      rw [hsy, hsz]
    have hpair := smallFace_armPoint_coordinate m 3 C.seed n
    change tetraCoordinate m (bulkArmPoint 1 (-1) C.seed n).val 3 =
      tetraCoordinate m C.seed.val 3 - 2 * (n : ℤ) +
        siteCharge (bulkArmPoint 1 (-1) C.seed n) - siteCharge C.seed at hpair
    rw [← hpoint] at hpair
    have hcseed : siteCharge C.seed = 1 := siteCharge_B (step_in_B hpA C.dir)
    have hcpoint : siteCharge (C.point n) = 1 := by
      rw [heq]
      exact siteCharge_B (faceSurfaceCoordinates_inB m j a b c hs)
    rw [hcseed, hcpoint] at hpair
    have hseed : tetraCoordinate m C.seed.val 3 = tetraCoordinate m C.owner.val 3 - 1 := by
      change tetraCoordinate m (step C.owner C.dir).val 3 = _
      rw [hd, tetraCoordinate_step_A m hpA, if_neg (by decide : (3 : Fin 4) ≠ 2)]
      omega
    have howner := ((inOctahedron_iff_A m hpA).mp ((mem_octahedron m _).mp C.owner_mem) 3).1
    have hface : tetraCoordinate m (C.point n).val 3 = -(2 * ((m + 2 * j : ℕ) : ℤ) - 1) := by
      rw [heq]
      exact tetraCoordinate_faceSurface m j a b c hs 3
    dsimp [octRadius] at howner
    push_cast at hface
    omega
  · exact ⟨hpB, column_small_owner_dir C hpB hsy hsz⟩

theorem column_sub_owner {m j a b c n : ℕ} (C : DanglingColumn m)
    (hj : 1 ≤ j) (hs : a + b + c + 1 = m + 2 * j)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (heq : C.point n = faceSubSite m j a b c hs) :
    InBSublattice C.owner.val ∧ C.dir = 3 := by
  have hq := faceSub_quadrant m j a b c hs ha hb
  rw [← heq] at hq
  obtain ⟨hsy, hsz⟩ := column_face_quadrant C n (by have h := hq.1; omega) (by have h := hq.2; omega)
  have hskin : C.point n ∈ skin m j := by rw [heq]; exact faceSub_mem_skin m j a b c hj hs ha hb hc
  have hrank := (C.point_mem_skin_iff n j).mp hskin
  rcases C.owner.property with hpA | hpB
  · have hd := column_big_owner_dir C hpA hsy hsz
    have hf2 := C.big_point_coordinate hpA n
    rw [hd] at hf2
    have hsub2 : tetraCoordinate m (C.point n).val 2 =
        2 * ((m + 2 * j : ℕ) : ℤ) - 2 - 4 * c := by
      rw [heq]
      exact tetraCoordinate_faceSub m j a b c hs 2
    dsimp [octRadius] at hf2
    push_cast at hsub2
    omega
  · exact ⟨hpB, column_small_owner_dir C hpB hsy hsz⟩

theorem column_over_face_coordinates {m : ℕ} (C : DanglingColumn m)
    (hpB : InBSublattice C.owner.val) (hdir : C.dir = 3) :
    ∃ a b c : ℕ, ∃ hs : a + b + c + 2 = m, C = faceDanglingColumn m a b c hs := by
  have hface := (step_not_mem_octahedron_B m hpB C.owner_mem C.dir).mp C.seed_outside
  rw [hdir] at hface
  obtain ⟨a, b, c, hs, heq⟩ := smallFace_owner_coordinates m hpB C.owner_mem hface
  exact ⟨a, b, c, hs, DanglingColumn.ext_owner_dir heq hdir⟩

end ProteinFolding.Tetrahedral

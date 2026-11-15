import ProteinFolding.Tetrahedral.FaceRowsAvoidance

namespace ProteinFolding.Tetrahedral

example {m : ℕ} {C D : DanglingColumn m} (hne : C.seed ≠ D.seed) (n r : ℕ) :
    C.point n ≠ D.point r := DanglingColumn.points_ne_of_seed_ne hne n r

example (m a b c : ℕ) (hs : a + b + c + 2 = m) :
    (faceDanglingColumn m a b c hs).point 2 =
      faceSubSite m 2 (a + 2) (b + 2) (c + 1) (by omega) :=
  faceDanglingColumn_sub_in_skin m a b c hs 2 (by decide)

example (m j a c : ℕ) (hs : a + (j - 1) + c + 2 = m + 2 * j)
    (hj : 2 ≤ j) (r : ℕ) (hr : r ≤ 2 * a) :
    ¬ OnDanglingColumn m (faceRowPoint 1 m j a (j - 1) c hs r) :=
  faceRowB_avoids_columns m j a (j - 1) c hs (by omega) (by omega) (by omega) r hr

#print axioms big_dangling_quadrant
#print axioms small_dangling_quadrant
#print axioms dangling_has_column
#print axioms DanglingColumn.point_outside
#print axioms DanglingColumn.point_dangling_iff_zero
#print axioms DanglingColumn.sites_disjoint_of_seed_ne
#print axioms DanglingColumn.big_point_coordinate
#print axioms DanglingColumn.small_point_coordinate
#print axioms DanglingColumn.point_mem_skin_iff_two_indices
#print axioms faceSub_step_zero
#print axioms faceSub_step_one
#print axioms faceSub_step_two
#print axioms faceSub_step_three_mem_previousSolid
#print axioms faceRowPoint_step
#print axioms faceRowPoint_injective
#print axioms faceRowSegment_nodup
#print axioms faceRowSegment_isChain
#print axioms faceDanglingColumn_sub_in_skin
#print axioms faceDanglingColumn_surface_in_skin
#print axioms column_surface_owner
#print axioms column_sub_owner
#print axioms faceSurface_column_coordinates
#print axioms faceSub_column_coordinates
#print axioms faceRowA_avoids_columns
#print axioms faceRowB_avoids_columns
#print axioms faceRowC_one_column_owners

end ProteinFolding.Tetrahedral

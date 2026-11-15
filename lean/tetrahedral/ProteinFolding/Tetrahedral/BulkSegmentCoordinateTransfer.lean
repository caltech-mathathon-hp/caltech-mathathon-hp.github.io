import ProteinFolding.Tetrahedral.BulkSegmentValueTransfer

/-! Coordinate statistics of complete finite segment certificates translate by
the vertex displacement. These formulas also cover the two x vertices. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkSegment_vertex_xValues_shift (m n : ℕ) (v : Fin 6) (D : ℕ)
    (A : Finset Site) (p : BulkVertex m) (q : BulkVertex n) (rank : Site → ℕ)
    (hm : D + 7 ≤ m) (hn : D + 7 ≤ n)
    (hbox : ∀ r ∈ A, InBulkVertexBox m v D r)
    (h : BulkSegmentFiniteCheck m A p.val rank)
    (hq : q.val = bulkReanchorSite m n v p.val) :
    bulkSegmentXValues n q = (bulkSegmentXValues m p).image
      (fun x => x + ((bulkPatchVertex n v).val 0 - (bulkPatchVertex m v).val 0)) := by
  rw [bulkSegment_projected_xValues n q _
      (bulkSegment_vertex_projected m n v D A p q rank hm hn hbox h hq),
    bulkSegmentFiniteCheck_xValues m p A rank h, Finset.image_image, Finset.image_image]
  congr 1
  funext r
  change (bulkReanchorSite m n v r).val 0 =
    r.val 0 + ((bulkPatchVertex n v).val 0 - (bulkPatchVertex m v).val 0)
  rw [bulkReanchorSite_coordinates]
  omega

theorem bulkSegment_vertex_xhat_shift (m n : ℕ) (v : Fin 6) (D : ℕ)
    (A : Finset Site) (p : BulkVertex m) (q : BulkVertex n) (rank : Site → ℕ)
    (hm : D + 7 ≤ m) (hn : D + 7 ≤ n)
    (hbox : ∀ r ∈ A, InBulkVertexBox m v D r)
    (h : BulkSegmentFiniteCheck m A p.val rank)
    (hq : q.val = bulkReanchorSite m n v p.val) :
    bulkSegmentXhat n q = bulkSegmentXhat m p +
      2 * ((bulkPatchVertex n v).val 0 - (bulkPatchVertex m v).val 0) := by
  have hmono : Monotone (fun x : ℤ => x +
      ((bulkPatchVertex n v).val 0 - (bulkPatchVertex m v).val 0)) := by
    intro x y hxy
    change x + ((bulkPatchVertex n v).val 0 - (bulkPatchVertex m v).val 0) ≤
      y + ((bulkPatchVertex n v).val 0 - (bulkPatchVertex m v).val 0)
    omega
  unfold bulkSegmentXhat
  simp only [bulkSegment_vertex_xValues_shift m n v D A p q rank hm hn hbox h hq,
    Finset.min'_image hmono, Finset.max'_image hmono]
  ring

theorem bulk_y_vertex_alpha_positive (m : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hv : v = 1 ∨ v = 4) (hp : InBulkVertexBox m v D p) :
    0 < bulkAlpha m p := by
  have hy := abs_le.mp (hp 1)
  have hz := abs_le.mp (hp 2)
  have hzabs : |bulkZ p| ≤ (D : ℤ) + 1 := by
    rcases hv with rfl | rfl <;>
      dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre] at hz <;>
      apply abs_le.mpr <;> dsimp [bulkZ] <;> omega
  rcases hv with rfl | rfl
  · dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre, octRadius] at hy
    have hY : bulkY m p ≤ 0 := by dsimp [bulkY, octRadius]; omega
    dsimp [bulkAlpha]
    rw [abs_of_nonpos hY]
    dsimp [bulkY, octRadius] at *
    omega
  · dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre, octRadius] at hy
    have hY : 0 ≤ bulkY m p := by dsimp [bulkY, octRadius]; omega
    dsimp [bulkAlpha]
    rw [abs_of_nonneg hY]
    dsimp [bulkY, octRadius] at *
    omega

theorem bulk_z_vertex_alpha_negative (m : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hm : D + 2 ≤ m) (hv : v = 2 ∨ v = 3) (hp : InBulkVertexBox m v D p) :
    bulkAlpha m p < 0 := by
  have hy := abs_le.mp (hp 1)
  have hz := abs_le.mp (hp 2)
  have hyabs : |bulkY m p| ≤ (D : ℤ) := by
    rcases hv with rfl | rfl <;>
      dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre] at hy <;>
      apply abs_le.mpr <;> dsimp [bulkY] <;> omega
  rcases hv with rfl | rfl
  · dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre, octRadius] at hz
    have hZ : bulkZ p ≤ 0 := by dsimp [bulkZ]; omega
    dsimp [bulkAlpha]
    rw [abs_of_nonpos hZ]
    dsimp [bulkZ, octRadius] at *
    omega
  · dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre, octRadius] at hz
    have hZ : 0 ≤ bulkZ p := by dsimp [bulkZ]; omega
    dsimp [bulkAlpha]
    rw [abs_of_nonneg hZ]
    dsimp [bulkZ, octRadius] at *
    omega

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkEdgeSigns
import ProteinFolding.Tetrahedral.BulkPatchSupport

/-! A sufficiently far edge box meets none of the six frozen vertex patches. -/

namespace ProteinFolding.Tetrahedral

theorem bulkVertexBox_face_bound (m : ℕ) (v : Fin 6) (D : ℕ) (p : Site)
    (hp : InBulkVertexBox m v D p) (i : Fin 4) :
    |tetraCoordinate m p.val i - tetraCoordinate m (bulkPatchVertex m v).val i| ≤ 3 * (D : ℤ) := by
  have hx := abs_le.mp (hp 0)
  have hy := abs_le.mp (hp 1)
  have hz := abs_le.mp (hp 2)
  apply abs_le.mpr
  fin_cases i <;> dsimp [tetraCoordinate] <;> constructor <;> omega

theorem bulkPatchVertex_face_cases (m : ℕ) (v : Fin 6) (i : Fin 4) :
    tetraCoordinate m (bulkPatchVertex m v).val i = octRadius m ∨
      tetraCoordinate m (bulkPatchVertex m v).val i = -octRadius m := by
  fin_cases v <;> fin_cases i
  all_goals dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre, tetraCoordinate]
  all_goals omega

theorem bulkFarEdgeBox_not_vertex_box (m : ℕ) (F : OctEdgeFrame) (t D : ℕ) (p : Site)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hp : InBulkEdgeBox m F t D p) (v : Fin 6) :
    ¬InBulkVertexBox m v 8 p := by
  intro hv
  have hm : 1 ≤ m := by omega
  have hAnchor := (bulkEdgeAnchor_faces hm F t).2.2.1
  have hEdge := abs_le.mp (bulkEdgeBox_face_bound m F t D p hp F.a)
  have hVertex := abs_le.mp (bulkVertexBox_face_bound m v 8 p hv F.a)
  have hVertexFace := bulkPatchVertex_face_cases m v F.a
  rw [hAnchor] at hEdge
  dsimp [octRadius] at hEdge hVertexFace
  omega

theorem bulkFarEdgeBox_not_patchSupport (m : ℕ) (F : OctEdgeFrame) (t D : ℕ) (p : Site)
    (ht : D + 8 ≤ t) (htm : t + D + 9 ≤ m) (hp : InBulkEdgeBox m F t D p) :
    p ∉ bulkPatchSupport m := by
  intro hs
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hs
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
  exact bulkFarEdgeBox_not_vertex_box m F t D _ ht htm hp v (bulkPatchOffsetSite_in_box m v r)

end ProteinFolding.Tetrahedral

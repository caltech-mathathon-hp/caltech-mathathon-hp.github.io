import ProteinFolding.Tetrahedral.BulkEdgeMergeTransfer
import ProteinFolding.Tetrahedral.OctahedralTrackGeometry
import ProteinFolding.Tetrahedral.FaceRowsGeometry

/-! Every c=1 F' surface site lies in one uniformly translated far-edge
box or one of two bounded vertex boxes. No finite-size inference is used. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem secondRow_in_edge_box (m a b : ℕ) (hs : a + b + 1 + 2 = m + 2 * 0) :
    InBulkEdgeBox m entryEdgeFrame (b + 1) 3 (faceSurfaceSite m 0 a b 1 hs) := by
  have hm : 1 ≤ m := by omega
  intro k
  change |(faceSurfaceSite m 0 a b 1 hs).val k -
    (octEdgeZigzag m entryEdgeFrame (2 * (b + 1))).val k| ≤ (3 : ℤ)
  rw [entryEdgeZigzag_coordinates hm]
  fin_cases k <;> dsimp [faceSurfaceSite, faceSurfaceCoordinates, entryEdgeCoordinates, octRadius]
  all_goals rw [abs_le]; constructor <;> omega

theorem secondRow_edge_reanchor (m a b : ℕ) (hs : a + b + 1 + 2 = m + 2 * 0) :
    bulkEdgeReanchor m 23 (b + 1) 11 entryEdgeFrame (faceSurfaceSite m 0 a b 1 hs) =
      faceSurfaceSite 23 0 10 10 1 (by decide) := by
  have hm : 1 ≤ m := by omega
  apply Subtype.ext
  funext k
  rw [bulkEdgeReanchor_coordinates]
  simp only [bulkEdgeAnchor]
  rw [entryEdgeZigzag_coordinates hm, entryEdgeZigzag_coordinates (by decide : 1 ≤ 23)]
  fin_cases k <;> dsimp [faceSurfaceSite, faceSurfaceCoordinates, entryEdgeCoordinates, octRadius] <;> omega

theorem secondRow_in_left_box (m a b : ℕ) (hs : a + b + 1 + 2 = m + 2 * 0) (hb : b ≤ 9) :
    InBulkVertexBox m 2 23 (faceSurfaceSite m 0 a b 1 hs) := by
  intro k
  fin_cases k <;> dsimp [faceSurfaceSite, faceSurfaceCoordinates, bulkPatchVertex,
    octVertexSite, octVertexCoordinates, octCentre, octRadius]
  all_goals rw [abs_le]; constructor <;> omega

theorem secondRow_in_right_box (m a b : ℕ) (hs : a + b + 1 + 2 = m + 2 * 0) (ha : a ≤ 9) :
    InBulkVertexBox m 4 23 (faceSurfaceSite m 0 a b 1 hs) := by
  intro k
  fin_cases k <;> dsimp [faceSurfaceSite, faceSurfaceCoordinates, bulkPatchVertex,
    octVertexSite, octVertexCoordinates, octCentre, octRadius]
  all_goals rw [abs_le]; constructor <;> omega

theorem secondRow_left_reanchor (m a b : ℕ) (hs : a + b + 1 + 2 = m + 2 * 0) (hb : b ≤ 9) :
    bulkReanchorSite m 50 2 (faceSurfaceSite m 0 a b 1 hs) =
      faceSurfaceSite 50 0 (47 - b) b 1 (by omega) := by
  apply Subtype.ext
  funext k
  rw [bulkReanchorSite_coordinates]
  fin_cases k <;> dsimp [faceSurfaceSite, faceSurfaceCoordinates, bulkPatchVertex,
    octVertexSite, octVertexCoordinates, octCentre, octRadius] <;> omega

theorem secondRow_right_reanchor (m a b : ℕ) (hs : a + b + 1 + 2 = m + 2 * 0) (ha : a ≤ 9) :
    bulkReanchorSite m 50 4 (faceSurfaceSite m 0 a b 1 hs) =
      faceSurfaceSite 50 0 a (47 - a) 1 (by omega) := by
  apply Subtype.ext
  funext k
  rw [bulkReanchorSite_coordinates]
  fin_cases k <;> dsimp [faceSurfaceSite, faceSurfaceCoordinates, bulkPatchVertex,
    octVertexSite, octVertexCoordinates, octCentre, octRadius] <;> omega

end ProteinFolding.Tetrahedral.NearField

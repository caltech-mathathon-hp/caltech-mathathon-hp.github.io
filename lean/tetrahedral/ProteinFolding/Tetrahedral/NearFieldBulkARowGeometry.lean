import ProteinFolding.Tetrahedral.NearFieldBulkARowCoordinates
import ProteinFolding.Tetrahedral.BulkEdgeMergeTransfer

/-! Uniform bounded-box and translation geometry for the A second row. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem aSecondRow_index_bound (m t : ℕ) (hp : aSecondRowSite m t ∈ bulkInterior m) : t + 1 ≤ m := by
  have hOct := (Finset.mem_sdiff.mp hp).1
  have h := ((mem_octahedron m _).mp hOct) 0
  dsimp [tetraCoordinate, aSecondRowSite, aSecondRowCoordinates, octRadius] at h
  omega

theorem aSecondRow_in_edge_box (m t : ℕ) (hm : 1 ≤ m) :
    InBulkEdgeBox m entryEdgeFrame t 2 (aSecondRowSite m t) := by
  intro k
  change |(aSecondRowSite m t).val k - (octEdgeZigzag m entryEdgeFrame (2 * t)).val k| ≤ (2 : ℤ)
  rw [entryEdgeZigzag_coordinates hm]
  fin_cases k <;> dsimp [aSecondRowSite, aSecondRowCoordinates, entryEdgeCoordinates]
  all_goals rw [abs_le]; constructor <;> omega

theorem aSecondRow_edge_reanchor (m t : ℕ) (hm : 1 ≤ m) :
    bulkEdgeReanchor m 21 t 10 entryEdgeFrame (aSecondRowSite m t) = aSecondRowSite 21 10 := by
  apply Subtype.ext
  funext k
  rw [bulkEdgeReanchor_coordinates]
  simp only [bulkEdgeAnchor]
  rw [entryEdgeZigzag_coordinates hm, entryEdgeZigzag_coordinates (by decide : 1 ≤ 21)]
  fin_cases k <;> dsimp [aSecondRowSite, aSecondRowCoordinates, entryEdgeCoordinates] <;> omega

theorem aSecondRow_in_left_box (m t : ℕ) (ht : t ≤ 9) :
    InBulkVertexBox m 2 23 (aSecondRowSite m t) := by
  intro k
  fin_cases k <;> dsimp [aSecondRowSite, aSecondRowCoordinates, bulkPatchVertex,
    octVertexSite, octVertexCoordinates, octCentre, octRadius]
  all_goals rw [abs_le]; constructor <;> omega

theorem aSecondRow_in_right_box (m t : ℕ) (htm : t + 1 ≤ m) (hr : m - 1 - t ≤ 9) :
    InBulkVertexBox m 4 23 (aSecondRowSite m t) := by
  intro k
  fin_cases k <;> dsimp [aSecondRowSite, aSecondRowCoordinates, bulkPatchVertex,
    octVertexSite, octVertexCoordinates, octCentre, octRadius]
  all_goals rw [abs_le]; constructor <;> omega

theorem aSecondRow_left_reanchor (m t : ℕ) :
    bulkReanchorSite m 50 2 (aSecondRowSite m t) = aSecondRowSite 50 t := by
  apply Subtype.ext
  funext k
  rw [bulkReanchorSite_coordinates]
  fin_cases k <;> dsimp [aSecondRowSite, aSecondRowCoordinates, bulkPatchVertex,
    octVertexSite, octVertexCoordinates, octCentre, octRadius] <;> omega

theorem aSecondRow_right_reanchor (m t : ℕ) (htm : t + 1 ≤ m) (hr : m - 1 - t ≤ 9) :
    bulkReanchorSite m 50 4 (aSecondRowSite m t) = aSecondRowSite 50 (49 - (m - 1 - t)) := by
  apply Subtype.ext
  funext k
  rw [bulkReanchorSite_coordinates]
  fin_cases k <;> dsimp [aSecondRowSite, aSecondRowCoordinates, bulkPatchVertex,
    octVertexSite, octVertexCoordinates, octCentre, octRadius] <;> omega

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.OctahedralTrackGeometry

namespace ProteinFolding.Tetrahedral

example : (octEdgeZigzag 3 entryEdgeFrame 2).val 1 = 6 := by
  rw [entryEdgeZigzag_coordinates (by decide)]
  rfl

example : (octEdgeZigzag 3 exitEdgeFrame 1).val 2 = -1 := by
  rw [exitEdgeZigzag_coordinates (by decide)]
  rfl

example {m : ℕ} (hm : 4 ≤ m) :
    bulkOnDeletedEdge m (octEdgeZigzag m trackEdgeFrame 3) ∧
      3 ≤ (octEdgeZigzag m trackEdgeFrame 3).val 0 ∧
      (octEdgeZigzag m trackEdgeFrame 3).val 2 ≤ -3 := by
  apply (deleted_edge_track_region_iff (by omega : 1 ≤ m) _).mpr
  exact ⟨3, by decide, by omega, rfl⟩

#print axioms entryEdgeZigzag_coordinates
#print axioms exitEdgeZigzag_coordinates
#print axioms trackEdgeZigzag_coordinates
#print axioms deleted_edge_track_region
#print axioms deleted_edge_track_region_iff

end ProteinFolding.Tetrahedral

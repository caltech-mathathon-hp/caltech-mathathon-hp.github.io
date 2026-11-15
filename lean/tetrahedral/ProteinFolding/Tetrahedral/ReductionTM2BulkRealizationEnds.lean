import ProteinFolding.Tetrahedral.ReductionTM2BulkRealization

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

theorem physicalFirst_surface (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) : OctSurfaceSite m (physicalFirst m hm ha j) := by
  rw [physicalFirst_eq]
  let u := (BulkOrientedPath.fold m hm ha (recordComponent m hm ha j)).pos
    (PathOrientation.first (by have h := BulkComponentPath.length_ge_three m hm ha (recordComponent m hm ha j); omega))
  exact bulkCover_degree_one_surface_split m hm u.val u.property
    ((bulkFinite_degree m u).symm.trans (BulkOrientedPath.first_degree m hm ha _))

theorem physicalLast_surface (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (taggedRecords m).length) : OctSurfaceSite m (physicalLast m hm ha j) := by
  rw [physicalLast_eq]
  let u := (BulkOrientedPath.fold m hm ha (recordComponent m hm ha j)).pos
    (PathOrientation.last (by have h := BulkComponentPath.length_ge_three m hm ha (recordComponent m hm ha j); omega))
  exact bulkCover_degree_one_surface_split m hm u.val u.property
    ((bulkFinite_degree m u).symm.trans (BulkOrientedPath.last_degree m hm ha _))

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

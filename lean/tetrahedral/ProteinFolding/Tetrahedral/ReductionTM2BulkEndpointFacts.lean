import ProteinFolding.Tetrahedral.ReductionTM2BulkCappedFamily

/-! Exact degree-one and bulk-membership facts for the actual emitted
endpoints and their chosen columns, ready for the N3 clearance consumers. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

set_option maxHeartbeats 2000000

theorem runtimeFirst_inside (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : runtimeFirst m hm ha j ∈ bulkInterior m :=
  runtimeFold_inside m hm ha j _

theorem runtimeLast_inside (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : runtimeLast m hm ha j ∈ bulkInterior m :=
  runtimeFold_inside m hm ha j _

theorem runtimeFirst_degree (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : (bulkCoverNeighbours m (runtimeFirst m hm ha j)).card = 1 := by
  rw [runtimeFirst_eq, physicalFirst_eq]
  let c := recordComponent m hm ha (outputIndex m j)
  let u : BulkVertex m := (BulkOrientedPath.fold m hm ha c).pos
    (PathOrientation.first (by have h := BulkComponentPath.length_ge_three m hm ha c; omega))
  exact (bulkFinite_degree m u).symm.trans (BulkOrientedPath.first_degree m hm ha c)

theorem runtimeLast_degree (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) : (bulkCoverNeighbours m (runtimeLast m hm ha j)).card = 1 := by
  rw [runtimeLast_eq, physicalLast_eq]
  let c := recordComponent m hm ha (outputIndex m j)
  let u : BulkVertex m := (BulkOrientedPath.fold m hm ha c).pos
    (PathOrientation.last (by have h := BulkComponentPath.length_ge_three m hm ha c; omega))
  exact (bulkFinite_degree m u).symm.trans (BulkOrientedPath.last_degree m hm ha c)

theorem runtimeEndpoint_inside (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (e : Bool) : runtimeEndpoint m hm ha j e ∈ bulkInterior m := by
  cases e
  · exact runtimeFirst_inside m hm ha j
  · exact runtimeLast_inside m hm ha j

theorem runtimeEndpoint_degree (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (e : Bool) : (bulkCoverNeighbours m (runtimeEndpoint m hm ha j e)).card = 1 := by
  cases e
  · exact runtimeFirst_degree m hm ha j
  · exact runtimeLast_degree m hm ha j

theorem runtimeColumn_data (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (e : Bool) (C : DanglingColumn m)
    (hC : C.owner = runtimeEndpoint m hm ha j e) :
    C.owner ∈ bulkInterior m ∧ (bulkCoverNeighbours m C.owner).card = 1 := by
  rw [hC]
  exact ⟨runtimeEndpoint_inside m hm ha j e, runtimeEndpoint_degree m hm ha j e⟩

theorem runtimeColumns_data (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (lengths m).length) (e : Bool) :
    (runtimeColumns m hm ha j e).owner ∈ bulkInterior m ∧
      (bulkCoverNeighbours m (runtimeColumns m hm ha j e).owner).card = 1 :=
  runtimeColumn_data m hm ha j e _ (runtimeColumns_owner m hm ha j e)

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

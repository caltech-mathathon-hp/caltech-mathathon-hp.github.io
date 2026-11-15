import ProteinFolding.Tetrahedral.NearFieldBulkARow
import ProteinFolding.Tetrahedral.NearFieldBulkColumnSeparation
import ProteinFolding.Tetrahedral.NearFieldFrameCaps

/-! The borrowed frame linker columns are free of bulk endpoint columns.
The A second-row theorem supplies the previously missing N2 degree fact. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem frameBorrowOwner_eq_aSecondRow {m : ℕ} (hm : 1 ≤ m) (i : ℕ)
    (hi : i % 2 = 0) (hilo : 2 ≤ i) (mode : Bool) :
    frameBorrowOwner hm i hi mode = aSecondRowSite m (if mode then i / 2 else i / 2 - 1) := by
  apply Subtype.ext
  funext k
  change (octEdgeZigzag m entryEdgeFrame i).val k + frameBorrowOffset mode k = _
  rw [entryEdgeZigzag_coordinates hm]
  cases mode <;> fin_cases k <;>
    dsimp [entryEdgeCoordinates, frameBorrowOffset, aSecondRowSite, aSecondRowCoordinates] <;> omega

theorem frameBorrowOwner_bulk_degree {m : ℕ} (hm : 30 ≤ m) (i : ℕ)
    (hi : i % 2 = 0) (hilo : 2 ≤ i) (mode : Bool)
    (hp : frameBorrowOwner (by omega : 1 ≤ m) i hi mode ∈ bulkInterior m) :
    (bulkCoverNeighbours m (frameBorrowOwner (by omega : 1 ≤ m) i hi mode)).card = 2 := by
  rw [frameBorrowOwner_eq_aSecondRow (by omega : 1 ≤ m) i hi hilo mode] at hp ⊢
  exact bulk_aSecondRow_degree m hm _ hp

theorem bulkEndColumn_ne_frameBorrowColumn {m : ℕ} (hm : 30 ≤ m)
    (i : ℕ) (hi : i % 2 = 0) (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool)
    (C : DanglingColumn m) (hC : C.owner ∈ bulkInterior m)
    (hend : (bulkCoverNeighbours m C.owner).card = 1) (n r : ℕ) :
    C.point n ≠ (frameBorrowColumn (by omega : 1 ≤ m) i hi hilo hihi mode).point r := by
  intro heq
  have howners := column_owner_eq_of_seed_eq C _ (DanglingColumn.seeds_eq_of_point_eq C _ heq)
  rw [howners] at hC hend
  have hdegree := frameBorrowOwner_bulk_degree hm i hi hilo mode hC
  exact (by decide : (2 : ℕ) ≠ 1) (hdegree.symm.trans hend)

theorem edgeZigzag_mem_deleted {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (i : ℕ)
    (hi : i < 2 * m - 1) : octEdgeZigzag m F i ∈ bulkDeletedEdges m := by
  have he := octEdgeZigzag_mem hm F hi
  have hp := he.elim (fun h => h.1.1) (fun h => h.1.1)
  exact Finset.mem_filter.mpr ⟨hp, F.k, F.j, F.kj, he⟩

theorem frameBorrowPoint_ne_bulkEndColumn {m : ℕ} (hm : 30 ≤ m)
    (i : ℕ) (hi : i % 2 = 0) (hilo : 2 ≤ i) (hihi : (i : ℤ) + 2 ≤ octRadius m) (mode : Bool)
    (C : DanglingColumn m) (hC : C.owner ∈ bulkInterior m)
    (hend : (bulkCoverNeighbours m C.owner).card = 1) (n r : ℕ) :
    frameBorrowPoint (by omega : 1 ≤ m) i hi hilo hihi mode n ≠ C.point r := by
  cases n with
  | zero =>
    have hdel := edgeZigzag_mem_deleted (by omega : 1 ≤ m) entryEdgeFrame i
      (by dsimp [octRadius] at hihi; omega)
    let D : DanglingColumn m := ⟨octEdgeZigzag m entryEdgeFrame i, 2,
      (Finset.mem_filter.mp hdel).1,
      (frameLinkerCap_dangling (by omega : 1 ≤ m) i hi hilo hihi).1⟩
    exact (bulkColumn_ne_edgeColumn C D hC hdel r 0).symm
  | succ n => exact (bulkEndColumn_ne_frameBorrowColumn hm i hi hilo hihi mode C hC hend r (n + 1)).symm

end ProteinFolding.Tetrahedral.NearField

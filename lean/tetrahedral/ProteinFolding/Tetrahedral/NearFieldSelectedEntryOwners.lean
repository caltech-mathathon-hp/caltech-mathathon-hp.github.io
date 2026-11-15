import ProteinFolding.Tetrahedral.NearFieldEntryCapFamily
import ProteinFolding.Tetrahedral.NearFieldBorrowedOwnersInterior

/-! Borrowed entry-column owners are interior second-row A sites of
degree two. They therefore cannot be ordinary local or bulk endpoint owners. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

theorem frameBorrowOwner_small_strict {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hlo : 2 ≤ i) (hhi : (i : ℤ) + 4 ≤ octRadius m) (mode : Bool)
    (hnear : mode = true ∨ 4 ≤ i) (d : Fin 4) :
    -octRadius m < tetraCoordinate m (frameBorrowOwner hm i hi mode).val d := by
  change -octRadius m < tetraCoordinate m
    (fun k => (octEdgeZigzag m entryEdgeFrame i).val k + frameBorrowOffset mode k) d
  simp only [tetraCoordinate_add_linear]
  rw [entryEdgeZigzag_coordinates hm]
  cases mode
  · have hi4 : 4 ≤ i := by
      rcases hnear with h | h
      · cases h
      · exact h
    fin_cases d <;> dsimp [entryEdgeCoordinates, frameBorrowOffset, tetraCoordinate, octRadius] at hhi ⊢ <;> omega
  · fin_cases d <;> dsimp [entryEdgeCoordinates, frameBorrowOffset, tetraCoordinate, octRadius] at hhi ⊢ <;> omega

theorem frameBorrowOwner_not_deleted {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hlo : 2 ≤ i) (hhi : (i : ℤ) + 4 ≤ octRadius m) (mode : Bool)
    (hnear : mode = true ∨ 4 ≤ i) : frameBorrowOwner hm i hi mode ∉ bulkDeletedEdges m := by
  intro hdel
  obtain ⟨k, j, _, hedge⟩ := (Finset.mem_filter.mp hdel).2
  rcases hedge with hA | hB
  · have hs := frameBorrowOwner_small_strict hm i hi hlo hhi mode hnear j
    have he := hA.2
    omega
  · exact sublattices_disjoint _ (frameBorrowOwner_inA hm i hi mode) hB.1.2.1

theorem selectedEntryColumn_owner_bulk (p : ConstructionParameters) (i : EntryCapIndex p) :
    (selectedEntryColumn p i).owner ∈ bulkInterior p.side := by
  dsimp only [selectedEntryColumn]
  with_reducible
    exact frameBorrowColumn_owner_in_bulk (m := p.side) (by have h := p.side_ge; omega)
      (entryCapIndex p i) (entryCapIndex_even p i) (entryCapIndex_lo p i)
      (by have h := entryCapIndex_room p i; omega) (entryCapMode i)
      (entryCapIndex_near p i) (Or.inr (entryCapIndex_room p i))

theorem selectedEntryColumn_owner_degree_two (p : ConstructionParameters) (i : EntryCapIndex p) :
    (bulkCoverNeighbours p.side (selectedEntryColumn p i).owner).card = 2 := by
  have hb := selectedEntryColumn_owner_bulk p i
  dsimp only [selectedEntryColumn, frameBorrowColumn] at hb ⊢
  with_reducible
    exact frameBorrowOwner_bulk_degree (m := p.side) (by have h := p.side_ge; omega)
      (entryCapIndex p i) (entryCapIndex_even p i) (entryCapIndex_lo p i) (entryCapMode i)
      hb

private theorem column_owner_not_deleted_of_bulk {m : ℕ} (C : DanglingColumn m)
    (hC : C.owner ∈ bulkInterior m) : C.owner ∉ bulkDeletedEdges m := by
  dsimp only [bulkInterior] at hC
  with_reducible exact (Finset.mem_sdiff.mp hC).2

private theorem column_seed_ne_deletedColumn_of_bulk {m : ℕ} (C D : DanglingColumn m)
    (hC : C.owner ∈ bulkInterior m) (hD : D.owner ∈ bulkDeletedEdges m) : C.seed ≠ D.seed := by
  intro heq
  have ho := column_owner_eq_of_seed_eq C D heq
  have hnot := column_owner_not_deleted_of_bulk C hC
  exact hnot (ho.symm ▸ hD)

theorem selectedEntryColumn_seed_ne_deletedColumn (p : ConstructionParameters) (i : EntryCapIndex p)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkDeletedEdges p.side) :
    (selectedEntryColumn p i).seed ≠ C.seed := by
  with_reducible
    exact column_seed_ne_deletedColumn_of_bulk (m := p.side) (selectedEntryColumn p i) C
      (selectedEntryColumn_owner_bulk p i) hC

theorem selectedEntryColumn_seed_ne_bulkEndpoint (p : ConstructionParameters) (i : EntryCapIndex p)
    (C : DanglingColumn p.side) (hC : (bulkCoverNeighbours p.side C.owner).card = 1) :
    (selectedEntryColumn p i).seed ≠ C.seed := by
  intro heq
  have ho := column_owner_eq_of_seed_eq (selectedEntryColumn p i) C heq
  have htwo := selectedEntryColumn_owner_degree_two p i
  rw [ho, hC] at htwo
  omega

private theorem column_points_ne_of_degree_two_one {m : ℕ} (C D : DanglingColumn m)
    (hC : (bulkCoverNeighbours m C.owner).card = 2)
    (hD : (bulkCoverNeighbours m D.owner).card = 1) (n r : ℕ) : C.point n ≠ D.point r := by
  intro heq
  have ho := column_owner_eq_of_seed_eq C D (DanglingColumn.seeds_eq_of_point_eq C D heq)
  rw [ho, hD] at hC
  omega

theorem selectedEntryColumn_ne_bulkEndColumn (p : ConstructionParameters) (i : EntryCapIndex p)
    (C : DanglingColumn p.side) (_hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1) (n r : ℕ) :
    (selectedEntryColumn p i).point n ≠ C.point r :=
  column_points_ne_of_degree_two_one (selectedEntryColumn p i) C
    (selectedEntryColumn_owner_degree_two p i) hend n r

end ProteinFolding.Tetrahedral.NearField

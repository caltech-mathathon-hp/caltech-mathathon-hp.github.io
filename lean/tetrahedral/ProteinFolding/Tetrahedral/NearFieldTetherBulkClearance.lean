import ProteinFolding.Tetrahedral.NearFieldBulkColumnSeparation
import ProteinFolding.Tetrahedral.NearFieldTetherSites

/-! Every actual bulk endpoint column avoids the entire tether family,
including all caps and all column prefixes. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem entryDown_ne_bulkColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (i : Fin (2 * p.entrySkin k - 1)) (n : ℕ) : (entryDown p k hk).pos i ≠ C.point n :=
  (bulkColumn_ne_edgeColumn C (entryTargetColumn p k hk) hC
    (faceColumn_zero_b_owner_deleted _ _ _ (by have h := p.separator_room k hk; omega)) n i.rev.val).symm

theorem exitUp_ne_bulkColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (i : Fin (exitColumnCount p k)) (n : ℕ) : (exitUp p k hk).pos i ≠ C.point n :=
  (bulkColumn_ne_edgeColumn C (exitSourceColumn p k hk) hC
    (faceColumn_zero_b_owner_deleted _ _ _ (by have h := p.separator_room k hk; omega)) n i.val).symm

theorem exitDown_ne_bulkColumn (p : ConstructionParameters) (k : ℕ)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (i : Fin (exitColumnCount p k)) (n : ℕ) : (exitDown p k).pos i ≠ C.point n :=
  (bulkColumn_ne_edgeColumn C (exitTargetColumn p k) hC
    (faceColumn_zero_a_owner_deleted _ _ _ (by have h := p.exit_column_triangle_room k; omega)) n i.rev.val).symm

theorem entryTetherFold_ne_bulkEndColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1)
    (i : Fin (p.entryTether k)) (n : ℕ) : (entryTetherFold p k hk).pos i ≠ C.point n :=
  entryTetherFold_property p k hk (fun q => q ≠ C.point n)
    (fun r => entryUp_ne_bulkEndColumn p k hk C hC hend r n)
    (fun r => entryRow_ne_bulkEndColumn p k hk C hC hend r n)
    (fun r => entryDown_ne_bulkColumn p k hk C hC r n) i

theorem exitTetherFold_ne_bulkColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (i : Fin (p.exitTether k)) (n : ℕ) : (exitTetherFold p k hk).pos i ≠ C.point n :=
  exitTetherFold_property p k hk (fun q => q ≠ C.point n)
    (fun r => exitUp_ne_bulkColumn p k hk C hC r n)
    (fun r => exitRow_ne_column p k hk C r n)
    (fun r => exitDown_ne_bulkColumn p k C hC r n) i

theorem tetherFold_ne_bulkEndColumn (p : ConstructionParameters) (t : TetherIndex p)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1)
    (i : Fin (tetherCount p t)) (n : ℕ) : (tetherFold p t).pos i ≠ C.point n := by
  rcases t with ⟨b, k⟩
  cases b
  · exact entryTetherFold_ne_bulkEndColumn p k.val (Nat.le_of_lt_succ k.isLt) C hC hend i n
  · exact exitTetherFold_ne_bulkColumn p k.val (Nat.le_of_lt_succ k.isLt) C hC i n

theorem bulkEndColumn_disjoint_tetherSites (p : ConstructionParameters)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1) (n : ℕ) : C.point n ∉ tetherSites p := by
  intro hmem
  obtain ⟨t, i, hi⟩ := (mem_tetherSites p _).mp hmem
  exact tetherFold_ne_bulkEndColumn p t C hC hend i n hi

end ProteinFolding.Tetrahedral.NearField

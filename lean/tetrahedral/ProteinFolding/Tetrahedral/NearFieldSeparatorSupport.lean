import ProteinFolding.Tetrahedral.NearFieldSeparatorFold
import ProteinFolding.Tetrahedral.NearFieldDimerBounds
import ProteinFolding.Tetrahedral.NearFieldDimerBulkClearance
import ProteinFolding.Tetrahedral.NearFieldTetherBulkClearance

/-! Exact H support and bulk-column clearance of the actual separator fold. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

theorem separatorFold_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    hSupport (p.separatorWord k) (separatorFold p k hk) =
      (edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0 ∪
        edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k) 1) ∪
          edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hA : hSupport (dimerChain 1) (separatorEntryChain p k hk) =
      edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0 :=
    edgeDimerFold_hSupport hm entryEdgeFrame _ _ false (separatorEntry_room p k hk)
  have hC : hSupport (dimerChain 2) (separatorCenterChain p k hk) =
      edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k) 1 :=
    edgeDimerFold_hSupport hm trackEdgeFrame _ _ true (separatorCenter_room p k hk)
  have hE : hSupport (dimerChain 3) (separatorExitChain p k) =
      edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 :=
    edgeDimerFold_hSupport hm exitEdgeFrame _ _ true (separatorExit_room p k)
  change hSupport ((((dimerChain 1 ++ List.replicate (p.entryTether k) Residue.P) ++
    dimerChain 2) ++ List.replicate (p.exitTether k) Residue.P) ++ dimerChain 3) (separatorFold p k hk) = _
  unfold separatorFold separatorMiddleOut separatorMiddle separatorEntryWalk
  rw [hSupport_appendWord, hSupport_appendWord, hSupport_appendWord, hSupport_appendWord,
    hSupport_allP_empty, hSupport_allP_empty]
  simp only [Finset.union_empty]
  rw [hA, hC, hE]

theorem separatorFold_ne_bulkEndColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1)
    (i : Fin (p.separatorWord k).length) (n : ℕ) : (separatorFold p k hk).pos i ≠ C.point n := by
  have hm : 30 ≤ p.side := by have h := p.side_ge; omega
  apply separatorFold_property p k hk (fun x => x ≠ C.point n) _ _ _ _ _ i
  · exact fun j => edgeDimerFold_ne_bulkEndColumn p.side hm entryEdgeFrame (6 * (k + 1)) 0 false
      (separatorEntry_room p k hk) C hC hend j n
  · intro j
    rw [entryTetherWordFold_pos]
    exact entryTetherFold_ne_bulkEndColumn p k hk C hC hend ⟨j.val, by simpa using j.isLt⟩ n
  · exact fun j => edgeDimerFold_ne_bulkEndColumn p.side hm trackEdgeFrame (2 * p.separatorIndex k) 1 true
      (separatorCenter_room p k hk) C hC hend j n
  · intro j
    rw [exitTetherWordFold_pos]
    exact exitTetherFold_ne_bulkColumn p k hk C hC ⟨j.val, by simpa using j.isLt⟩ n
  · exact fun j => edgeDimerFold_ne_bulkEndColumn p.side hm exitEdgeFrame (10 * p.exitSlot k + 6) 2 true
      (separatorExit_room p k) C hC hend j n

theorem separatorFold_mem_solid (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.separatorWord k).length) : (separatorFold p k hk).pos i ∈ skinSolid p.side (2 * p.bins + 3) := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply separatorFold_property p k hk (fun x => x ∈ skinSolid p.side (2 * p.bins + 3)) _ _ _ _ _ i
  · intro j
    exact skinSolid_mono p.side (by omega : 1 ≤ 2 * p.bins + 3)
      (edgeDimerFold_mem_solid_one hm entryEdgeFrame (6 * (k + 1)) 0 false (separatorEntry_room p k hk) j)
  · intro j
    rw [entryTetherWordFold_pos]
    exact entryTetherFold_mem_solid p k hk ⟨j.val, by simpa using j.isLt⟩
  · intro j
    exact skinSolid_mono p.side (by omega : 1 ≤ 2 * p.bins + 3)
      (edgeDimerFold_mem_solid_one hm trackEdgeFrame (2 * p.separatorIndex k) 1 true (separatorCenter_room p k hk) j)
  · intro j
    rw [exitTetherWordFold_pos]
    exact exitTetherFold_mem_solid p k hk ⟨j.val, by simpa using j.isLt⟩
  · intro j
    exact skinSolid_mono p.side (by omega : 1 ≤ 2 * p.bins + 3)
      (edgeDimerFold_mem_solid_one hm exitEdgeFrame (10 * p.exitSlot k + 6) 2 true (separatorExit_room p k) j)

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.NearFieldSelectedCapData
import ProteinFolding.Tetrahedral.NearFieldCanonicalCappedUnits
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonFamily
import ProteinFolding.Tetrahedral.NearFieldOrdinaryInnerColumns
import ProteinFolding.Tetrahedral.ReductionTM2BulkEndpointFacts

/-! Every actual selected endpoint is either its physical ordinary cap,
with a deleted-edge or degree-one owner, or the prescribed borrowed entry. -/

namespace ProteinFolding.Tetrahedral.NearField

private theorem column_owner_deleted_of_edge {m : ℕ} (hm : 1 ≤ m)
    (C : DanglingColumn m) (F : OctEdgeFrame) (r : ℕ) (hr : r < 2 * m - 1)
    (howner : C.owner = octEdgeZigzag m F r) : C.owner ∈ bulkDeletedEdges m :=
  Eq.mpr (congrArg (fun x : Site => x ∈ bulkDeletedEdges m) howner)
    (@edgeZigzag_mem_deleted m hm F r hr)

private theorem frameEndpointColumn_owner_deleted {m : ℕ} (hm : 1 ≤ m) (b : Bool) :
    (frameEndpointColumn hm b).owner ∈ bulkDeletedEdges m := by
  apply octVertices_subset_bulkDeleted hm
  cases b
  · exact Finset.mem_image.mpr ⟨(0, true), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨(2, false), Finset.mem_univ _, rfl⟩

private theorem rightFinalColumn_owner_deleted (p : ConstructionParameters) :
    (rightFinalColumn p).owner ∈ bulkDeletedEdges p.side := by
  with_reducible
    exact column_owner_deleted_of_edge (m := p.side) (by have h := p.side_ge; omega)
      (rightFinalColumn p) exitEdgeFrame 1 (by have h := p.side_ge; omega)
      (rightFinalColumn_exit_owner p)

private theorem singletonPiece_first_seed (m : ℕ) (hm : 1 ≤ m) (i : Fin 3) :
    (canonicalSingletonPiece m hm i).first = (canonicalSingletonColumn m hm i false).seed := by
  dsimp only [canonicalSingletonPiece, singletonWordPiece]

private theorem singletonPiece_last_seed (m : ℕ) (hm : 1 ≤ m) (i : Fin 3) :
    (canonicalSingletonPiece m hm i).last = (canonicalSingletonColumn m hm i true).seed := by
  dsimp only [canonicalSingletonPiece, singletonWordPiece]

private theorem framePiece_first_seed (p : ConstructionParameters) :
    (frameWordPiece p).first = (frameFirstColumn p).seed := by
  dsimp only [frameWordPiece]

private theorem framePiece_last_seed (p : ConstructionParameters) :
    (frameWordPiece p).last = (frameLastColumn p).seed := by
  dsimp only [frameWordPiece]

private theorem itemPiece_first_seed (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    (canonicalItemPiece p k before s hk hs hload).first = (itemFirstColumn p k before s hk hs hload).seed := by
  dsimp only [canonicalItemPiece, itemWordPiece, cappedIntervalDimerPiece]

private theorem itemPiece_last_seed (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    (canonicalItemPiece p k before s hk hs hload).last = (itemLastColumn p k before s hk hs hload).seed := by
  dsimp only [canonicalItemPiece, itemWordPiece, cappedIntervalDimerPiece]

theorem singletonCappedUnit_selectedCapData (p : ConstructionParameters) (i : Fin 3) (b : Bool) :
    SelectedCapData p (wordEndpoint (singletonCappedUnit p i).piece b) ((singletonCappedUnit p i).column b) := by
  dsimp only [singletonCappedUnit]
  with_reducible
    exact CappedUnit.ofColumns_selectedCapData p [Residue.H]
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) i)
      (canonicalSingletonPiece_word p.side (by have h := p.side_ge; omega) i)
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) i false)
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) i true)
      (singletonPiece_first_seed p.side (by have h := p.side_ge; omega) i)
      (singletonPiece_last_seed p.side (by have h := p.side_ge; omega) i)
      (Or.inl (canonicalSingletonColumn_owner_deleted p.side (by have h := p.side_ge; omega) i false))
      (Or.inl (canonicalSingletonColumn_owner_deleted p.side (by have h := p.side_ge; omega) i true)) b

theorem frameCappedUnit_selectedCapData (p : ConstructionParameters) (b : Bool) :
    SelectedCapData p (wordEndpoint (frameCappedUnit p).piece b) ((frameCappedUnit p).column b) := by
  have hfirst : (frameFirstColumn p).owner ∈ bulkDeletedEdges p.side := by
    dsimp only [frameFirstColumn]
    with_reducible exact frameEndpointColumn_owner_deleted (m := p.side) (by have h := p.side_ge; omega) true
  have hlast : (frameLastColumn p).owner ∈ bulkDeletedEdges p.side := by
    dsimp only [frameLastColumn]
    with_reducible exact frameEndpointColumn_owner_deleted (m := p.side) (by have h := p.side_ge; omega) false
  dsimp only [frameCappedUnit]
  with_reducible
    exact CappedUnit.ofColumns_selectedCapData p (p.framePart1 ++ p.framePart2) (frameWordPiece p) (frameWordPiece_word p)
      (frameFirstColumn p) (frameLastColumn p) (framePiece_first_seed p) (framePiece_last_seed p)
      (Or.inl hfirst) (Or.inl hlast) b

private theorem separatorPiece_first_cap (p : ConstructionParameters) (k : Fin (p.bins + 1)) :
    (canonicalSeparatorPiece p k).first = entryCapSite p (some k) := by
  dsimp only [canonicalSeparatorPiece, separatorWordPiece]
  exact entryLocalColumn_seed p (some k)

private theorem separatorPiece_last_seed (p : ConstructionParameters) (k : Fin (p.bins + 1)) :
    (canonicalSeparatorPiece p k).last =
      (exitCapColumn p k.val (by have h := k.isLt; omega)).seed := by
  dsimp only [canonicalSeparatorPiece, separatorWordPiece]

theorem separatorCappedUnit_selectedCapData (p : ConstructionParameters) (k : Fin (p.bins + 1)) (b : Bool) :
    SelectedCapData p (wordEndpoint (separatorCappedUnit p k).piece b) ((separatorCappedUnit p k).column b) := by
  cases b
  · change SelectedCapData p (canonicalSeparatorPiece p k).last
      (exitCapColumn p k.val (by have h := k.isLt; omega))
    with_reducible
      exact @SelectedCapData.ordinary p (canonicalSeparatorPiece p k).last
        (exitCapColumn p k.val (by have h := k.isLt; omega)) (separatorPiece_last_seed p k).symm
        (Or.inl (exitCapColumn_owner_deleted p k.val (by have h := k.isLt; omega)))
  · change SelectedCapData p (canonicalSeparatorPiece p k).first (selectedEntryColumn p (some k))
    with_reducible
      exact @SelectedCapData.borrowed p (canonicalSeparatorPiece p k).first
        (selectedEntryColumn p (some k)) (some k) rfl (separatorPiece_first_cap p k)

theorem leftCappedUnit_selectedCapData (p : ConstructionParameters) (b : Bool) :
    SelectedCapData p (wordEndpoint (leftCappedUnit p).piece b) ((leftCappedUnit p).column b) := by
  cases b
  · change SelectedCapData p (canonicalLeftPiece p).last (leftLastColumn p)
    with_reducible
      exact @SelectedCapData.ordinary p (canonicalLeftPiece p).last
        (leftLastColumn p) (canonicalLeftPiece_last p).symm (Or.inl (leftLastColumn_ordinary p).owner_deleted)
  · change SelectedCapData p (canonicalLeftPiece p).first (selectedEntryColumn p none)
    with_reducible
      exact @SelectedCapData.borrowed p (canonicalLeftPiece p).first
        (selectedEntryColumn p none) none rfl (canonicalLeftPiece_first p)

theorem itemCappedUnit_selectedCapData (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) (b : Bool) :
    SelectedCapData p (wordEndpoint (itemCappedUnit p k before s hk hs hload).piece b)
      ((itemCappedUnit p k before s hk hs hload).column b) := by
  dsimp only [itemCappedUnit]
  with_reducible
    exact CappedUnit.ofColumns_selectedCapData p (dimerChain (p.itemDimers s))
      (canonicalItemPiece p k before s hk hs hload) (canonicalItemPiece_word p k before s hk hs hload)
      (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
      (itemPiece_first_seed p k before s hk hs hload) (itemPiece_last_seed p k before s hk hs hload)
      (Or.inl (itemFirstColumn_ordinary p k before s hk hs hload).owner_deleted)
      (Or.inl (itemLastColumn_ordinary p k before s hk hs hload).owner_deleted) b

theorem rightCappedUnit_selectedCapData (p : ConstructionParameters) (b : Bool) :
    SelectedCapData p (wordEndpoint (rightCappedUnit p).piece b) ((rightCappedUnit p).column b) := by
  dsimp only [rightCappedUnit]
  with_reducible
    exact CappedUnit.ofColumns_selectedCapData p (dimerChain p.rightFiller)
      (canonicalRightPiece p) (canonicalRightPiece_word p)
      (rightFirstColumn p) (rightFinalColumn p) (canonicalRightPiece_first p) (canonicalRightPiece_last p)
      (Or.inl (rightFirstColumn_ordinary p).owner_deleted) (Or.inl (rightFinalColumn_owner_deleted p)) b

theorem ringCappedUnit_selectedCapData (p : ConstructionParameters) (i : Fin 3) (b : Bool) :
    SelectedCapData p (wordEndpoint (ringCappedUnit p i).piece b) ((ringCappedUnit p i).column b) := by
  dsimp only [ringCappedUnit]
  with_reducible
    exact CappedUnit.ofColumns_selectedCapData p (dimerChain (3 * (p.side - 2)))
      (canonicalRingWordPiece p i) (canonicalRingWordPiece_word p i)
      (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
      (canonicalRingWordPiece_first p i) (canonicalRingWordPiece_last p i)
      (Or.inl (canonicalRingColumn_owner_deleted p i 0)) (Or.inl (canonicalRingColumn_owner_deleted p i 1)) b

theorem bulkCappedUnit_selectedCapData (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) (b : Bool) :
    SelectedCapData p (wordEndpoint (bulkCappedUnit p ha j).piece b) ((bulkCappedUnit p ha j).column b) := by
  have hm : 27 ≤ p.side := by have h := p.side_ge; omega
  have hfirst := (ReductionTM2.BulkScan.runtimeColumn_data p.side hm ha j false
    (ReductionTM2.BulkScan.firstColumn p.side hm ha j)
    (ReductionTM2.BulkScan.firstColumn_owner p.side hm ha j)).2
  have hlast := (ReductionTM2.BulkScan.runtimeColumn_data p.side hm ha j true
    (ReductionTM2.BulkScan.lastColumn p.side hm ha j)
    (ReductionTM2.BulkScan.lastColumn_owner p.side hm ha j)).2
  exact CappedUnit.ofColumns_selectedCapData p
    (List.replicate ((ReductionTM2.BulkScan.lengths p.side).get j) Residue.H)
    (ReductionTM2.BulkScan.cappedRuntimePiece p.side hm ha j) rfl
    (ReductionTM2.BulkScan.firstColumn p.side hm ha j) (ReductionTM2.BulkScan.lastColumn p.side hm ha j)
    rfl rfl (Or.inr hfirst) (Or.inr hlast) b

theorem canonicalTagged_selectedCapData (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    CanonicalTaggedProperty p ha (fun u => ∀ b, SelectedCapData p (wordEndpoint u.piece b) (u.column b)) := {
  singleton := singletonCappedUnit_selectedCapData p
  frame := frameCappedUnit_selectedCapData p
  separator := separatorCappedUnit_selectedCapData p
  left := leftCappedUnit_selectedCapData p
  item := itemCappedUnit_selectedCapData p
  right := rightCappedUnit_selectedCapData p
  ring := ringCappedUnit_selectedCapData p
  bulk := bulkCappedUnit_selectedCapData p ha }

theorem canonicalTaggedBody_selectedCapData (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) (u : CappedUnit p.side)
    (hu : u ∈ canonicalTaggedBodies p items d ha) (b : Bool) :
    SelectedCapData p (wordEndpoint u.piece b) (u.column b) :=
  canonicalTaggedBodies_selectedProperty p items d ha _ (canonicalTagged_selectedCapData p ha) u hu b

theorem terminal_selectedCapData (p : ConstructionParameters) :
    SelectedCapData p (terminalWordPiece p).last (terminalColumn p) := by
  dsimp only [terminalWordPiece]
  with_reducible
    exact @SelectedCapData.ordinary p (terminalColumn p).seed (terminalColumn p) rfl
      (Or.inl (column_owner_deleted_of_edge (m := p.side) (by have h := p.side_ge; omega)
        (terminalColumn p) entryEdgeFrame (2 * p.side - 3) (by have h := p.side_ge; omega)
        (terminalColumn_owner p)))

end ProteinFolding.Tetrahedral.NearField

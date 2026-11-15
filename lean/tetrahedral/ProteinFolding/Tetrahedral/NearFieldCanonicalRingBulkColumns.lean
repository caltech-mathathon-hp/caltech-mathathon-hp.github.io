import ProteinFolding.Tetrahedral.NearFieldCanonicalUnits
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonFamily
import ProteinFolding.Tetrahedral.NearFieldFrameColumnFamily
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingTetherColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingTrackSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalBulkSeparation

/-! Complete local-unit clearance for actual ring and bulk endpoint columns.
The initial HP unit and capped all-H bulk words admit arbitrary columns. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

attribute [local irreducible] ConstructionParameters.side

theorem terminalWordPiece_ne_positiveColumn (p : ConstructionParameters) (C : DanglingColumn p.side)
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (terminalWordPiece p).word.length) :
    (terminalWordPiece p).fold.pos i ≠ C.point n := by
  change (if i.val = 0 then (terminalColumn p).owner else (terminalColumn p).seed) ≠ C.point n
  split_ifs
  · intro heq
    have h := (terminalColumn p).owner_mem
    rw [heq] at h
    exact C.point_outside n h
  · exact FarField.dangling_ne_positive_column (terminalColumn p).seed_dangling C n hn

theorem canonicalBulkPiece_ne_positiveColumn (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) (j : Fin (ReductionTM2.BulkScan.lengths p.side).length)
    (C : DanglingColumn p.side) (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).word.length) :
    (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).fold.pos i ≠ C.point n :=
  ReductionTM2.BulkScan.cappedRuntimePiece_ne_positive_column p.side (by have h := p.side_ge; omega) ha j
    (ReductionTM2.BulkScan.firstColumn p.side (by have h := p.side_ge; omega) ha j)
    (ReductionTM2.BulkScan.lastColumn p.side (by have h := p.side_ge; omega) ha j) rfl rfl C n hn i

theorem canonicalLocal_ne_ringColumn (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (r : Fin 3) (e : Fin 2) (n : ℕ) (hn : 1 ≤ n) :
    CanonicalLocalProperty p ha (fun q => ∀ i, q.fold.pos i ≠ (canonicalRingColumn p r e).point n) where
  singleton s i := canonicalSingletonPiece_ne_positiveColumn p.side (by have h := p.side_ge; omega)
    s (canonicalRingColumn p r e) n hn i
  frame i := frameFold_ne_canonicalRingColumn p r e n hn i
  separator k i := canonicalSeparatorPiece_ne_ringColumn p r e k i n
  left i := canonicalLeftPiece_ne_ringColumn p r e i n
  item k before s hk hs hload i := canonicalItemPiece_ne_ringColumn p r e k before s hk hs hload i n
  right i := canonicalRightPiece_ne_ringColumn p r e i n
  ring s i := canonicalRingWordPiece_ne_column_pos p s r e i n (by omega)
  bulk j i := canonicalBulkPiece_ne_positiveColumn p ha j (canonicalRingColumn p r e) n hn i

theorem canonicalLocal_ne_bulkColumn (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1) (n : ℕ) (hn : 1 ≤ n) :
    CanonicalLocalProperty p ha (fun q => ∀ i, q.fold.pos i ≠ C.point n) where
  singleton r i := canonicalSingletonPiece_ne_bulkEndColumn p r C hC i n
  frame i := frameFold_ne_bulkEndColumn p C hC i n
  separator k i := canonicalSeparatorPiece_ne_bulkEndColumn p k C hC hend i n
  left i := canonicalLeftPiece_ne_bulkEndColumn p C hC hend i n
  item k before s hk hs hload i := canonicalItemPiece_ne_bulkEndColumn p k before s hk hs hload C hC hend i n
  right i := canonicalRightPiece_ne_bulkEndColumn p C hC hend i n
  ring r i := canonicalRingWordPiece_ne_bulkEndColumn p r C hC hend i n
  bulk j i := canonicalBulkPiece_ne_positiveColumn p ha j C n hn i

theorem canonicalUnitPieces_ne_ringColumn (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (r : Fin 3) (e : Fin 2) (n : ℕ) (hn : 1 ≤ n)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha) (i : Fin q.word.length) :
    q.fold.pos i ≠ (canonicalRingColumn p r e).point n :=
  canonicalUnitPieces_property p items d ha _
    (terminalWordPiece_ne_positiveColumn p (canonicalRingColumn p r e) n hn)
    (canonicalLocal_ne_ringColumn p ha r e n hn) q hq i

theorem canonicalUnitPieces_ne_bulkColumn (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (C : DanglingColumn p.side) (hC : C.owner ∈ bulkInterior p.side)
    (hend : (bulkCoverNeighbours p.side C.owner).card = 1) (n : ℕ) (hn : 1 ≤ n)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha) (i : Fin q.word.length) :
    q.fold.pos i ≠ C.point n :=
  canonicalUnitPieces_property p items d ha _ (terminalWordPiece_ne_positiveColumn p C n hn)
    (canonicalLocal_ne_bulkColumn p ha C hC hend n hn) q hq i

end ProteinFolding.Tetrahedral.NearField

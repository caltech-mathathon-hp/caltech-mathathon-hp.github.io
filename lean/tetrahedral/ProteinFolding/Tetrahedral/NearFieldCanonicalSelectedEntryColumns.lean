import ProteinFolding.Tetrahedral.NearFieldSelectedEntryUnitColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingBulkColumns

/-! Whole-list N5 for the actual selected borrowed entry columns. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem canonicalRingWordPiece_ne_selectedEntryColumn (p : ConstructionParameters) (r : Fin 3)
    (a : EntryCapIndex p) (i : Fin (canonicalRingWordPiece p r).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalRingWordPiece p r).fold.pos i ≠ (selectedEntryColumn p a).point n := by
  cases n with
  | zero => omega
  | succ n =>
    exact canonicalRingWordPiece_ne_frameBorrowPoint p r (entryCapIndex p a) (entryCapIndex_even p a)
      (entryCapIndex_lo p a) (by have h := entryCapIndex_room p a; omega) (entryCapMode a)
      (entryCapIndex_near p a) (Or.inr (entryCapIndex_room p a)) i (n + 1)

theorem canonicalLocal_ne_selectedEntryColumn (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) (a : EntryCapIndex p) (n : ℕ) (hn : 1 ≤ n) :
    CanonicalLocalProperty p ha (fun q => ∀ i, q.fold.pos i ≠ (selectedEntryColumn p a).point n) where
  singleton r i := canonicalSingletonPiece_ne_positiveColumn p.side (by have h := p.side_ge; omega)
    r (selectedEntryColumn p a) n hn i
  frame i := frameFold_ne_selectedEntryColumn p a n hn i
  separator k i := canonicalSeparatorPiece_ne_selectedEntryColumn p k a i n hn
  left i := canonicalLeftPiece_ne_selectedEntryColumn p a i n hn
  item k before s hk hs hload i := canonicalItemPiece_ne_selectedEntryColumn p a k before s hk hs hload i n hn
  right i := canonicalRightPiece_ne_selectedEntryColumn p a i n hn
  ring r i := canonicalRingWordPiece_ne_selectedEntryColumn p r a i n hn
  bulk j i := canonicalBulkPiece_ne_positiveColumn p ha j (selectedEntryColumn p a) n hn i

theorem canonicalUnitPieces_ne_selectedEntryColumn (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (a : EntryCapIndex p) (n : ℕ) (hn : 1 ≤ n)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha) (i : Fin q.word.length) :
    q.fold.pos i ≠ (selectedEntryColumn p a).point n :=
  canonicalUnitPieces_property p items d ha _
    (terminalWordPiece_ne_positiveColumn p (selectedEntryColumn p a) n hn)
    (canonicalLocal_ne_selectedEntryColumn p ha a n hn) q hq i

end ProteinFolding.Tetrahedral.NearField

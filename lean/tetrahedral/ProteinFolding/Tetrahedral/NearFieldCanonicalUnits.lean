import ProteinFolding.Tetrahedral.NearFieldCanonicalCappedUnits

/-! The actual tagged bodies project to precisely the source unit order.
The terminal is kept separate because its word has only a trailing cap. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 500000
set_option maxRecDepth 4096

noncomputable def canonicalUnitPieces (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) : List PositionedWord :=
  terminalWordPiece p :: (canonicalTaggedBodies p items d ha).map CappedUnit.piece

theorem canonicalUnitPieces_words (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (canonicalUnitPieces p items d ha).map PositionedWord.word =
      [Residue.H, Residue.P] ::
        (p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).map capWord := by
  rw [canonicalUnitPieces, List.map_cons, terminalWordPiece_word,
    CappedUnit.pieces_words, canonicalTaggedBodies_bodies]

theorem canonicalUnitPieces_length (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (canonicalUnitPieces p items d ha).length =
      (p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length + 1 := by
  have h := congrArg List.length (canonicalUnitPieces_words p items d ha)
  simpa only [List.length_map, List.length_cons, Nat.add_comm] using h

noncomputable def canonicalUnitAt (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin ((p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length + 1)) :
    PositionedWord :=
  (canonicalUnitPieces p items d ha).get (Fin.cast (canonicalUnitPieces_length p items d ha).symm i)

theorem canonicalUnitPieces_property (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) (P : PositionedWord → Prop)
    (hTerminal : P (terminalWordPiece p)) (hLocal : CanonicalLocalProperty p ha P)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha) : P q := by
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hTerminal
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
    exact canonicalTaggedBodies_property p items d ha P hLocal u hu

end ProteinFolding.Tetrahedral.NearField

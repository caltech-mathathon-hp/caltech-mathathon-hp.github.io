import ProteinFolding.Tetrahedral.NearFieldCanonicalColumnClearance
import ProteinFolding.Tetrahedral.NearFieldCanonicalRoutingUnits

/-! The complete actual selected-wire catalogue has N5 clearance from the
concrete source-ordered local obstacle set. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem canonicalSelectedWire_clear (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (e : FarField.Pairing (2 * canonicalBodyCount p items) (canonicalBodyCount p items))
    (a : Fin (2 * canonicalBodyCount p items)) (q : PositionedWord)
    (hq : q ∈ canonicalUnitPieces p items d ha) (i : Fin q.word.length) (n : ℕ) (hn : 1 ≤ n) :
    q.fold.pos i ≠
      (selectedUnitWireColumn (canonicalCappedBodyAt p items d ha) (terminalColumn p) e a).point n :=
  actualSelectedWire_column_clear p items d ha (canonicalUnitPieces_pairwise p items d ha)
    (canonicalCappedBodyAt p items d ha) (canonicalCappedBodyAt_mem p items d ha) e a q hq i n hn

theorem canonicalSelectedWire_avoids_pieceSites (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (e : FarField.Pairing (2 * canonicalBodyCount p items) (canonicalBodyCount p items))
    (a : Fin (2 * canonicalBodyCount p items)) (n : ℕ) (hn : 1 ≤ n) :
    (selectedUnitWireColumn (canonicalCappedBodyAt p items d ha) (terminalColumn p) e a).point n ∉
      pieceSites (canonicalUnitPieces p items d ha) :=
  actualSelectedWire_avoids_pieceSites p items d ha (canonicalUnitPieces_pairwise p items d ha)
    (canonicalCappedBodyAt p items d ha) (canonicalCappedBodyAt_mem p items d ha) e a n hn

theorem canonicalSelectedWire_clear_routingUnit (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (e : FarField.Pairing (2 * canonicalBodyCount p items) (canonicalBodyCount p items))
    (a : Fin (2 * canonicalBodyCount p items)) (j : Fin (canonicalBodyCount p items + 1))
    (i : Fin (canonicalRoutingUnits p items d ha j).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalRoutingUnits p items d ha j).fold.pos i ≠
      (selectedUnitWireColumn (canonicalCappedBodyAt p items d ha) (terminalColumn p) e a).point n :=
  canonicalSelectedWire_clear p items d ha e a _ (canonicalRoutingUnits_mem p items d ha j) i n hn

end ProteinFolding.Tetrahedral.NearField

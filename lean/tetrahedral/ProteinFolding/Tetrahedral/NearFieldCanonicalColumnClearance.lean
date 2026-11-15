import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonUnitColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalFrameEndpointColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingBulkColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalRightFinalColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalOrdinaryColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalTerminalColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalSelectedEntryColumns
import ProteinFolding.Tetrahedral.NearFieldCappedUnitRouting

/-! Every actual selected local column avoids all complete canonical units
at positive height. The only family premise is geometric pairwise disjointness. -/

namespace ProteinFolding.Tetrahedral.NearField

attribute [local irreducible] ConstructionParameters.side

private theorem unit_clear_of_tagged (p : ConstructionParameters) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) (C : DanglingColumn p.side) (n : ℕ) (hn : 1 ≤ n)
    (hbody : ∀ u ∈ canonicalTaggedBodies p items d ha, ∀ i, u.piece.fold.pos i ≠ C.point n)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha) (i : Fin q.word.length) :
    q.fold.pos i ≠ C.point n := by
  rcases List.mem_cons.mp hq with rfl | hq
  · exact terminalWordPiece_ne_positiveColumn p C n hn i
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
    exact hbody u hu i

private def TaggedColumnClear (p : ConstructionParameters) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) (u : CappedUnit p.side) : Prop :=
  u ∈ canonicalTaggedBodies p items d ha → ∀ (b : Bool) (q : PositionedWord),
    q ∈ canonicalUnitPieces p items d ha → ∀ (i : Fin q.word.length) (n : ℕ), 1 ≤ n →
      q.fold.pos i ≠ (u.column b).point n

theorem canonicalTagged_columnClear (p : ConstructionParameters) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) (hp : (canonicalUnitPieces p items d ha).Pairwise WordsDisjoint) :
    CanonicalTaggedProperty p ha (TaggedColumnClear p items d ha) := by
  have hpBody : ((canonicalTaggedBodies p items d ha).map CappedUnit.piece).Pairwise WordsDisjoint :=
    (List.pairwise_cons.mp hp).2
  refine {
    singleton := ?_
    frame := ?_
    separator := ?_
    left := ?_
    item := ?_
    right := ?_
    ring := ?_
    bulk := ?_ }
  · intro r hu b q hq i n hn
    cases b
    · exact canonicalUnitPieces_ne_singletonColumn p items d ha r true n hn q hq i
    · exact canonicalUnitPieces_ne_singletonColumn p items d ha r false n hn q hq i
  · intro hu b q hq i n hn
    cases b
    · exact canonicalUnitPieces_ne_frameEndpointColumn p items d ha false n hn q hq i
    · exact canonicalUnitPieces_ne_frameEndpointColumn p items d ha true n hn q hq i
  · intro k hu b q hq i n hn
    cases b
    · exact unit_clear_of_tagged p items d ha
        (exitCapColumn p k.val (by have h := k.isLt; omega)) n hn
        (fun u hu j => exitCapColumn_clear_of_pairwise p items d ha hpBody k u hu j n hn) q hq i
    · exact canonicalUnitPieces_ne_selectedEntryColumn p items d ha (some k) n hn q hq i
  · intro hu b q hq i n hn
    cases b
    · exact unit_clear_of_tagged p items d ha (leftLastColumn p) n hn
        (fun u hu j => leftLastColumn_clear_of_pairwise p items d ha hpBody u hu j n hn) q hq i
    · exact canonicalUnitPieces_ne_selectedEntryColumn p items d ha none n hn q hq i
  · intro k before s hk hs hload hu b q hq i n hn
    have hown : canonicalItemPiece p k before s hk hs hload ∈
        (canonicalTaggedBodies p items d ha).map CappedUnit.piece :=
      List.mem_map.mpr ⟨itemCappedUnit p k before s hk hs hload, hu, rfl⟩
    cases b
    · exact unit_clear_of_tagged p items d ha (itemLastColumn p k before s hk hs hload) n hn
        (fun u hu j => itemLastColumn_clear_of_pairwise p items d ha hpBody k before s hk hs hload hown u hu j n hn) q hq i
    · exact unit_clear_of_tagged p items d ha (itemFirstColumn p k before s hk hs hload) n hn
        (fun u hu j => itemFirstColumn_clear_of_pairwise p items d ha hpBody k before s hk hs hload hown u hu j n hn) q hq i
  · intro hu b q hq i n hn
    cases b
    · exact canonicalUnitPieces_ne_rightFinalColumn_of_pairwise p items d ha hpBody q hq i n hn
    · exact unit_clear_of_tagged p items d ha (rightFirstColumn p) n hn
        (fun u hu j => rightFirstColumn_clear_of_pairwise p items d ha hpBody u hu j n hn) q hq i
  · intro r hu b q hq i n hn
    cases b
    · exact canonicalUnitPieces_ne_ringColumn p items d ha r 1 n hn q hq i
    · exact canonicalUnitPieces_ne_ringColumn p items d ha r 0 n hn q hq i
  · intro j hu b q hq i n hn
    have hm : 27 ≤ p.side := by have h := p.side_ge; omega
    cases b
    · let C := ReductionTM2.BulkScan.lastColumn p.side hm ha j
      have hC := ReductionTM2.BulkScan.runtimeColumn_data p.side hm ha j true C
        (ReductionTM2.BulkScan.lastColumn_owner p.side hm ha j)
      exact canonicalUnitPieces_ne_bulkColumn p items d ha C hC.1 hC.2 n hn q hq i
    · let C := ReductionTM2.BulkScan.firstColumn p.side hm ha j
      have hC := ReductionTM2.BulkScan.runtimeColumn_data p.side hm ha j false C
        (ReductionTM2.BulkScan.firstColumn_owner p.side hm ha j)
      exact canonicalUnitPieces_ne_bulkColumn p items d ha C hC.1 hC.2 n hn q hq i

theorem canonicalTaggedBody_column_clear_of_pairwise (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : (canonicalUnitPieces p items d ha).Pairwise WordsDisjoint)
    (u : CappedUnit p.side) (hu : u ∈ canonicalTaggedBodies p items d ha) (b : Bool)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha)
    (i : Fin q.word.length) (n : ℕ) (hn : 1 ≤ n) : q.fold.pos i ≠ (u.column b).point n :=
  canonicalTaggedBodies_selectedProperty p items d ha _ (canonicalTagged_columnClear p items d ha hp)
    u hu hu b q hq i n hn

theorem canonicalUnitPieces_ne_terminalSelectedColumn (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha)
    (i : Fin q.word.length) (n : ℕ) (hn : 1 ≤ n) : q.fold.pos i ≠ (terminalColumn p).point n :=
  canonicalUnitPieces_property p items d ha _ (fun j => terminalWordPiece_ne_terminalColumn p j n hn)
    (canonicalLocal_ne_terminalColumn p ha n hn) q hq i

theorem actualCatalogue_column_clear (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : (canonicalUnitPieces p items d ha).Pairwise WordsDisjoint)
    {n : ℕ} (bs : Fin n → CappedUnit p.side) (hbs : ∀ i, bs i ∈ canonicalTaggedBodies p items d ha)
    (a : Option (Fin n × Bool)) (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha)
    (i : Fin q.word.length) (r : ℕ) (hr : 1 ≤ r) :
    q.fold.pos i ≠ (cappedUnitColumnCatalogue bs (terminalColumn p) a).point r := by
  cases a with
  | none => exact canonicalUnitPieces_ne_terminalSelectedColumn p items d ha q hq i r hr
  | some a => exact canonicalTaggedBody_column_clear_of_pairwise p items d ha hp (bs a.1) (hbs a.1) a.2 q hq i r hr

theorem actualSelectedWire_column_clear (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : (canonicalUnitPieces p items d ha).Pairwise WordsDisjoint)
    {n : ℕ} (bs : Fin n → CappedUnit p.side) (hbs : ∀ i, bs i ∈ canonicalTaggedBodies p items d ha)
    (e : FarField.Pairing (2 * n) n) (a : Fin (2 * n))
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha)
    (i : Fin q.word.length) (r : ℕ) (hr : 1 ≤ r) :
    q.fold.pos i ≠ (selectedUnitWireColumn bs (terminalColumn p) e a).point r :=
  selectedUnitWireColumn_property bs (terminalColumn p) e (fun C => q.fold.pos i ≠ C.point r)
    (fun b => actualCatalogue_column_clear p items d ha hp bs hbs b q hq i r hr) a

theorem actualSelectedWire_avoids_pieceSites (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : (canonicalUnitPieces p items d ha).Pairwise WordsDisjoint)
    {n : ℕ} (bs : Fin n → CappedUnit p.side) (hbs : ∀ i, bs i ∈ canonicalTaggedBodies p items d ha)
    (e : FarField.Pairing (2 * n) n) (a : Fin (2 * n)) (r : ℕ) (hr : 1 ≤ r) :
    (selectedUnitWireColumn bs (terminalColumn p) e a).point r ∉ pieceSites (canonicalUnitPieces p items d ha) := by
  intro hmem
  obtain ⟨q, hq, hsite⟩ := (mem_pieceSites _ _).mp hmem
  obtain ⟨i, hi⟩ := (mem_foldSites q.fold _).mp hsite
  exact actualSelectedWire_column_clear p items d ha hp bs hbs e a q hq i r hr hi

end ProteinFolding.Tetrahedral.NearField

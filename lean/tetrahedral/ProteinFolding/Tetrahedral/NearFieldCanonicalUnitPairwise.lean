import ProteinFolding.Tetrahedral.NearFieldCanonicalUnits
import ProteinFolding.Tetrahedral.NearFieldCappedSeparatorFamily

/-! The tagged occurrence permutation preserves the geometric item family.
All eight body families are internally disjoint; the final list-level
composition exposes only the still-required cross-family separation. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem list_forall_mem_nil_iff {α : Type*} (P : α → Prop) :
    (∀ x ∈ ([] : List α), P x) ↔ True :=
  ⟨fun _ => True.intro, fun _ => List.forall_mem_nil P⟩

theorem PackedBins.taggedBinUnits_pieces {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (k : Fin d.parts.length) :
    (d.taggedBinUnits k).map CappedUnit.piece = d.binPieces k := by
  rw [PackedBins.taggedBinUnits, List.map_ofFn]
  rfl

theorem PackedBins.taggedPlacedUnits_pieces {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : d.taggedPlacedUnits.map CappedUnit.piece = d.placedPieces := by
  simp only [PackedBins.taggedPlacedUnits, List.map_flatMap, d.taggedBinUnits_pieces,
    PackedBins.placedPieces]

theorem PackedBins.taggedPlacedUnits_pairwise {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) :
    d.taggedPlacedUnits.Pairwise (fun u v => WordsDisjoint u.piece v.piece) := by
  apply List.pairwise_map.mp
  rw [d.taggedPlacedUnits_pieces]
  exact d.placedPieces_pairwise

theorem PackedBins.taggedItems_pairwise {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) :
    d.taggedItems.Pairwise (fun u v => WordsDisjoint u.piece v.piece) :=
  d.taggedReordered.pairwise d.taggedPlacedUnits_pairwise

theorem PackedBins.taggedItemPieces_pairwise {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : (d.taggedItems.map CappedUnit.piece).Pairwise WordsDisjoint :=
  List.pairwise_map.mpr d.taggedItems_pairwise

theorem taggedSingletonUnits_pieces (p : ConstructionParameters) :
    (taggedSingletonUnits p).map CappedUnit.piece = canonicalSingletonPieces p := rfl

theorem taggedSeparatorUnits_pieces (p : ConstructionParameters) :
    (taggedSeparatorUnits p).map CappedUnit.piece = canonicalSeparatorPieces p := by
  rw [taggedSeparatorUnits, List.map_ofFn]
  rfl

theorem taggedRingUnits_pieces (p : ConstructionParameters) :
    (taggedRingUnits p).map CappedUnit.piece = canonicalRingPieces p := rfl

theorem taggedBulkUnits_pieces (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (taggedBulkUnits p ha).map CappedUnit.piece =
      ReductionTM2.BulkScan.cappedRuntimePieces p.side (by have h := p.side_ge; omega) ha := by
  rw [taggedBulkUnits, List.map_ofFn]
  rfl

theorem canonicalSingletonPieces_pairwise (p : ConstructionParameters) :
    (canonicalSingletonPieces p).Pairwise WordsDisjoint := by
  have hm : 2 ≤ p.side := by have h := p.side_ge; omega
  have h01 := canonicalSingletonPieces_disjoint p.side hm 0 1 (by decide)
  have h02 := canonicalSingletonPieces_disjoint p.side hm 0 2 (by decide)
  have h12 := canonicalSingletonPieces_disjoint p.side hm 1 2 (by decide)
  refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact h01
    · exact h02
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl
    exact h12
  · intro q hq
    cases hq

theorem canonicalSeparatorPieces_pairwise (p : ConstructionParameters) :
    (canonicalSeparatorPieces p).Pairwise WordsDisjoint := by
  apply List.pairwise_ofFn.mpr
  intro k l hkl
  have hk : k.val ≤ p.bins := by have h := k.isLt; omega
  have hl : l.val ≤ p.bins := by have h := l.isLt; omega
  have hne : k.val ≠ l.val := fun h => (ne_of_lt hkl) (Fin.ext h)
  exact cappedSeparatorFolds_disjoint p k.val l.val hk hl hne
    (entryLocalColumn p (some k)) (exitCapColumn p k.val hk)
    (entryLocalColumn p (some l)) (exitCapColumn p l.val hl)
    rfl (exitCapColumn_owner p k.val hk) rfl (exitCapColumn_owner p l.val hl)

noncomputable def canonicalPieceFamilies (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) : List (List PositionedWord) :=
  [canonicalSingletonPieces p, [frameWordPiece p], canonicalSeparatorPieces p,
    [canonicalLeftPiece p], d.taggedItems.map CappedUnit.piece, [canonicalRightPiece p],
    canonicalRingPieces p,
    ReductionTM2.BulkScan.cappedRuntimePieces p.side (by have h := p.side_ge; omega) ha]

theorem canonicalTaggedBodies_pieces_families (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (canonicalTaggedBodies p items d ha).map CappedUnit.piece =
      (canonicalPieceFamilies p items d ha).flatten := by
  simp only [canonicalTaggedBodies, List.map_append, taggedSingletonUnits_pieces,
    taggedSeparatorUnits_pieces, taggedRingUnits_pieces, taggedBulkUnits_pieces,
    List.map_cons, List.map_nil, frameCappedUnit, leftCappedUnit, rightCappedUnit,
    CappedUnit.ofColumns, canonicalPieceFamilies, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem canonicalPieceFamilies_internal (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    ∀ ps ∈ canonicalPieceFamilies p items d ha, ps.Pairwise WordsDisjoint := by
  have hs := canonicalSingletonPieces_pairwise p
  have hf : ([frameWordPiece p] : List PositionedWord).Pairwise WordsDisjoint := List.pairwise_singleton _ _
  have hsep := canonicalSeparatorPieces_pairwise p
  have hl : ([canonicalLeftPiece p] : List PositionedWord).Pairwise WordsDisjoint := List.pairwise_singleton _ _
  have hi := d.taggedItemPieces_pairwise
  have hright : ([canonicalRightPiece p] : List PositionedWord).Pairwise WordsDisjoint := List.pairwise_singleton _ _
  have hr := canonicalRingPieces_pairwise p
  have hb := ReductionTM2.BulkScan.cappedRuntimePieces_pairwise p.side (by have h := p.side_ge; omega) ha
  simpa only [canonicalPieceFamilies, List.forall_mem_cons, list_forall_mem_nil_iff, and_true] using
    And.intro hs (And.intro hf (And.intro hsep (And.intro hl (And.intro hi (And.intro hright (And.intro hr hb))))))

theorem canonicalTaggedBodies_pairwise_of_cross (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hcross : (canonicalPieceFamilies p items d ha).Pairwise
      (fun ps qs => ∀ u ∈ ps, ∀ v ∈ qs, WordsDisjoint u v)) :
    ((canonicalTaggedBodies p items d ha).map CappedUnit.piece).Pairwise WordsDisjoint := by
  rw [canonicalTaggedBodies_pieces_families]
  exact List.pairwise_flatten.mpr ⟨canonicalPieceFamilies_internal p items d ha, hcross⟩

theorem canonicalUnitPieces_pairwise_of_cross (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hterminal : CanonicalLocalProperty p ha (WordsDisjoint (terminalWordPiece p)))
    (hcross : (canonicalPieceFamilies p items d ha).Pairwise
      (fun ps qs => ∀ u ∈ ps, ∀ v ∈ qs, WordsDisjoint u v)) :
    (canonicalUnitPieces p items d ha).Pairwise WordsDisjoint := by
  apply List.pairwise_cons.mpr
  constructor
  · intro q hq
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
    exact canonicalTaggedBodies_property p items d ha
      (WordsDisjoint (terminalWordPiece p)) hterminal u hu
  · exact canonicalTaggedBodies_pairwise_of_cross p items d ha hcross

theorem positionedPieces_get_disjoint (ps : List PositionedWord) (hp : ps.Pairwise WordsDisjoint)
    (i j : Fin ps.length) (hne : i ≠ j) : WordsDisjoint (ps.get i) (ps.get j) := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact List.pairwise_iff_get.mp hp i j hij
  · exact (List.pairwise_iff_get.mp hp j i hji).symm

theorem canonicalUnitAt_disjoint_of_pairwise (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : (canonicalUnitPieces p items d ha).Pairwise WordsDisjoint)
    (i j : Fin ((p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length + 1))
    (hne : i ≠ j) : WordsDisjoint (canonicalUnitAt p items d ha i) (canonicalUnitAt p items d ha j) := by
  apply positionedPieces_get_disjoint _ hp
    (Fin.cast (canonicalUnitPieces_length p items d ha).symm i)
    (Fin.cast (canonicalUnitPieces_length p items d ha).symm j)
  intro heq
  have hv := congrArg Fin.val heq
  change i.val = j.val at hv
  exact hne (Fin.ext hv)

end ProteinFolding.Tetrahedral.NearField

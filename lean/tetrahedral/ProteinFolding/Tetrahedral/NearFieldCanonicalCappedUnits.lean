import ProteinFolding.Tetrahedral.NearFieldCanonicalBasePieces
import ProteinFolding.Tetrahedral.NearFieldCappedUnitData

/-! Actual capped body units retain their selected routing columns. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 500000
set_option maxRecDepth 4096

noncomputable def singletonCappedUnit (p : ConstructionParameters) (i : Fin 3) : CappedUnit p.side :=
  .ofColumns [Residue.H] (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) i) rfl
    (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) i false)
    (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) i true) rfl rfl

noncomputable def frameCappedUnit (p : ConstructionParameters) : CappedUnit p.side :=
  .ofColumns (p.framePart1 ++ p.framePart2) (frameWordPiece p) (frameWordPiece_word p)
    (frameFirstColumn p) (frameLastColumn p) rfl rfl

noncomputable def separatorCappedUnit (p : ConstructionParameters) (k : Fin (p.bins + 1)) : CappedUnit p.side where
  body := p.separatorWord k.val
  piece := canonicalSeparatorPiece p k
  word_eq := rfl
  entry := selectedEntryColumn p (some k)
  exit := exitCapColumn p k.val (by have h := k.isLt; omega)
  first_dangling := entryCapSite_dangling p (some k)
  last_dangling := (exitCapColumn p k.val (by have h := k.isLt; omega)).seed_dangling
  first_adjacent := entryCapSite_adj_columnOne p (some k)
  last_adjacent := (exitCapColumn p k.val (by have h := k.isLt; omega)).point_adj 0

noncomputable def leftCappedUnit (p : ConstructionParameters) : CappedUnit p.side where
  body := dimerChain p.leftFiller
  piece := canonicalLeftPiece p
  word_eq := rfl
  entry := selectedEntryColumn p none
  exit := leftLastColumn p
  first_dangling := entryCapSite_dangling p none
  last_dangling := (leftLastColumn p).seed_dangling
  first_adjacent := entryCapSite_adj_columnOne p none
  last_adjacent := (leftLastColumn p).point_adj 0

noncomputable def itemCappedUnit (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) : CappedUnit p.side :=
  .ofColumns (dimerChain (p.itemDimers s)) (canonicalItemPiece p k before s hk hs hload) rfl
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload) rfl rfl

noncomputable def rightCappedUnit (p : ConstructionParameters) : CappedUnit p.side :=
  .ofColumns (dimerChain p.rightFiller) (canonicalRightPiece p) rfl
    (rightFirstColumn p) (rightFinalColumn p) rfl rfl

noncomputable def ringCappedUnit (p : ConstructionParameters) (i : Fin 3) : CappedUnit p.side :=
  .ofColumns (dimerChain (3 * (p.side - 2))) (canonicalRingWordPiece p i) rfl
    (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
    (canonicalRingWordPiece_first p i) (canonicalRingWordPiece_last p i)

noncomputable def bulkCappedUnit (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) : CappedUnit p.side :=
  .ofColumns (List.replicate ((ReductionTM2.BulkScan.lengths p.side).get j) Residue.H)
    (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j) rfl
    (ReductionTM2.BulkScan.firstColumn p.side (by have h := p.side_ge; omega) ha j)
    (ReductionTM2.BulkScan.lastColumn p.side (by have h := p.side_ge; omega) ha j) rfl rfl

private theorem ofColumns_body_eq {m : ℕ} (body : Sequence) (piece : PositionedWord)
    (hword : piece.word = capWord body) (C D : DanglingColumn m)
    (hf : piece.first = C.seed) (hl : piece.last = D.seed) :
    (CappedUnit.ofColumns body piece hword C D hf hl).body = body := rfl

private theorem bulkCappedUnit_body (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) :
    (bulkCappedUnit p ha j).body = List.replicate ((ReductionTM2.BulkScan.lengths p.side).get j) Residue.H := by
  dsimp only [bulkCappedUnit]
  with_reducible
    exact ofColumns_body_eq (m := p.side) _ _ rfl
      (ReductionTM2.BulkScan.firstColumn p.side (by have h := p.side_ge; omega) ha j)
      (ReductionTM2.BulkScan.lastColumn p.side (by have h := p.side_ge; omega) ha j) rfl rfl

noncomputable def PackedBins.taggedBinUnits {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (k : Fin d.parts.length) : List (CappedUnit p.side) :=
  List.ofFn (fun i : Fin (d.parts.get k).length => itemCappedUnit p k.val
    (itemPrefix (d.parts.get k) i) ((d.parts.get k).get i) (d.bin_lt k)
    (d.part_positive k _ (List.get_mem _ _))
    (by rw [← d.part_load k]; exact itemPrefix_load (d.parts.get k) i))

theorem PackedBins.taggedBinUnits_bodies {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (k : Fin d.parts.length) :
    (d.taggedBinUnits k).map CappedUnit.body = (d.parts.get k).map (fun s => dimerChain (p.itemDimers s)) := by
  have he := congrArg (List.map (fun s => dimerChain (p.itemDimers s))) (List.ofFn_get (d.parts.get k))
  rw [List.map_ofFn] at he
  rw [taggedBinUnits, List.map_ofFn]
  change List.ofFn (fun i : Fin (d.parts.get k).length =>
    dimerChain (p.itemDimers ((d.parts.get k).get i))) = _
  simpa only [Function.comp_def] using he

noncomputable def PackedBins.taggedPlacedUnits {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : List (CappedUnit p.side) :=
  (List.finRange d.parts.length).flatMap d.taggedBinUnits

theorem PackedBins.taggedPlacedUnits_bodies {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) :
    d.taggedPlacedUnits.map CappedUnit.body = d.parts.flatten.map (fun s => dimerChain (p.itemDimers s)) := by
  simp only [taggedPlacedUnits, List.map_flatMap, taggedBinUnits_bodies]
  have he := congrArg
    (fun parts : List (List ℕ) => parts.flatMap (fun part => part.map (fun s => dimerChain (p.itemDimers s))))
    (List.finRange_map_get d.parts)
  dsimp only at he
  rw [List.flatMap_map] at he
  simpa only [List.flatMap_def, List.map_flatten] using he

noncomputable def PackedBins.taggedReordered {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : ReorderedCappedBodies d.taggedPlacedUnits
      (items.map (fun s => dimerChain (p.itemDimers s))) :=
  reorderCappedBodies d.taggedPlacedUnits _ (by rw [d.taggedPlacedUnits_bodies]; exact d.perm.map _)

noncomputable def PackedBins.taggedItems {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : List (CappedUnit p.side) := d.taggedReordered.units

theorem PackedBins.taggedItems_bodies {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) : d.taggedItems.map CappedUnit.body = items.map (fun s => dimerChain (p.itemDimers s)) :=
  d.taggedReordered.bodies_eq

theorem PackedBins.taggedItems_property {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (P : PositionedWord → Prop)
    (h : ∀ k : Fin d.parts.length, ∀ i : Fin (d.parts.get k).length,
      P (packedItemPiece p k.val (d.bin_lt k) (d.parts.get k) (d.part_positive k) (d.part_load k) i)) :
    ∀ u ∈ d.taggedItems, P u.piece := by
  apply d.taggedReordered.property (fun u => P u.piece)
  intro u hu
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hu
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
  exact h k i

theorem PackedBins.taggedItems_selectedProperty {p : ConstructionParameters} {items : List ℕ}
    (d : PackedBins p items) (Q : CappedUnit p.side → Prop)
    (h : ∀ k : Fin d.parts.length, ∀ i : Fin (d.parts.get k).length,
      Q (itemCappedUnit p k.val (itemPrefix (d.parts.get k) i) ((d.parts.get k).get i) (d.bin_lt k)
        (d.part_positive k _ (List.get_mem _ _))
        (by rw [← d.part_load k]; exact itemPrefix_load (d.parts.get k) i))) :
    ∀ u ∈ d.taggedItems, Q u := by
  apply d.taggedReordered.property Q
  intro u hu
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hu
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
  exact h k i

noncomputable def taggedSingletonUnits (p : ConstructionParameters) : List (CappedUnit p.side) :=
  [singletonCappedUnit p 0, singletonCappedUnit p 1, singletonCappedUnit p 2]

noncomputable def taggedSeparatorUnits (p : ConstructionParameters) : List (CappedUnit p.side) :=
  List.ofFn (separatorCappedUnit p)

noncomputable def taggedRingUnits (p : ConstructionParameters) : List (CappedUnit p.side) :=
  [ringCappedUnit p 0, ringCappedUnit p 1, ringCappedUnit p 2]

noncomputable def taggedBulkUnits (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    List (CappedUnit p.side) := List.ofFn (bulkCappedUnit p ha)

theorem taggedSeparatorUnits_bodies (p : ConstructionParameters) :
    (taggedSeparatorUnits p).map CappedUnit.body = (List.range (p.bins + 1)).map p.separatorWord := by
  rw [taggedSeparatorUnits, List.map_ofFn, List.ofFn_eq_map]
  have he := congrArg (List.map p.separatorWord) (List.map_coe_finRange (p.bins + 1))
  simpa only [List.map_map, Function.comp_def] using he

theorem taggedBulkUnits_bodies (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (taggedBulkUnits p ha).map CappedUnit.body =
      (ReductionTM2.BulkScan.lengths p.side).map (fun n => List.replicate n Residue.H) := by
  have he := congrArg (List.map (fun n => List.replicate n Residue.H))
    (List.ofFn_get (ReductionTM2.BulkScan.lengths p.side))
  rw [List.map_ofFn] at he
  rw [taggedBulkUnits, List.map_ofFn]
  simpa only [Function.comp_def, bulkCappedUnit_body] using he

noncomputable def canonicalTaggedBodies (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) : List (CappedUnit p.side) :=
  taggedSingletonUnits p ++ [frameCappedUnit p] ++ taggedSeparatorUnits p ++ [leftCappedUnit p] ++
    d.taggedItems ++ [rightCappedUnit p] ++ taggedRingUnits p ++ taggedBulkUnits p ha

theorem canonicalTaggedBodies_bodies (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (canonicalTaggedBodies p items d ha).map CappedUnit.body =
      p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side) := by
  simp only [canonicalTaggedBodies, List.map_append, List.map_cons, List.map_nil,
    taggedSingletonUnits, taggedRingUnits, taggedSeparatorUnits_bodies, taggedBulkUnits_bodies,
    d.taggedItems_bodies, singletonCappedUnit, frameCappedUnit, leftCappedUnit, rightCappedUnit,
    ringCappedUnit, CappedUnit.ofColumns, ConstructionParameters.reductionUnitBodies,
    List.replicate_succ, List.replicate_zero, List.append_assoc, List.cons_append, List.nil_append]

structure CanonicalLocalProperty (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (P : PositionedWord → Prop) : Prop where
  singleton : ∀ i : Fin 3, P (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) i)
  frame : P (frameWordPiece p)
  separator : ∀ k : Fin (p.bins + 1), P (canonicalSeparatorPiece p k)
  left : P (canonicalLeftPiece p)
  item : ∀ k before s, ∀ hk : k < p.bins, ∀ hs : 0 < s, ∀ hload : before + s ≤ p.capacity,
    P (canonicalItemPiece p k before s hk hs hload)
  right : P (canonicalRightPiece p)
  ring : ∀ i : Fin 3, P (canonicalRingWordPiece p i)
  bulk : ∀ j : Fin (ReductionTM2.BulkScan.lengths p.side).length,
    P (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j)

theorem canonicalTaggedBodies_property (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) (P : PositionedWord → Prop)
    (h : CanonicalLocalProperty p ha P) :
    ∀ u ∈ canonicalTaggedBodies p items d ha, P u.piece := by
  have hs : ∀ u ∈ taggedSingletonUnits p, P u.piece := by
    intro u hu
    simp only [taggedSingletonUnits, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact h.singleton 0
    · exact h.singleton 1
    · exact h.singleton 2
  have hsep : ∀ u ∈ taggedSeparatorUnits p, P u.piece := by
    intro u hu
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hu
    exact h.separator k
  have hi : ∀ u ∈ d.taggedItems, P u.piece := by
    apply d.taggedItems_property P
    intro k i
    exact h.item k.val (itemPrefix (d.parts.get k) i) ((d.parts.get k).get i) (d.bin_lt k)
      (d.part_positive k _ (List.get_mem _ _))
      (by rw [← d.part_load k]; exact itemPrefix_load (d.parts.get k) i)
  have hr : ∀ u ∈ taggedRingUnits p, P u.piece := by
    intro u hu
    simp only [taggedRingUnits, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact h.ring 0
    · exact h.ring 1
    · exact h.ring 2
  have hb : ∀ u ∈ taggedBulkUnits p ha, P u.piece := by
    intro u hu
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
    exact h.bulk j
  intro u hu
  simp only [canonicalTaggedBodies, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu
  rcases hu with hu | rfl | hu | rfl | hu | rfl | hu | hu
  · exact hs u hu
  · exact h.frame
  · exact hsep u hu
  · exact h.left
  · exact hi u hu
  · exact h.right
  · exact hr u hu
  · exact hb u hu

structure CanonicalTaggedProperty (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (Q : CappedUnit p.side → Prop) : Prop where
  singleton : ∀ i : Fin 3, Q (singletonCappedUnit p i)
  frame : Q (frameCappedUnit p)
  separator : ∀ k : Fin (p.bins + 1), Q (separatorCappedUnit p k)
  left : Q (leftCappedUnit p)
  item : ∀ k before s, ∀ hk : k < p.bins, ∀ hs : 0 < s, ∀ hload : before + s ≤ p.capacity,
    Q (itemCappedUnit p k before s hk hs hload)
  right : Q (rightCappedUnit p)
  ring : ∀ i : Fin 3, Q (ringCappedUnit p i)
  bulk : ∀ j : Fin (ReductionTM2.BulkScan.lengths p.side).length, Q (bulkCappedUnit p ha j)

theorem canonicalTaggedBodies_selectedProperty (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) (Q : CappedUnit p.side → Prop)
    (h : CanonicalTaggedProperty p ha Q) : ∀ u ∈ canonicalTaggedBodies p items d ha, Q u := by
  have hs : ∀ u ∈ taggedSingletonUnits p, Q u := by
    intro u hu
    simp only [taggedSingletonUnits, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact h.singleton 0
    · exact h.singleton 1
    · exact h.singleton 2
  have hsep : ∀ u ∈ taggedSeparatorUnits p, Q u := by
    intro u hu
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hu
    exact h.separator k
  have hi : ∀ u ∈ d.taggedItems, Q u := by
    apply d.taggedItems_selectedProperty Q
    intro k i
    exact h.item k.val (itemPrefix (d.parts.get k) i) ((d.parts.get k).get i) (d.bin_lt k)
      (d.part_positive k _ (List.get_mem _ _))
      (by rw [← d.part_load k]; exact itemPrefix_load (d.parts.get k) i)
  have hr : ∀ u ∈ taggedRingUnits p, Q u := by
    intro u hu
    simp only [taggedRingUnits, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact h.ring 0
    · exact h.ring 1
    · exact h.ring 2
  have hb : ∀ u ∈ taggedBulkUnits p ha, Q u := by
    intro u hu
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
    exact h.bulk j
  intro u hu
  simp only [canonicalTaggedBodies, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hu
  rcases hu with hu | rfl | hu | rfl | hu | rfl | hu | hu
  · exact hs u hu
  · exact h.frame
  · exact hsep u hu
  · exact h.left
  · exact hi u hu
  · exact h.right
  · exact hr u hu
  · exact hb u hu

end ProteinFolding.Tetrahedral.NearField

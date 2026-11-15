import ProteinFolding.Tetrahedral.NearFieldCanonicalUnits
import ProteinFolding.Tetrahedral.NearFieldLeftFillerBounds
import ProteinFolding.Tetrahedral.NearFieldUnitSeparatorSupport
import ProteinFolding.Tetrahedral.FarFieldCoordinates

/-! Support, lengths and locality of the actual canonical local words. The
list interfaces preserve their occurrences through the tagged item reorder. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem positionedWord_solid_mono (m s t : ℕ) (q : PositionedWord)
    (hst : s ≤ t) (h : ∀ i : Fin q.word.length, q.fold.pos i ∈ skinSolid m s) :
    ∀ i : Fin q.word.length, q.fold.pos i ∈ skinSolid m t := by
  intro i
  exact skinSolid_mono m hst (h i)

private theorem cappedBulk_hSupport_subset_oct (m : ℕ) (hm : 27 ≤ m)
    (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths m).length) :
    hSupport (ReductionTM2.BulkScan.cappedRuntimePiece m hm ha j).word
      (ReductionTM2.BulkScan.cappedRuntimePiece m hm ha j).fold ⊆ octahedron m := by
  have h := ReductionTM2.BulkScan.cappedRuntimePieceWithColumns_hSupport_inside m hm ha j
    (ReductionTM2.BulkScan.firstColumn m hm ha j)
    (ReductionTM2.BulkScan.lastColumn m hm ha j) rfl rfl
  intro x hx
  exact (Finset.mem_sdiff.mp (h hx)).1

private theorem cappedBulk_mem_solid_one (m : ℕ) (hm : 27 ≤ m)
    (ha : (bulkFiniteGraph m).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths m).length)
    (i : Fin (ReductionTM2.BulkScan.cappedRuntimePiece m hm ha j).word.length) :
    (ReductionTM2.BulkScan.cappedRuntimePiece m hm ha j).fold.pos i ∈ skinSolid m 1 :=
  ReductionTM2.BulkScan.cappedRuntimePieceWithColumns_mem_solid_one m hm ha j
    (ReductionTM2.BulkScan.firstColumn m hm ha j)
    (ReductionTM2.BulkScan.lastColumn m hm ha j) rfl rfl i

theorem terminalWordPiece_mem_solid_one (p : ConstructionParameters)
    (i : Fin (terminalWordPiece p).word.length) :
    (terminalWordPiece p).fold.pos i ∈ skinSolid p.side 1 := by
  change (if i.val = 0 then (terminalColumn p).owner else (terminalColumn p).seed) ∈ _
  split_ifs
  · apply skinSolid_mono p.side (by omega : 0 ≤ 1)
    rw [skinSolid_zero]
    exact (terminalColumn p).owner_mem
  · exact (terminalColumn p).point_zero_mem_solid_one

theorem canonicalSeparatorPiece_hSupport (p : ConstructionParameters) (k : Fin (p.bins + 1)) :
    hSupport (canonicalSeparatorPiece p k).word (canonicalSeparatorPiece p k).fold ⊆
      octahedron p.side :=
  separatorWordPiece_hSupport_subset_oct p k.val (by have h := k.isLt; omega)
    _ _ rfl (exitCapColumn_owner p k.val (by have h := k.isLt; omega))

theorem canonicalSeparatorPiece_mem_solid (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (i : Fin (canonicalSeparatorPiece p k).word.length) :
    (canonicalSeparatorPiece p k).fold.pos i ∈ skinSolid p.side (2 * p.bins + 3) :=
  cappedSeparatorFold_mem_solid p k.val (by have h := k.isLt; omega)
    _ _ rfl (exitCapColumn_owner p k.val (by have h := k.isLt; omega)) i

theorem leftFillerWordPiece_mem_solid_one (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2))
    (i : Fin (leftFillerWordPiece p C D hC hD).word.length) :
    (leftFillerWordPiece p C D hC hD).fold.pos i ∈ skinSolid p.side 1 := by
  have hmem := (mem_foldSites (leftFillerWordPiece p C D hC hD).fold _).mpr ⟨i, rfl⟩
  change (leftFillerWordPiece p C D hC hD).fold.pos i ∈
    foldSites (cappedLeftFillerFold p C D hC hD) at hmem
  rw [cappedLeftFillerFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]
    exact C.point_zero_mem_solid_one
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    rw [← hj]
    exact leftFillerFold_mem_solid_one p j
  · rw [h]
    exact D.point_zero_mem_solid_one

theorem canonicalLeftPiece_mem_solid_one (p : ConstructionParameters)
    (i : Fin (canonicalLeftPiece p).word.length) :
    (canonicalLeftPiece p).fold.pos i ∈ skinSolid p.side 1 :=
  leftFillerWordPiece_mem_solid_one p _ _ rfl (leftLastColumn_owner p) i

theorem canonicalItemPiece_mem_solid_one (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ∈ skinSolid p.side 1 :=
  cappedIntervalDimerFold_mem_solid_one (m := p.side) (by have h := p.side_ge; omega)
    trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s)
    (by have h := p.itemDimers_ge s hs; omega) false
    (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload) i

theorem canonicalRightPiece_mem_solid_one (p : ConstructionParameters)
    (i : Fin (canonicalRightPiece p).word.length) :
    (canonicalRightPiece p).fold.pos i ∈ skinSolid p.side 1 :=
  cappedIntervalDimerFold_mem_solid_one (m := p.side) (by have h := p.side_ge; omega)
    trackEdgeFrame (rightFillerTrackBase p) p.rightFiller
    (by have h := p.rightFiller_ge; omega) false (rightFillerTrackBase_room p)
    (rightFirstColumn p) (rightFinalColumn p) rfl
    (by
      rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
      have he : rightFillerTrackBase p + 2 * p.rightFiller - 1 = 2 * p.side - 3 := by
        have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
        dsimp [rightFillerTrackBase]
        omega
      rw [he]
      exact rightFinalColumn_track_owner p) i

theorem canonicalBulkPiece_hSupport (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length) :
    hSupport (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).word
      (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).fold ⊆
        octahedron p.side := by
  with_reducible
    exact cappedBulk_hSupport_subset_oct p.side
      (by have h := p.side_ge; omega) ha j

theorem canonicalBulkPiece_mem_solid_one (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (j : Fin (ReductionTM2.BulkScan.lengths p.side).length)
    (i : Fin (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).word.length) :
    (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j).fold.pos i ∈
      skinSolid p.side 1 := by
  with_reducible
    exact cappedBulk_mem_solid_one p.side
      (by have h := p.side_ge; omega) ha j i

theorem canonicalUnit_solid_rho_bound (p : ConstructionParameters) (x : Site)
    (hx : x ∈ skinSolid p.side (2 * p.bins + 3)) :
    FarField.rho (octRadius p.side) x < 20 * (p.side : ℤ) + 21 := by
  have hr := skinSolid_rho_bound p.side (2 * p.bins + 3) hx
  change FarField.rho (octRadius p.side) x ≤ 2 * ((p.side + 2 * (2 * p.bins + 3) : ℕ) : ℤ) at hr
  push_cast at hr
  have hb : p.bins ≤ p.side := by
    have h := p.family_side_bound
    omega
  have hbZ : (p.bins : ℤ) ≤ (p.side : ℤ) := by exact_mod_cast hb
  omega

theorem canonicalLocal_hSupport (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    CanonicalLocalProperty p ha (fun q => hSupport q.word q.fold ⊆ octahedron p.side) := {
  singleton := fun i => canonicalSingletonPiece_hSupport_subset p.side
    (by have h := p.side_ge; omega) i
  frame := frameFold_hSupport_subset_oct p
  separator := canonicalSeparatorPiece_hSupport p
  left := canonicalLeftPiece_hSupport p
  item := canonicalItemPiece_hSupport p
  right := canonicalRightPiece_hSupport p
  ring := canonicalRingWordPiece_hSupport_subset_oct p
  bulk := canonicalBulkPiece_hSupport p ha }

theorem canonicalLocal_mem_solid (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    CanonicalLocalProperty p ha (fun q => ∀ i : Fin q.word.length,
      q.fold.pos i ∈ skinSolid p.side (2 * p.bins + 3)) := by
  have hdepth : 1 ≤ 2 * p.bins + 3 := by omega
  have hframe : ∀ i : Fin (frameWordPiece p).word.length,
      (frameWordPiece p).fold.pos i ∈ skinSolid p.side 1 := by
    change ∀ i : Fin p.frameWord.length, (frameFold p).pos i ∈ skinSolid p.side 1
    with_reducible exact frameFold_mem_solid_one p
  with_reducible
    exact {
      singleton := fun r => positionedWord_solid_mono p.side 1 (2 * p.bins + 3)
        (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) r) hdepth
        (canonicalSingletonPiece_mem_solid_one p.side (by have h := p.side_ge; omega) r)
      frame := positionedWord_solid_mono p.side 1 (2 * p.bins + 3)
        (frameWordPiece p) hdepth hframe
      separator := canonicalSeparatorPiece_mem_solid p
      left := positionedWord_solid_mono p.side 1 (2 * p.bins + 3)
        (canonicalLeftPiece p) hdepth (canonicalLeftPiece_mem_solid_one p)
      item := fun k before s hk hs hload => positionedWord_solid_mono p.side 1 (2 * p.bins + 3)
        (canonicalItemPiece p k before s hk hs hload) hdepth
        (canonicalItemPiece_mem_solid_one p k before s hk hs hload)
      right := positionedWord_solid_mono p.side 1 (2 * p.bins + 3)
        (canonicalRightPiece p) hdepth (canonicalRightPiece_mem_solid_one p)
      ring := fun r => positionedWord_solid_mono p.side 1 (2 * p.bins + 3)
        (canonicalRingWordPiece p r) hdepth (canonicalRingWordPiece_mem_solid_one p r)
      bulk := fun j => positionedWord_solid_mono p.side 1 (2 * p.bins + 3)
        (ReductionTM2.BulkScan.cappedRuntimePiece p.side (by have h := p.side_ge; omega) ha j)
        hdepth (canonicalBulkPiece_mem_solid_one p ha j) }

theorem canonicalUnitPieces_hSupport_subset_oct (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha) :
    hSupport q.word q.fold ⊆ octahedron p.side :=
  canonicalUnitPieces_property p items d ha _ (terminalWordPiece_hSupport_subset_oct p)
    (canonicalLocal_hSupport p ha) q hq

theorem canonicalUnitPieces_hSupport (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    pieceHsupport (canonicalUnitPieces p items d ha) ⊆ octahedron p.side := by
  intro x hx
  obtain ⟨q, hq, hH⟩ := (ReductionTM2.BulkScan.mem_pieceHsupport _ _).mp hx
  exact canonicalUnitPieces_hSupport_subset_oct p items d ha q hq hH

theorem canonicalUnitPieces_mem_solid (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha)
    (i : Fin q.word.length) : q.fold.pos i ∈ skinSolid p.side (2 * p.bins + 3) := by
  apply canonicalUnitPieces_property p items d ha
    (fun q => ∀ i : Fin q.word.length, q.fold.pos i ∈ skinSolid p.side (2 * p.bins + 3))
    _ (canonicalLocal_mem_solid p ha) q hq i
  intro j
  exact skinSolid_mono p.side (by omega : 1 ≤ 2 * p.bins + 3)
    (terminalWordPiece_mem_solid_one p j)

theorem canonicalUnitPieces_sites_mem_solid (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha)
    (x : Site) (hx : x ∈ foldSites q.fold) : x ∈ skinSolid p.side (2 * p.bins + 3) := by
  obtain ⟨i, rfl⟩ := (mem_foldSites q.fold x).mp hx
  exact canonicalUnitPieces_mem_solid p items d ha q hq i

theorem canonicalUnitPieces_rho_bound (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha)
    (x : Site) (hx : x ∈ foldSites q.fold) :
    FarField.rho (octRadius p.side) x < 20 * (p.side : ℤ) + 21 :=
  canonicalUnit_solid_rho_bound p x (canonicalUnitPieces_sites_mem_solid p items d ha q hq x hx)

theorem canonicalUnitPieces_length_ge_two (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha) : 2 ≤ q.word.length := by
  have hw : q.word ∈ (canonicalUnitPieces p items d ha).map PositionedWord.word :=
    List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [canonicalUnitPieces_words] at hw
  rcases List.mem_cons.mp hw with hw | hw
  · rw [hw]
    decide
  · obtain ⟨body, _, hbody⟩ := List.mem_map.mp hw
    rw [← hbody]
    simp only [capWord, List.length_cons, List.length_append]
    omega

theorem canonicalUnitAt_mem (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin ((p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length + 1)) :
    canonicalUnitAt p items d ha i ∈ canonicalUnitPieces p items d ha :=
  List.get_mem _ _

theorem canonicalUnitAt_property (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (P : PositionedWord → Prop) (hP : ∀ q ∈ canonicalUnitPieces p items d ha, P q)
    (i : Fin ((p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length + 1)) :
    P (canonicalUnitAt p items d ha i) :=
  hP _ (canonicalUnitAt_mem p items d ha i)

theorem canonicalUnitAt_length_ge_two (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin ((p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length + 1)) :
    2 ≤ (canonicalUnitAt p items d ha i).word.length :=
  canonicalUnitPieces_length_ge_two p items d ha _ (canonicalUnitAt_mem p items d ha i)

theorem canonicalUnitAt_hSupport_subset_oct (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin ((p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length + 1)) :
    hSupport (canonicalUnitAt p items d ha i).word (canonicalUnitAt p items d ha i).fold ⊆
      octahedron p.side :=
  canonicalUnitPieces_hSupport_subset_oct p items d ha _ (canonicalUnitAt_mem p items d ha i)

theorem canonicalUnitAt_mem_solid (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin ((p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length + 1))
    (j : Fin (canonicalUnitAt p items d ha i).word.length) :
    (canonicalUnitAt p items d ha i).fold.pos j ∈ skinSolid p.side (2 * p.bins + 3) :=
  canonicalUnitPieces_mem_solid p items d ha _ (canonicalUnitAt_mem p items d ha i) j

theorem canonicalUnitAt_sites_mem_solid (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin ((p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length + 1))
    (x : Site) (hx : x ∈ foldSites (canonicalUnitAt p items d ha i).fold) :
    x ∈ skinSolid p.side (2 * p.bins + 3) :=
  canonicalUnitPieces_sites_mem_solid p items d ha _ (canonicalUnitAt_mem p items d ha i) x hx

theorem canonicalUnitAt_rho_bound (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i : Fin ((p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length + 1))
    (x : Site) (hx : x ∈ foldSites (canonicalUnitAt p items d ha i).fold) :
    FarField.rho (octRadius p.side) x < 20 * (p.side : ℤ) + 21 :=
  canonicalUnitPieces_rho_bound p items d ha _ (canonicalUnitAt_mem p items d ha i) x hx

theorem canonicalUnitAt_list (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    List.ofFn (canonicalUnitAt p items d ha) = canonicalUnitPieces p items d ha := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, canonicalUnitPieces_length]
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

theorem canonicalUnitAt_words (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (List.ofFn (canonicalUnitAt p items d ha)).map PositionedWord.word = [.H, .P] ::
      (p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).map capWord := by
  rw [canonicalUnitAt_list]
  exact canonicalUnitPieces_words p items d ha

end ProteinFolding.Tetrahedral.NearField

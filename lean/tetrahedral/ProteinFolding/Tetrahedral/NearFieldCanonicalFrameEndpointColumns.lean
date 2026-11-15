import ProteinFolding.Tetrahedral.NearFieldCanonicalRingBulkColumns

/-! Both free frame endpoint columns avoid every complete canonical unit
at positive height, including all polar link and tether sites. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem dimerLinkIndex_pos_of_base_or_forward (base : ℕ) (reverse : Bool) (j : ℕ)
    (hlo : 1 ≤ base ∨ reverse = false) : 1 ≤ dimerLinkIndex base reverse j := by
  have hb := dimerLinkIndex_bounds base reverse j
  rcases hlo with hlo | rfl
  · omega
  · by_cases hj : j = 0
    · subst j
      dsimp [dimerLinkIndex, dimerFlip]
      omega
    · omega

theorem edgePPPFold_ne_frameEndpointColumn (p : ConstructionParameters) (F : OctEdgeFrame)
    (r : ℕ) (hlo : 1 ≤ r) (hhi : r + 4 ≤ 2 * p.side - 1)
    (atStart : Bool) (s : Fin 3) (n : ℕ) :
    (edgePPPFold p.side F r).pos s ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  cases atStart
  · exact edgePPPFold_ne_vertex_column p.side hm F r (by omega)
      (frameEndpointColumn (m := p.side) (by omega) false) 0 true rfl
      (ringEdgePoint_ne_vertex p.side hm F r hlo (by omega) 0 true).symm
      (ringEdgePoint_ne_vertex p.side hm F (r + 2) (by omega) hhi 0 true).symm s n
  · exact edgePPPFold_ne_vertex_column p.side hm F r (by omega)
      (frameEndpointColumn (m := p.side) (by omega) true) 2 false rfl
      (ringEdgePoint_ne_vertex p.side hm F r hlo (by omega) 2 false).symm
      (ringEdgePoint_ne_vertex p.side hm F (r + 2) (by omega) hhi 2 false).symm s n

theorem edgeDimerFold_ne_frameEndpointColumn (p : ConstructionParameters) (F : OctEdgeFrame)
    (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * p.side - 1)
    (hlo : 1 ≤ base ∨ reverse = false) (hhi : base + 2 * (q + 1) + 1 ≤ 2 * p.side - 1)
    (atStart : Bool) (i : Fin (dimerChain (q + 1)).length) (n : ℕ) :
    (edgeDimerFold (by have h := p.side_ge; omega : 1 ≤ p.side) F base q reverse hroom).pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n := by
  apply edgeDimerFold_ne_column_of_PPP_ne (by have h := p.side_ge; omega : 1 ≤ p.side)
    F base q reverse hroom
    (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart) _ i n
  intro j hj s t
  have hb := dimerLinkIndex_bounds base reverse j
  exact edgePPPFold_ne_frameEndpointColumn p F _
    (dimerLinkIndex_pos_of_base_or_forward base reverse j hlo) (by omega) atStart s t

theorem cappedInterval_ne_frameEndpointColumn (p : ConstructionParameters) (F : OctEdgeFrame)
    (base n : ℕ) (hn : 0 < n) (reverse : Bool) (hroom : base + 2 * n ≤ 2 * p.side - 1)
    (hlo : 1 ≤ base ∨ reverse = false) (hhi : base + 2 * n + 1 ≤ 2 * p.side - 1)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (n - 1) 1))
    (atStart : Bool) (t : ℕ) (ht : 1 ≤ t) (i : Fin (capWord (dimerChain n)).length) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      F base n hn reverse hroom C D hC hD).pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point t := by
  apply transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold (by have h := p.side_ge; omega : 1 ≤ p.side)
      F base (n - 1) reverse (by omega) C D hC hD)
    (fun x => x ≠ (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point t) _ i
  exact cappedEdgeDimerFold_property (by have h := p.side_ge; omega : 1 ≤ p.side)
    F base (n - 1) reverse (by omega) C D hC hD
    (fun x => x ≠ (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point t)
    (FarField.dangling_ne_positive_column C.seed_dangling _ t ht)
    (fun j => edgeDimerFold_ne_frameEndpointColumn p F base (n - 1) reverse (by omega) hlo (by omega) atStart j t)
    (FarField.dangling_ne_positive_column D.seed_dangling _ t ht)

theorem canonicalItemPiece_ne_frameEndpointColumn (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (atStart : Bool) (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n := by
  have hend := itemTrackBase_end_le p k before s hload
  have hmono := p.separatorIndex_mono (show k + 1 ≤ p.bins by omega)
  have hside : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
  have hright := p.rightFiller_ge
  exact cappedInterval_ne_frameEndpointColumn p trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s)
    (by have h := p.itemDimers_ge s hs; omega) false (itemTrackBase_room p k before s hk hload)
    (Or.inr rfl) (by omega)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload) atStart n hn i

theorem canonicalRightPiece_ne_frameEndpointColumn (p : ConstructionParameters)
    (atStart : Bool) (n : ℕ) (hn : 1 ≤ n) (i : Fin (canonicalRightPiece p).word.length) :
    (canonicalRightPiece p).fold.pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n := by
  have hside : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
  have hend : rightFillerTrackBase p + 2 * p.rightFiller = 2 * p.side - 2 := by
    dsimp [rightFillerTrackBase]
    omega
  exact cappedInterval_ne_frameEndpointColumn p trackEdgeFrame (rightFillerTrackBase p) p.rightFiller
    (by have h := p.rightFiller_ge; omega) false (rightFillerTrackBase_room p) (Or.inr rfl) (by omega)
    (rightFirstColumn p) (rightFinalColumn p) rfl
    (by
      rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
      have he : rightFillerTrackBase p + 2 * p.rightFiller - 1 = 2 * p.side - 3 := by omega
      rw [he]
      exact rightFinalColumn_track_owner p) atStart n hn i

theorem leftFillerFold_ne_frameEndpointColumn (p : ConstructionParameters)
    (atStart : Bool) (i : Fin (dimerChain p.leftFiller).length) (n : ℕ) :
    (leftFillerFold p).pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n := by
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hi
  · intro heq
    exact (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point_outside n
      (heq ▸ leftFillerStart_mem_oct p)
  · let j : Fin (dimerChain (p.leftFiller - 1 + 1)).length :=
      ⟨i.val, by
        have hlen := dimerChain_succ_length (p.leftFiller - 1)
        have hword := leftFiller_word_length p
        have hi := i.isLt
        omega⟩
    have hside := p.side_eq_track
    have hpos := p.leftFiller_ge
    have h := edgeDimerFold_ne_frameEndpointColumn p trackEdgeFrame 0 (p.leftFiller - 1) false
      (leftFiller_room p) (Or.inr rfl) (by omega) atStart j n
    rw [edgeDimerFold_pos] at h
    exact h

theorem canonicalLeftPiece_ne_frameEndpointColumn (p : ConstructionParameters)
    (atStart : Bool) (n : ℕ) (hn : 1 ≤ n) (i : Fin (canonicalLeftPiece p).word.length) :
    (canonicalLeftPiece p).fold.pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n :=
  frameTrack_property_of_capped_sites _ _ _ _
    (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p))
    (fun x => x ≠ (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n)
    (FarField.dangling_ne_positive_column (entryLocalColumn p none).seed_dangling _ n hn)
    (fun j => leftFillerFold_ne_frameEndpointColumn p atStart j n)
    (FarField.dangling_ne_positive_column (leftLastColumn p).seed_dangling _ n hn) i

theorem separatorFold_ne_frameEndpointColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (atStart : Bool) (i : Fin (p.separatorWord k).length) (n : ℕ) :
    (separatorFold p k hk).pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n := by
  apply separatorFold_property p k hk
    (fun x => x ≠ (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n)
    _ _ _ _ _ i
  · have hroom := p.entry_column_triangle_room k hk
    intro j
    exact edgeDimerFold_ne_frameEndpointColumn p entryEdgeFrame (6 * (k + 1)) 0 false
      (separatorEntry_room p k hk) (Or.inr rfl) (by omega) atStart
      j n
  · intro j
    rw [entryTetherWordFold_pos]
    exact (entryTetherFold_positive p k hk ⟨j.val, by simpa using j.isLt⟩).ne_frameEndpointColumn
      (by have h := p.side_ge; omega) atStart n
  · have hroom := p.separator_room k hk
    have hright := p.rightFiller_ge
    intro j
    exact edgeDimerFold_ne_frameEndpointColumn p trackEdgeFrame (2 * p.separatorIndex k) 1 true
      (separatorCenter_room p k hk) (Or.inl (by have h := separatorIndex_ge_two p k; omega))
      (by omega) atStart j n
  · intro j
    rw [exitTetherWordFold_pos]
    exact (exitTetherFold_positive p k hk ⟨j.val, by simpa using j.isLt⟩).ne_frameEndpointColumn
      (by have h := p.side_ge; omega) atStart n
  · have hroom := p.exit_column_triangle_room k
    intro j
    exact edgeDimerFold_ne_frameEndpointColumn p exitEdgeFrame (10 * p.exitSlot k + 6) 2 true
      (separatorExit_room p k) (Or.inl (by omega)) (by omega) atStart j n

theorem canonicalSeparatorPiece_ne_frameEndpointColumn (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (atStart : Bool) (n : ℕ) (hn : 1 ≤ n) (i : Fin (canonicalSeparatorPiece p k).word.length) :
    (canonicalSeparatorPiece p k).fold.pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n :=
  frameTrack_property_of_capped_sites _ _ _ _
    (cappedSeparatorFold_sites p k.val (by have h := k.isLt; omega) _ _ rfl
      (exitCapColumn_owner p k.val (by have h := k.isLt; omega)))
    (fun x => x ≠ (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n)
    (FarField.dangling_ne_positive_column (entryLocalColumn p (some k)).seed_dangling _ n hn)
    (fun j => separatorFold_ne_frameEndpointColumn p k.val (by have h := k.isLt; omega) atStart j n)
    (FarField.dangling_ne_positive_column (exitCapColumn p k.val (by have h := k.isLt; omega)).seed_dangling _ n hn) i

theorem canonicalRingWordPiece_ne_frameEndpointColumn (p : ConstructionParameters) (r : Fin 3)
    (atStart : Bool) (i : Fin (canonicalRingWordPiece p r).word.length) (n : ℕ) :
    (canonicalRingWordPiece p r).fold.pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n := by
  cases atStart
  · exact canonicalRingWordPiece_ne_vertexColumn p r
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) false) 0 true rfl i n
  · exact canonicalRingWordPiece_ne_vertexColumn p r
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) true) 2 false rfl i n

theorem canonicalLocal_ne_frameEndpointColumn (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) (atStart : Bool) (n : ℕ) (hn : 1 ≤ n) :
    CanonicalLocalProperty p ha (fun q => ∀ i, q.fold.pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n) where
  singleton r i := canonicalSingletonPiece_ne_positiveColumn p.side (by have h := p.side_ge; omega)
    r (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart) n hn i
  frame i := frameFold_ne_endpointColumn p atStart n hn i
  separator k i := canonicalSeparatorPiece_ne_frameEndpointColumn p k atStart n hn i
  left i := canonicalLeftPiece_ne_frameEndpointColumn p atStart n hn i
  item k before s hk hs hload i := canonicalItemPiece_ne_frameEndpointColumn p k before s hk hs hload atStart n hn i
  right i := canonicalRightPiece_ne_frameEndpointColumn p atStart n hn i
  ring r i := canonicalRingWordPiece_ne_frameEndpointColumn p r atStart i n
  bulk j i := canonicalBulkPiece_ne_positiveColumn p ha j
    (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart) n hn i

theorem canonicalUnitPieces_ne_frameEndpointColumn (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (atStart : Bool) (n : ℕ) (hn : 1 ≤ n)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha) (i : Fin q.word.length) :
    q.fold.pos i ≠ (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n :=
  canonicalUnitPieces_property p items d ha _
    (fun j => terminalWordPiece_ne_positiveColumn p
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart) n hn j)
    (canonicalLocal_ne_frameEndpointColumn p ha atStart n hn) q hq i

theorem canonicalTaggedBody_ne_frameEndpointColumn (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (atStart : Bool) (n : ℕ) (hn : 1 ≤ n)
    (u : CappedUnit p.side) (hu : u ∈ canonicalTaggedBodies p items d ha)
    (i : Fin u.piece.word.length) :
    u.piece.fold.pos i ≠ (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) atStart).point n :=
  canonicalTaggedBodies_property p items d ha _
    (canonicalLocal_ne_frameEndpointColumn p ha atStart n hn) u hu i

end ProteinFolding.Tetrahedral.NearField

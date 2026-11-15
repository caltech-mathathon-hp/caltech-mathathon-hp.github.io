import ProteinFolding.Tetrahedral.NearFieldOrdinaryInnerColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalCappedUnits
import ProteinFolding.Tetrahedral.NearFieldLeftFillerSupport
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonFamily

/-! Inner ordinary columns avoid complete local units once their owners are
excluded from those units' H sites. Frame and tether clearance is geometric. -/

namespace ProteinFolding.Tetrahedral.NearField

attribute [local irreducible] ConstructionParameters.side

private theorem mem_of_eq {A B : Finset Site} {x : Site} (h : A = B) (hx : x ∈ B) : x ∈ A := by
  rw [h]
  exact hx

private theorem not_mem_of_eq {A B : Finset Site} {x : Site} (h : A = B) (hx : x ∉ A) : x ∉ B :=
  fun hm => hx (mem_of_eq h hm)

theorem itemPiece_hSupport_eq (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    hSupport (canonicalItemPiece p k before s hk hs hload).word (canonicalItemPiece p k before s hk hs hload).fold =
      edgeDimerHsites p.side trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s - 1) :=
  cappedIntervalDimerFold_hSupport (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame
    (itemTrackBase p k before) (p.itemDimers s) (by have h := p.itemDimers_ge s hs; omega) false
    (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload)

theorem rightPiece_lastHIndex (p : ConstructionParameters) :
    dimerHIndex (rightFillerTrackBase p) false (p.rightFiller - 1) 1 = 2 * p.side - 3 := by
  rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
  have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := by
    simp only [ConstructionParameters.side]
  dsimp [rightFillerTrackBase]
  omega

theorem rightPiece_hSupport_eq (p : ConstructionParameters) :
    hSupport (canonicalRightPiece p).word (canonicalRightPiece p).fold =
      edgeDimerHsites p.side trackEdgeFrame (rightFillerTrackBase p) (p.rightFiller - 1) :=
  cappedIntervalDimerFold_hSupport (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame
    (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega) false
    (rightFillerTrackBase_room p) (rightFirstColumn p) (rightFinalColumn p) rfl
    (by rw [rightPiece_lastHIndex]; exact rightFinalColumn_track_owner p)

theorem leftPiece_hSupport_eq (p : ConstructionParameters) :
    hSupport (canonicalLeftPiece p).word (canonicalLeftPiece p).fold = leftFillerHsites p := by
  dsimp only [canonicalLeftPiece, leftFillerWordPiece]
  exact cappedLeftFillerFold_hSupport_exact p _ _ rfl (leftLastColumn_owner p)

theorem separatorPiece_hSupport_eq (p : ConstructionParameters) (k : Fin (p.bins + 1)) :
    hSupport (canonicalSeparatorPiece p k).word (canonicalSeparatorPiece p k).fold =
      (edgeDimerHsites p.side entryEdgeFrame (6 * (k.val + 1)) 0 ∪
        edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k.val) 1) ∪
        edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k.val + 6) 2 := by
  dsimp only [canonicalSeparatorPiece, separatorWordPiece]
  exact (cappedSeparatorFold_hSupport p k.val (by have h := k.isLt; omega) _ _ rfl
    (exitCapColumn_owner p k.val (by have h := k.isLt; omega))).trans
    (separatorFold_hSupport p k.val (by have h := k.isLt; omega))

private theorem capped_clear {a b : ℕ} {p : ConstructionParameters} (C : DanglingColumn p.side)
    (f : Fold tetrahedralLattice a) (g : Fold tetrahedralLattice b) (c d : Site)
    (hsites : foldSites f = ({c} ∪ foldSites g) ∪ {d}) (hc : IsDangling p.side c) (hd : IsDangling p.side d)
    (n : ℕ) (hn : 1 ≤ n) (hg : ∀ i, g.pos i ≠ C.point n) (i : Fin a) : f.pos i ≠ C.point n :=
  frameTrack_property_of_capped_sites f g c d hsites (fun x => x ≠ C.point n)
    (FarField.dangling_ne_positive_column hc C n hn) hg (FarField.dangling_ne_positive_column hd C n hn) i

private theorem inside_clear {p : ConstructionParameters} (C : DanglingColumn p.side) (x : Site)
    (hx : x ∈ octahedron p.side) (n : ℕ) : x ≠ C.point n := by
  intro heq
  rw [heq] at hx
  exact C.point_outside n hx

theorem leftLink_mem_leftHsites (p : ConstructionParameters) (j : ℕ) (hj : j < p.leftFiller - 1) (a : Fin 2) :
    octEdgeZigzag p.side trackEdgeFrame (dimerLinkIndex 0 false j + 2 * a.val) ∈ leftFillerHsites p := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_erase.mpr
  constructor
  · intro heq
    have hi := octEdgeZigzag_injective (by have h := p.side_ge; omega) trackEdgeFrame heq
    exact dimerFirst_ne_link_endpoint 0 false j a hi.symm
  · exact dimerLink_endpoint_mem_Hsites p.side trackEdgeFrame 0 (p.leftFiller - 1) false j hj a

theorem leftPiece_ne_ordinaryInnerColumn_of_not_mem {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C)
    (hnot : C.owner ∉ hSupport (canonicalLeftPiece p).word (canonicalLeftPiece p).fold)
    (i : Fin (canonicalLeftPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalLeftPiece p).fold.pos i ≠ C.point n := by
  have hleft := not_mem_of_eq (leftPiece_hSupport_eq p) hnot
  have howners : DimerLinkOwnerExcluded p.side trackEdgeFrame 0 (p.leftFiller - 1) false C.owner := by
    intro j hj a heq
    apply hleft
    rw [heq]
    exact leftLink_mem_leftHsites p j hj a
  apply capped_clear C _ _ (entryLocalColumn p none).seed (leftLastColumn p).seed
    (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p))
    (entryLocalColumn p none).seed_dangling (leftLastColumn p).seed_dangling n hn _ i
  intro j
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hj
  · exact inside_clear C _ (leftFillerStart_mem_oct p) n
  · let r : Fin (dimerChain (p.leftFiller - 1 + 1)).length := ⟨j.val, by
      have hlen := leftFiller_word_length p
      have hs := dimerChain_succ_length (p.leftFiller - 1)
      have hj' := j.isLt
      omega⟩
    have h := edgeDimerFold_ne_ordinaryInnerColumn hC trackEdgeFrame 0 (p.leftFiller - 1) false
      (leftFiller_room p) howners r n
    rw [edgeDimerFold_pos] at h
    exact h

theorem itemPiece_ne_ordinaryInnerColumn_of_not_mem {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (k before s : ℕ) (hk : k < p.bins) (hs : 0 < s)
    (hload : before + s ≤ p.capacity)
    (hnot : C.owner ∉ hSupport (canonicalItemPiece p k before s hk hs hload).word (canonicalItemPiece p k before s hk hs hload).fold)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ≠ C.point n := by
  have hmask := not_mem_of_eq (itemPiece_hSupport_eq p k before s hk hs hload) hnot
  exact cappedInterval_ne_ordinaryInnerColumn hC trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s)
    (by have h := p.itemDimers_ge s hs; omega) false (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload)
    (dimerLinkOwnerExcluded_of_not_mem p.side trackEdgeFrame _ _ false C.owner hmask) i n hn

theorem rightPiece_ne_ordinaryInnerColumn_of_not_mem {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (hnot : C.owner ∉ hSupport (canonicalRightPiece p).word (canonicalRightPiece p).fold)
    (i : Fin (canonicalRightPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalRightPiece p).fold.pos i ≠ C.point n := by
  have hmask := not_mem_of_eq (rightPiece_hSupport_eq p) hnot
  exact cappedInterval_ne_ordinaryInnerColumn hC trackEdgeFrame (rightFillerTrackBase p) p.rightFiller
    (by have h := p.rightFiller_ge; omega) false (rightFillerTrackBase_room p)
    (rightFirstColumn p) (rightFinalColumn p) rfl
    (by rw [rightPiece_lastHIndex]; exact rightFinalColumn_track_owner p)
    (dimerLinkOwnerExcluded_of_not_mem p.side trackEdgeFrame _ _ false C.owner hmask) i n hn

theorem separatorPiece_ne_ordinaryInnerColumn_of_not_mem {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (k : Fin (p.bins + 1))
    (hnot : C.owner ∉ hSupport (canonicalSeparatorPiece p k).word (canonicalSeparatorPiece p k).fold)
    (i : Fin (canonicalSeparatorPiece p k).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalSeparatorPiece p k).fold.pos i ≠ C.point n := by
  have hk : k.val ≤ p.bins := by have h := k.isLt; omega
  have hmask := not_mem_of_eq (separatorPiece_hSupport_eq p k) hnot
  have hA : C.owner ∉ edgeDimerHsites p.side entryEdgeFrame (6 * (k.val + 1)) 0 :=
    fun hx => hmask (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have hB : C.owner ∉ edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k.val) 1 :=
    fun hx => hmask (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have hD : C.owner ∉ edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k.val + 6) 2 :=
    fun hx => hmask (Finset.mem_union_right _ hx)
  apply capped_clear C _ _ (entryLocalColumn p (some k)).seed (exitCapColumn p k.val hk).seed
    (cappedSeparatorFold_sites p k.val hk _ _ rfl (exitCapColumn_owner p k.val hk))
    (entryLocalColumn p (some k)).seed_dangling (exitCapColumn p k.val hk).seed_dangling n hn _ i
  intro j
  apply separatorFold_property p k.val hk (fun x => x ≠ C.point n) _ _ _ _ _ j
  · exact fun r => edgeDimerFold_ne_ordinaryInnerColumn hC entryEdgeFrame _ _ false (separatorEntry_room p k.val hk)
      (dimerLinkOwnerExcluded_of_not_mem p.side entryEdgeFrame _ _ false C.owner hA) r n
  · intro r
    rw [entryTetherWordFold_pos]
    exact hC.entryTether_clear k.val hk _ n
  · exact fun r => edgeDimerFold_ne_ordinaryInnerColumn hC trackEdgeFrame _ _ true (separatorCenter_room p k.val hk)
      (dimerLinkOwnerExcluded_of_not_mem p.side trackEdgeFrame _ _ true C.owner hB) r n
  · intro r
    rw [exitTetherWordFold_pos]
    exact hC.exitTether_clear k.val hk _ n
  · exact fun r => edgeDimerFold_ne_ordinaryInnerColumn hC exitEdgeFrame _ _ true (separatorExit_room p k.val)
      (dimerLinkOwnerExcluded_of_not_mem p.side exitEdgeFrame _ _ true C.owner hD) r n

theorem ringPiece_ne_ordinaryInnerColumn {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (i : Fin 3) (r : Fin (canonicalRingWordPiece p i).word.length)
    (n : ℕ) (hn : 1 ≤ n) : (canonicalRingWordPiece p i).fold.pos r ≠ C.point n := by
  have hsize := p.side_ge
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have hreserved := hC.owner_reserved_coordinate
  apply capped_clear C _ _ (canonicalRingColumn p i 0).seed (canonicalRingColumn p i 1).seed
    (cappedRingFold_sites p.side (by omega) p.side_even (canonicalRingFrame i)
      (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
      (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i))
    (canonicalRingColumn p i 0).seed_dangling (canonicalRingColumn p i 1).seed_dangling n hn _ r
  intro j
  apply ringFold_property p.side hm p.side_even (canonicalRingFrame i) (fun x => x ≠ C.point n) _ _ j
  · intro s t
    let t' : Fin (dimerChain (p.side - 3 + 1)).length :=
      ⟨t.val, by rw [show p.side - 3 + 1 = p.side - 2 by omega]; exact t.isLt⟩
    apply edgeDimerFold_ne_ordinaryInnerColumn hC (ringSideFrame (canonicalRingFrame i) s) 1 (p.side - 3)
      false (by omega) _ t' n
    intro k hk a heq
    have hb := dimerLinkIndex_bounds 1 false k
    have ha := a.isLt
    exact ringEdgePoint_ne_reserved_site p.side hm (ringSideFrame (canonicalRingFrame i) s)
      (by rw [ringSideFrame_small]; exact canonicalRingFrame_small_ne_reserved i)
      _ (by omega) (by omega) C.owner hreserved heq.symm
  · intro c t
    apply hC.edgePPP_clear (bulkReverseEdgeFrame (ringSideFrame (canonicalRingFrame i) c.castSucc)) 1 (by omega) _ _ t.rev n
    · rw [ringCorner_start_owner p.side hm (canonicalRingFrame i) c]
      intro heq
      have h := ringTerminal_reserved_coordinate p.side hm (canonicalRingFrame i)
        (canonicalRingFrame_small_ne_reserved i) c.succ 0
      rw [← heq] at h
      omega
    · rw [ringCorner_end_owner p.side hm (canonicalRingFrame i) c]
      intro heq
      have h := ringTerminal_reserved_coordinate p.side hm (canonicalRingFrame i)
        (canonicalRingFrame_small_ne_reserved i) c.castSucc 1
      rw [← heq] at h
      omega

theorem canonicalLocal_ordinaryColumn_of_not_mem {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (ha : (bulkFiniteGraph p.side).IsAcyclic) (n : ℕ) (hn : 1 ≤ n) :
    CanonicalLocalProperty p ha (fun q => C.owner ∉ hSupport q.word q.fold → ∀ i, q.fold.pos i ≠ C.point n) := {
  singleton := fun r _ i => canonicalSingletonPiece_ne_positiveColumn p.side (by have h := p.side_ge; omega) r C n hn i
  frame := fun _ i => hC.frame_clear n hn i
  separator := fun k hnot i => separatorPiece_ne_ordinaryInnerColumn_of_not_mem hC k hnot i n hn
  left := fun hnot i => leftPiece_ne_ordinaryInnerColumn_of_not_mem hC hnot i n hn
  item := fun k before s hk hs hload hnot i => itemPiece_ne_ordinaryInnerColumn_of_not_mem hC k before s hk hs hload hnot i n hn
  right := fun hnot i => rightPiece_ne_ordinaryInnerColumn_of_not_mem hC hnot i n hn
  ring := fun r _ i => ringPiece_ne_ordinaryInnerColumn hC r i n hn
  bulk := fun j _ i => ReductionTM2.BulkScan.cappedRuntimePiece_ne_positive_column p.side
    (by have h := p.side_ge; omega) ha j
    (ReductionTM2.BulkScan.firstColumn p.side (by have h := p.side_ge; omega) ha j)
    (ReductionTM2.BulkScan.lastColumn p.side (by have h := p.side_ge; omega) ha j) rfl rfl C n hn i }

end ProteinFolding.Tetrahedral.NearField

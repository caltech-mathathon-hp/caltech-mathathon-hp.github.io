import ProteinFolding.Tetrahedral.NearFieldTerminalTetherColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalTerminalSeparation
import ProteinFolding.Tetrahedral.FarFieldMixedCaps

/-! Positive-height clearance of the actual terminal column from every
complete local unit, retaining all hydrophobic bodies and physical caps. -/

namespace ProteinFolding.Tetrahedral.NearField

attribute [local irreducible] ConstructionParameters.side

private theorem inside_ne_terminalColumn (p : ConstructionParameters) (x : Site)
    (hx : x ∈ octahedron p.side) (n : ℕ) : x ≠ (terminalColumn p).point n := by
  intro heq
  rw [heq] at hx
  exact (terminalColumn p).point_outside n hx

theorem edgeDimerFold_ne_terminalColumn_of_not_mem (p : ConstructionParameters)
    (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * p.side - 1)
    (hnot : (terminalColumn p).owner ∉ edgeDimerHsites p.side F base q)
    (i : Fin (dimerChain (q + 1)).length) (n : ℕ) :
    (edgeDimerFold (by have h := p.side_ge; omega : 1 ≤ p.side) F base q reverse hroom).pos i ≠
      (terminalColumn p).point n := by
  have hex := dimerLinkOwnerExcluded_of_not_mem p.side F base q reverse (terminalColumn p).owner hnot
  apply edgeDimerFold_ne_column_of_PPP_ne (by have h := p.side_ge; omega : 1 ≤ p.side)
    F base q reverse hroom (terminalColumn p) _ i n
  intro j hj s r
  have hb := dimerLinkIndex_bounds base reverse j
  exact edgePPPFold_ne_terminalColumn p F _ (by omega)
    (by simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using hex j hj 0)
    (by simpa only [Fin.val_one, Nat.mul_one] using hex j hj 1) s r

private theorem terminal_capped_clear {a b : ℕ} (p : ConstructionParameters)
    (f : Fold tetrahedralLattice a) (g : Fold tetrahedralLattice b) (c d : Site)
    (hsites : foldSites f = ({c} ∪ foldSites g) ∪ {d})
    (hc : IsDangling p.side c) (hd : IsDangling p.side d) (n : ℕ) (hn : 1 ≤ n)
    (hg : ∀ i, g.pos i ≠ (terminalColumn p).point n) (i : Fin a) : f.pos i ≠ (terminalColumn p).point n :=
  frameTrack_property_of_capped_sites f g c d hsites (fun x => x ≠ (terminalColumn p).point n)
    (FarField.dangling_ne_positive_column hc (terminalColumn p) n hn) hg
    (FarField.dangling_ne_positive_column hd (terminalColumn p) n hn) i

theorem cappedInterval_ne_terminalColumn_of_not_mem (p : ConstructionParameters)
    (F : OctEdgeFrame) (base q : ℕ) (hq : 0 < q) (reverse : Bool)
    (hroom : base + 2 * q ≤ 2 * p.side - 1) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (q - 1) 1))
    (hnot : (terminalColumn p).owner ∉ edgeDimerHsites p.side F base (q - 1))
    (i : Fin (capWord (dimerChain q)).length) (n : ℕ) (hn : 1 ≤ n) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      F base q hq reverse hroom C D hC hD).pos i ≠ (terminalColumn p).point n := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hroom' : base + 2 * (q - 1 + 1) ≤ 2 * p.side - 1 := by omega
  apply transportWordFold_property (congrArg capWord (positive_dimer_word q hq))
    (cappedEdgeDimerFold hm F base (q - 1) reverse hroom' C D hC hD) (fun x => x ≠ (terminalColumn p).point n) _ i
  exact terminal_capped_clear p _ _ C.seed D.seed
    (cappedEdgeDimerFold_sites hm F base (q - 1) reverse hroom' C D hC hD)
    C.seed_dangling D.seed_dangling n hn
    (fun j => edgeDimerFold_ne_terminalColumn_of_not_mem p F base (q - 1) reverse hroom' hnot j n)

theorem canonicalItemPiece_ne_terminalColumn (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ≠ (terminalColumn p).point n :=
  cappedInterval_ne_terminalColumn_of_not_mem p trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s)
    (by have h := p.itemDimers_ge s hs; omega) false (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload)
    (terminalOwner_not_mem_trackHsites p _ _) i n hn

theorem canonicalRightPiece_ne_terminalColumn (p : ConstructionParameters)
    (i : Fin (canonicalRightPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalRightPiece p).fold.pos i ≠ (terminalColumn p).point n := by
  have hlast : (rightFinalColumn p).owner = octEdgeZigzag p.side trackEdgeFrame
      (dimerHIndex (rightFillerTrackBase p) false (p.rightFiller - 1) 1) := by
    rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
    have hside : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := by
      simp only [ConstructionParameters.side]
    have he : rightFillerTrackBase p + 2 * p.rightFiller - 1 = 2 * p.side - 3 := by
      dsimp [rightFillerTrackBase]
      omega
    rw [he]
    exact rightFinalColumn_track_owner p
  exact cappedInterval_ne_terminalColumn_of_not_mem p trackEdgeFrame (rightFillerTrackBase p) p.rightFiller
    (by have h := p.rightFiller_ge; omega) false (rightFillerTrackBase_room p)
    (rightFirstColumn p) (rightFinalColumn p) rfl hlast (terminalOwner_not_mem_trackHsites p _ _) i n hn

theorem leftFillerFold_ne_terminalColumn (p : ConstructionParameters)
    (i : Fin (dimerChain p.leftFiller).length) (n : ℕ) :
    (leftFillerFold p).pos i ≠ (terminalColumn p).point n := by
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hi
  · exact inside_ne_terminalColumn p _ (leftFillerStart_mem_oct p) n
  · let j : Fin (dimerChain (p.leftFiller - 1 + 1)).length :=
      ⟨i.val, by
        have hl := dimerChain_succ_length (p.leftFiller - 1)
        have hw := leftFiller_word_length p
        have hi' := i.isLt
        omega⟩
    have h := edgeDimerFold_ne_terminalColumn_of_not_mem p trackEdgeFrame 0 (p.leftFiller - 1)
      false (leftFiller_room p) (terminalOwner_not_mem_trackHsites p _ _) j n
    rw [edgeDimerFold_pos] at h
    exact h

theorem canonicalLeftPiece_ne_terminalColumn (p : ConstructionParameters)
    (i : Fin (canonicalLeftPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalLeftPiece p).fold.pos i ≠ (terminalColumn p).point n :=
  terminal_capped_clear p _ _ (entryLocalColumn p none).seed (leftLastColumn p).seed
    (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p))
    (entryLocalColumn p none).seed_dangling (leftLastColumn p).seed_dangling n hn
    (fun j => leftFillerFold_ne_terminalColumn p j n) i

theorem separatorFold_ne_terminalColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.separatorWord k).length) (n : ℕ) :
    (separatorFold p k hk).pos i ≠ (terminalColumn p).point n := by
  apply separatorFold_property p k hk (fun x => x ≠ (terminalColumn p).point n) _ _ _ _ _ i
  · exact fun j => edgeDimerFold_ne_terminalColumn_of_not_mem p entryEdgeFrame (6 * (k + 1)) 0 false
      (separatorEntry_room p k hk) (terminalOwner_not_mem_entryHsites p _ _
        (by have h := p.entry_column_triangle_room k hk; omega)) j n
  · intro j
    rw [entryTetherWordFold_pos]
    exact entryTetherFold_ne_terminalColumn p k hk _ n
  · exact fun j => edgeDimerFold_ne_terminalColumn_of_not_mem p trackEdgeFrame (2 * p.separatorIndex k) 1 true
      (separatorCenter_room p k hk) (terminalOwner_not_mem_trackHsites p _ _) j n
  · intro j
    rw [exitTetherWordFold_pos]
    exact exitTetherFold_ne_terminalColumn p k hk _ n
  · exact fun j => edgeDimerFold_ne_terminalColumn_of_not_mem p exitEdgeFrame (10 * p.exitSlot k + 6) 2 true
      (separatorExit_room p k) (terminalOwner_not_mem_exitHsites p _ _
        (by have h := p.exit_column_triangle_room k; omega)) j n

theorem canonicalSeparatorPiece_ne_terminalColumn (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (i : Fin (canonicalSeparatorPiece p k).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalSeparatorPiece p k).fold.pos i ≠ (terminalColumn p).point n :=
  terminal_capped_clear p _ _ (entryLocalColumn p (some k)).seed
    (exitCapColumn p k.val (by have h := k.isLt; omega)).seed
    (cappedSeparatorFold_sites p k.val (by have h := k.isLt; omega) _ _ rfl
      (exitCapColumn_owner p k.val (by have h := k.isLt; omega)))
    (entryLocalColumn p (some k)).seed_dangling
    (exitCapColumn p k.val (by have h := k.isLt; omega)).seed_dangling n hn
    (fun j => separatorFold_ne_terminalColumn p k.val (by have h := k.isLt; omega) j n) i

private theorem terminalOwner_not_mem_ringSide (p : ConstructionParameters) (i j : Fin 3) :
    (terminalColumn p).owner ∉ edgeDimerHsites p.side (ringSideFrame (canonicalRingFrame i) j) 1 (p.side - 3) := by
  have hm := p.side_ge
  intro hmem
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hmem
  have hb := r.isLt
  exact ringEdgePoint_ne_reserved_site p.side (by have h := p.side_ge; omega)
    (ringSideFrame (canonicalRingFrame i) j)
    (by rw [ringSideFrame_small]; exact canonicalRingFrame_small_ne_reserved i)
    _ (by omega) (by omega) _ (terminalColumn_owner_reserved_coordinate p) hr

private theorem terminalOwner_ne_ringTerminal (p : ConstructionParameters) (i j : Fin 3) (e : Fin 2) :
    (terminalColumn p).owner ≠ ringTerminalSite p.side (canonicalRingFrame i) j e := by
  intro heq
  have ht := terminalColumn_owner_reserved_coordinate p
  have hr := ringTerminal_reserved_coordinate p.side (by have h := p.side_ge; omega)
    (canonicalRingFrame i) (canonicalRingFrame_small_ne_reserved i) j e
  rw [heq] at ht
  omega

theorem ringFold_ne_terminalColumn (p : ConstructionParameters) (i : Fin 3)
    (r : Fin (dimerChain (3 * (p.side - 2))).length) (n : ℕ) :
    (ringFold p.side (by have h := p.side_ge; omega) p.side_even (canonicalRingFrame i)).pos r ≠
      (terminalColumn p).point n := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  apply ringFold_property p.side hm p.side_even (canonicalRingFrame i) (fun x => x ≠ (terminalColumn p).point n) _ _ r
  · intro j s
    let s' : Fin (dimerChain (p.side - 3 + 1)).length :=
      ⟨s.val, by rw [show p.side - 3 + 1 = p.side - 2 by omega]; exact s.isLt⟩
    exact edgeDimerFold_ne_terminalColumn_of_not_mem p (ringSideFrame (canonicalRingFrame i) j)
      1 (p.side - 3) false (by omega) (terminalOwner_not_mem_ringSide p i j) s' n
  · intro c s
    exact edgePPPFold_ne_terminalColumn p (bulkReverseEdgeFrame (ringSideFrame (canonicalRingFrame i) c.castSucc))
      1 (by omega)
      (by rw [ringCorner_start_owner p.side hm (canonicalRingFrame i) c]
          exact terminalOwner_ne_ringTerminal p i c.succ 0)
      (by rw [ringCorner_end_owner p.side hm (canonicalRingFrame i) c]
          exact terminalOwner_ne_ringTerminal p i c.castSucc 1) s.rev n

theorem canonicalRingWordPiece_ne_terminalColumn (p : ConstructionParameters) (i : Fin 3)
    (r : Fin (canonicalRingWordPiece p i).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (terminalColumn p).point n :=
  terminal_capped_clear p _ _ (canonicalRingColumn p i 0).seed (canonicalRingColumn p i 1).seed
    (cappedRingFold_sites p.side (by have h := p.side_ge; omega) p.side_even (canonicalRingFrame i)
      (canonicalRingColumn p i 0) (canonicalRingColumn p i 1)
      (canonicalRingColumn_first_owner p i) (canonicalRingColumn_last_owner p i))
    (canonicalRingColumn p i 0).seed_dangling (canonicalRingColumn p i 1).seed_dangling n hn
    (fun j => ringFold_ne_terminalColumn p i j n) r

theorem canonicalLocal_ne_terminalColumn (p : ConstructionParameters) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (n : ℕ) (hn : 1 ≤ n) :
    CanonicalLocalProperty p ha (fun q => ∀ i, q.fold.pos i ≠ (terminalColumn p).point n) := {
  singleton := fun r i => canonicalSingletonPiece_ne_positiveColumn p.side (by have h := p.side_ge; omega)
    r (terminalColumn p) n hn i
  frame := fun i => frameFold_ne_terminalColumn p n hn i
  separator := fun k i => canonicalSeparatorPiece_ne_terminalColumn p k i n hn
  left := fun i => canonicalLeftPiece_ne_terminalColumn p i n hn
  item := fun k before s hk hs hload i => canonicalItemPiece_ne_terminalColumn p k before s hk hs hload i n hn
  right := fun i => canonicalRightPiece_ne_terminalColumn p i n hn
  ring := fun r i => canonicalRingWordPiece_ne_terminalColumn p r i n hn
  bulk := fun j i => ReductionTM2.BulkScan.cappedRuntimePiece_ne_positive_column p.side
    (by have h := p.side_ge; omega) ha j
    (ReductionTM2.BulkScan.firstColumn p.side (by have h := p.side_ge; omega) ha j)
    (ReductionTM2.BulkScan.lastColumn p.side (by have h := p.side_ge; omega) ha j)
    rfl rfl (terminalColumn p) n hn i }

theorem canonicalTaggedBody_ne_terminalColumn (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (u : CappedUnit p.side) (hu : u ∈ canonicalTaggedBodies p items d ha)
    (i : Fin u.piece.word.length) (n : ℕ) (hn : 1 ≤ n) : u.piece.fold.pos i ≠ (terminalColumn p).point n :=
  canonicalTaggedBodies_property p items d ha _ (canonicalLocal_ne_terminalColumn p ha n hn) u hu i

theorem terminalWordPiece_ne_terminalColumn (p : ConstructionParameters)
    (i : Fin (terminalWordPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (terminalWordPiece p).fold.pos i ≠ (terminalColumn p).point n := by
  change (if i.val = 0 then (terminalColumn p).owner else (terminalColumn p).seed) ≠ _
  split_ifs
  · exact inside_ne_terminalColumn p _ (terminalColumn p).owner_mem n
  · exact FarField.dangling_ne_positive_column (terminalColumn p).seed_dangling (terminalColumn p) n hn

end ProteinFolding.Tetrahedral.NearField

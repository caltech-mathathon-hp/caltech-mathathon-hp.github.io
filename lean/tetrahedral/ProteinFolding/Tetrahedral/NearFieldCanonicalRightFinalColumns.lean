import ProteinFolding.Tetrahedral.NearFieldCanonicalOrdinaryColumns
import ProteinFolding.Tetrahedral.NearFieldRightFinalTethers
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingBulkColumns

/-! The right filler's last column is the reserved B corner exit[1]. Its
own unit is handled by endpoint arithmetic; actual pairwise geometry supplies
the owner exclusions needed by every other tagged unit. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem rightFinal_mem_of_eq {A B : Finset Site} {x : Site} (h : A = B) (hx : x ∈ B) : x ∈ A := by
  rw [h]
  exact hx

private theorem rightFinal_not_mem_of_eq {A B : Finset Site} {x : Site} (h : A = B) (hx : x ∉ A) : x ∉ B :=
  fun hm => hx (rightFinal_mem_of_eq h hm)

private theorem rightFinal_inside_clear (p : ConstructionParameters) (x : Site)
    (hx : x ∈ octahedron p.side) (n : ℕ) : x ≠ (rightFinalColumn p).point n := by
  intro heq
  exact (rightFinalColumn p).point_outside n (heq ▸ hx)

private theorem rightFinal_capped_clear {a b : ℕ} (p : ConstructionParameters)
    (f : Fold tetrahedralLattice a) (g : Fold tetrahedralLattice b) (c d : Site)
    (hsites : foldSites f = ({c} ∪ foldSites g) ∪ {d})
    (hc : IsDangling p.side c) (hd : IsDangling p.side d)
    (n : ℕ) (hn : 1 ≤ n) (hg : ∀ i, g.pos i ≠ (rightFinalColumn p).point n) (i : Fin a) :
    f.pos i ≠ (rightFinalColumn p).point n :=
  frameTrack_property_of_capped_sites f g c d hsites (fun x => x ≠ (rightFinalColumn p).point n)
    (FarField.dangling_ne_positive_column hc (rightFinalColumn p) n hn) hg
    (FarField.dangling_ne_positive_column hd (rightFinalColumn p) n hn) i

theorem edgeDimerFold_ne_rightFinalColumn_of_owners (p : ConstructionParameters)
    (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * p.side - 1)
    (howners : DimerLinkOwnerExcluded p.side F base q reverse (rightFinalColumn p).owner)
    (i : Fin (dimerChain (q + 1)).length) (n : ℕ) :
    (edgeDimerFold (by have h := p.side_ge; omega : 1 ≤ p.side) F base q reverse hroom).pos i ≠
      (rightFinalColumn p).point n := by
  apply edgeDimerFold_ne_column_of_PPP_ne (by have h := p.side_ge; omega : 1 ≤ p.side)
    F base q reverse hroom (rightFinalColumn p) _ i n
  intro j hj s t
  have hb := dimerLinkIndex_bounds base reverse j
  exact (rightFinalColumn_ne_edgePPP p F _ (by omega)
    (by simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using howners j hj 0)
    (by simpa only [Fin.val_one, Nat.mul_one] using howners j hj 1) t s).symm

theorem cappedInterval_ne_rightFinalColumn_of_owners (p : ConstructionParameters)
    (F : OctEdgeFrame) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * p.side - 1) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (n - 1) 1))
    (howners : DimerLinkOwnerExcluded p.side F base (n - 1) reverse (rightFinalColumn p).owner)
    (i : Fin (capWord (dimerChain n)).length) (t : ℕ) (ht : 1 ≤ t) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      F base n hn reverse hroom C D hC hD).pos i ≠ (rightFinalColumn p).point t := by
  apply transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold (by have h := p.side_ge; omega : 1 ≤ p.side)
      F base (n - 1) reverse (by omega) C D hC hD) (fun x => x ≠ (rightFinalColumn p).point t) _ i
  exact cappedEdgeDimerFold_property (by have h := p.side_ge; omega : 1 ≤ p.side)
    F base (n - 1) reverse (by omega) C D hC hD (fun x => x ≠ (rightFinalColumn p).point t)
    (FarField.dangling_ne_positive_column C.seed_dangling (rightFinalColumn p) t ht)
    (fun j => edgeDimerFold_ne_rightFinalColumn_of_owners p F base (n - 1) reverse (by omega) howners j t)
    (FarField.dangling_ne_positive_column D.seed_dangling (rightFinalColumn p) t ht)

theorem rightFinalColumn_mem_own_Hsupport (p : ConstructionParameters) :
    (rightFinalColumn p).owner ∈ hSupport (canonicalRightPiece p).word (canonicalRightPiece p).fold := by
  apply rightFinal_mem_of_eq (rightPiece_hSupport_eq p)
  rw [rightFinalColumn_track_owner, ← rightPiece_lastHIndex]
  exact dimerHIndex_mem_Hsites p.side trackEdgeFrame _ _ false (p.rightFiller - 1) le_rfl 1

theorem rightPiece_ne_own_finalColumn (p : ConstructionParameters)
    (i : Fin (canonicalRightPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalRightPiece p).fold.pos i ≠ (rightFinalColumn p).point n := by
  have howners : DimerLinkOwnerExcluded p.side trackEdgeFrame (rightFillerTrackBase p)
      (p.rightFiller - 1) false (rightFinalColumn p).owner := by
    rw [rightFinalColumn_track_owner, ← rightPiece_lastHIndex]
    exact dimerLinkOwnerExcluded_last (by have h := p.side_ge; omega)
      trackEdgeFrame (rightFillerTrackBase p) (p.rightFiller - 1) false
  exact cappedInterval_ne_rightFinalColumn_of_owners p trackEdgeFrame (rightFillerTrackBase p) p.rightFiller
    (by have h := p.rightFiller_ge; omega) false (rightFillerTrackBase_room p)
    (rightFirstColumn p) (rightFinalColumn p) rfl
    (by rw [rightPiece_lastHIndex]; exact rightFinalColumn_track_owner p) howners i n hn

theorem leftPiece_ne_rightFinalColumn_of_not_mem (p : ConstructionParameters)
    (hnot : (rightFinalColumn p).owner ∉ hSupport (canonicalLeftPiece p).word (canonicalLeftPiece p).fold)
    (i : Fin (canonicalLeftPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalLeftPiece p).fold.pos i ≠ (rightFinalColumn p).point n := by
  have hmask := rightFinal_not_mem_of_eq (leftPiece_hSupport_eq p) hnot
  have howners : DimerLinkOwnerExcluded p.side trackEdgeFrame 0 (p.leftFiller - 1) false
      (rightFinalColumn p).owner := by
    intro j hj a heq
    apply hmask
    rw [heq]
    exact leftLink_mem_leftHsites p j hj a
  apply rightFinal_capped_clear p _ _ (entryLocalColumn p none).seed (leftLastColumn p).seed
    (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p))
    (entryLocalColumn p none).seed_dangling (leftLastColumn p).seed_dangling n hn _ i
  intro j
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hj
  · exact rightFinal_inside_clear p _ (leftFillerStart_mem_oct p) n
  · let r : Fin (dimerChain (p.leftFiller - 1 + 1)).length := ⟨j.val, by
      have hlen := leftFiller_word_length p
      have hs := dimerChain_succ_length (p.leftFiller - 1)
      have hj' := j.isLt
      omega⟩
    have h := edgeDimerFold_ne_rightFinalColumn_of_owners p trackEdgeFrame 0 (p.leftFiller - 1) false
      (leftFiller_room p) howners r n
    rw [edgeDimerFold_pos] at h
    exact h

theorem itemPiece_ne_rightFinalColumn_of_not_mem (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (hnot : (rightFinalColumn p).owner ∉
      hSupport (canonicalItemPiece p k before s hk hs hload).word (canonicalItemPiece p k before s hk hs hload).fold)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ≠ (rightFinalColumn p).point n := by
  have hmask := rightFinal_not_mem_of_eq (itemPiece_hSupport_eq p k before s hk hs hload) hnot
  exact cappedInterval_ne_rightFinalColumn_of_owners p trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s)
    (by have h := p.itemDimers_ge s hs; omega) false (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload)
    (dimerLinkOwnerExcluded_of_not_mem p.side trackEdgeFrame _ _ false _ hmask) i n hn

theorem rightPiece_ne_rightFinalColumn_of_not_mem (p : ConstructionParameters)
    (hnot : (rightFinalColumn p).owner ∉ hSupport (canonicalRightPiece p).word (canonicalRightPiece p).fold)
    (i : Fin (canonicalRightPiece p).word.length) (n : ℕ) (_hn : 1 ≤ n) :
    (canonicalRightPiece p).fold.pos i ≠ (rightFinalColumn p).point n :=
  False.elim (hnot (rightFinalColumn_mem_own_Hsupport p))

theorem separatorPiece_ne_rightFinalColumn_of_not_mem (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (hnot : (rightFinalColumn p).owner ∉ hSupport (canonicalSeparatorPiece p k).word (canonicalSeparatorPiece p k).fold)
    (i : Fin (canonicalSeparatorPiece p k).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalSeparatorPiece p k).fold.pos i ≠ (rightFinalColumn p).point n := by
  have hk : k.val ≤ p.bins := by have h := k.isLt; omega
  have hmask := rightFinal_not_mem_of_eq (separatorPiece_hSupport_eq p k) hnot
  have hA : (rightFinalColumn p).owner ∉ edgeDimerHsites p.side entryEdgeFrame (6 * (k.val + 1)) 0 :=
    fun hx => hmask (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have hB : (rightFinalColumn p).owner ∉ edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k.val) 1 :=
    fun hx => hmask (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have hD : (rightFinalColumn p).owner ∉ edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k.val + 6) 2 :=
    fun hx => hmask (Finset.mem_union_right _ hx)
  apply rightFinal_capped_clear p _ _ (entryLocalColumn p (some k)).seed (exitCapColumn p k.val hk).seed
    (cappedSeparatorFold_sites p k.val hk _ _ rfl (exitCapColumn_owner p k.val hk))
    (entryLocalColumn p (some k)).seed_dangling (exitCapColumn p k.val hk).seed_dangling n hn _ i
  intro j
  apply separatorFold_property p k.val hk (fun x => x ≠ (rightFinalColumn p).point n) _ _ _ _ _ j
  · exact fun r => edgeDimerFold_ne_rightFinalColumn_of_owners p entryEdgeFrame _ _ false
      (separatorEntry_room p k.val hk)
      (dimerLinkOwnerExcluded_of_not_mem p.side entryEdgeFrame _ _ false _ hA) r n
  · intro r
    rw [entryTetherWordFold_pos]
    exact entryTetherFold_ne_rightFinalColumn p k.val hk _ n
  · exact fun r => edgeDimerFold_ne_rightFinalColumn_of_owners p trackEdgeFrame _ _ true
      (separatorCenter_room p k.val hk)
      (dimerLinkOwnerExcluded_of_not_mem p.side trackEdgeFrame _ _ true _ hB) r n
  · intro r
    rw [exitTetherWordFold_pos]
    exact exitTetherFold_ne_rightFinalColumn p k.val hk _ n
  · exact fun r => edgeDimerFold_ne_rightFinalColumn_of_owners p exitEdgeFrame _ _ true
      (separatorExit_room p k.val)
      (dimerLinkOwnerExcluded_of_not_mem p.side exitEdgeFrame _ _ true _ hD) r n

theorem canonicalRingWordPiece_ne_rightFinalColumn (p : ConstructionParameters) (r : Fin 3)
    (i : Fin (canonicalRingWordPiece p r).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalRingWordPiece p r).fold.pos i ≠ (rightFinalColumn p).point n := by
  apply rightFinal_capped_clear p _ _ (canonicalRingColumn p r 0).seed (canonicalRingColumn p r 1).seed
    (cappedRingFold_sites p.side (by have h := p.side_ge; omega) p.side_even (canonicalRingFrame r)
      (canonicalRingColumn p r 0) (canonicalRingColumn p r 1)
      (canonicalRingColumn_first_owner p r) (canonicalRingColumn_last_owner p r))
    (canonicalRingColumn p r 0).seed_dangling (canonicalRingColumn p r 1).seed_dangling n hn _ i
  intro j
  apply ringFold_ne_foreign_terminal_column p.side (by have h := p.side_ge; omega) p.side_even
    (canonicalRingFrame r) exitEdgeFrame (canonicalRingFrame_small_ne_reserved r) (rightFinalColumn p) _ j n
  apply Or.inl
  rw [rightFinalColumn_exit_owner]
  rfl

theorem canonicalLocal_rightFinalColumn_of_not_mem (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) (n : ℕ) (hn : 1 ≤ n) :
    CanonicalLocalProperty p ha (fun q => (rightFinalColumn p).owner ∉ hSupport q.word q.fold →
      ∀ i, q.fold.pos i ≠ (rightFinalColumn p).point n) where
  singleton r _ i := canonicalSingletonPiece_ne_positiveColumn p.side (by have h := p.side_ge; omega)
    r (rightFinalColumn p) n hn i
  frame _ i := frameFold_ne_rightFinalColumn p n hn i
  separator k hnot i := separatorPiece_ne_rightFinalColumn_of_not_mem p k hnot i n hn
  left hnot i := leftPiece_ne_rightFinalColumn_of_not_mem p hnot i n hn
  item k before s hk hs hload hnot i := itemPiece_ne_rightFinalColumn_of_not_mem p k before s hk hs hload hnot i n hn
  right hnot i := rightPiece_ne_rightFinalColumn_of_not_mem p hnot i n hn
  ring r _ i := canonicalRingWordPiece_ne_rightFinalColumn p r i n hn
  bulk j _ i := canonicalBulkPiece_ne_positiveColumn p ha j (rightFinalColumn p) n hn i

private theorem rightFinal_hSupport_subset_sites {S : Sequence} (f : Fold tetrahedralLattice S.length) :
    hSupport S f ⊆ foldSites f := by
  intro x hx
  obtain ⟨i, _, hi⟩ := (mem_hSupport S f x).mp hx
  exact (mem_foldSites f x).mpr ⟨i, hi⟩

private theorem rightFinal_wordsDisjoint_of_mem_ne (ps : List PositionedWord) (hp : ps.Pairwise WordsDisjoint)
    {u v : PositionedWord} (hu : u ∈ ps) (hv : v ∈ ps) (hne : u ≠ v) : WordsDisjoint u v := by
  revert hp hu hv hne
  induction ps with
  | nil => intro _ hu; cases hu
  | cons a ps ih =>
    intro hp hu hv hne
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hu with hua | hut
    · subst u
      rcases List.mem_cons.mp hv with hva | hvt
      · subst v
        exact False.elim (hne rfl)
      · exact hhead v hvt
    · rcases List.mem_cons.mp hv with hva | hvt
      · subst v
        exact (hhead u hut).symm
      · exact ih htail hut hvt hne

theorem rightFinalColumn_clear_of_pairwise (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : ((canonicalTaggedBodies p items d ha).map CappedUnit.piece).Pairwise WordsDisjoint)
    (u : CappedUnit p.side) (hu : u ∈ canonicalTaggedBodies p items d ha)
    (i : Fin u.piece.word.length) (n : ℕ) (hn : 1 ≤ n) :
    u.piece.fold.pos i ≠ (rightFinalColumn p).point n := by
  classical
  by_cases heq : canonicalRightPiece p = u.piece
  · have hself : ∀ j : Fin (canonicalRightPiece p).word.length,
        (canonicalRightPiece p).fold.pos j ≠ (rightFinalColumn p).point n :=
      fun j => rightPiece_ne_own_finalColumn p j n hn
    exact (heq ▸ hself) i
  · have hdis := rightFinal_wordsDisjoint_of_mem_ne _ hp
      (canonicalRightPiece_mem_taggedPieces p items d ha) (List.mem_map.mpr ⟨u, hu, rfl⟩) heq
    have hnot : (rightFinalColumn p).owner ∉ hSupport u.piece.word u.piece.fold := by
      intro hx
      exact Finset.disjoint_left.mp hdis
        (rightFinal_hSupport_subset_sites (canonicalRightPiece p).fold (rightFinalColumn_mem_own_Hsupport p))
        (rightFinal_hSupport_subset_sites u.piece.fold hx)
    exact canonicalTaggedBodies_property p items d ha _
      (canonicalLocal_rightFinalColumn_of_not_mem p ha n hn) u hu hnot i

theorem canonicalUnitPieces_ne_rightFinalColumn_of_pairwise (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : ((canonicalTaggedBodies p items d ha).map CappedUnit.piece).Pairwise WordsDisjoint)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha)
    (i : Fin q.word.length) (n : ℕ) (hn : 1 ≤ n) : q.fold.pos i ≠ (rightFinalColumn p).point n := by
  rcases List.mem_cons.mp hq with rfl | hq
  · exact terminalWordPiece_ne_positiveColumn p (rightFinalColumn p) n hn i
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
    exact rightFinalColumn_clear_of_pairwise p items d ha hp u hu i n hn

end ProteinFolding.Tetrahedral.NearField

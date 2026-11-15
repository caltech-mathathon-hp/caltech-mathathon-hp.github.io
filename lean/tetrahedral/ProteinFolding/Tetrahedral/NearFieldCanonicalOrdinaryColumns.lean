import ProteinFolding.Tetrahedral.NearFieldOrdinaryUnitColumns
import ProteinFolding.Tetrahedral.NearFieldCanonicalUnitPairwise

/-! Actual ordinary endpoint columns avoid their own words by dimer-index
arithmetic. Geometric pairwise disjointness supplies the other H-owner exclusions. -/

namespace ProteinFolding.Tetrahedral.NearField

attribute [local irreducible] ConstructionParameters.side

private theorem mem_of_eq {A B : Finset Site} {x : Site} (h : A = B) (hx : x ∈ B) : x ∈ A := by
  rw [h]
  exact hx

private theorem hSupport_subset_sites {S : Sequence} (f : Fold tetrahedralLattice S.length) :
    hSupport S f ⊆ foldSites f := by
  intro x hx
  obtain ⟨i, _, hi⟩ := (mem_hSupport S f x).mp hx
  exact (mem_foldSites f x).mpr ⟨i, hi⟩

private theorem inside_clear {p : ConstructionParameters} (C : DanglingColumn p.side) (x : Site)
    (hx : x ∈ octahedron p.side) (n : ℕ) : x ≠ C.point n := by
  intro heq
  rw [heq] at hx
  exact C.point_outside n hx

private theorem capped_clear {a b : ℕ} {p : ConstructionParameters} (C : DanglingColumn p.side)
    (f : Fold tetrahedralLattice a) (g : Fold tetrahedralLattice b) (c d : Site)
    (hsites : foldSites f = ({c} ∪ foldSites g) ∪ {d}) (hc : IsDangling p.side c) (hd : IsDangling p.side d)
    (n : ℕ) (hn : 1 ≤ n) (hg : ∀ i, g.pos i ≠ C.point n) (i : Fin a) : f.pos i ≠ C.point n :=
  frameTrack_property_of_capped_sites f g c d hsites (fun x => x ≠ C.point n)
    (FarField.dangling_ne_positive_column hc C n hn) hg (FarField.dangling_ne_positive_column hd C n hn) i

theorem itemFirstColumn_mem_own_Hsupport (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    (itemFirstColumn p k before s hk hs hload).owner ∈
      hSupport (canonicalItemPiece p k before s hk hs hload).word (canonicalItemPiece p k before s hk hs hload).fold := by
  apply mem_of_eq (itemPiece_hSupport_eq p k before s hk hs hload)
  rw [itemFirstColumn_owner]
  exact dimerHIndex_mem_Hsites p.side trackEdgeFrame _ _ false 0 (by omega) 0

theorem itemLastColumn_mem_own_Hsupport (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    (itemLastColumn p k before s hk hs hload).owner ∈
      hSupport (canonicalItemPiece p k before s hk hs hload).word (canonicalItemPiece p k before s hk hs hload).fold := by
  apply mem_of_eq (itemPiece_hSupport_eq p k before s hk hs hload)
  rw [itemLastColumn_owner, ← dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
  exact dimerHIndex_mem_Hsites p.side trackEdgeFrame _ _ false (p.itemDimers s - 1) le_rfl 1

theorem itemPiece_ne_own_firstColumn (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ≠ (itemFirstColumn p k before s hk hs hload).point n :=
  cappedInterval_ne_own_first_innerColumn (itemFirstColumn_ordinary p k before s hk hs hload)
    trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s) (by have h := p.itemDimers_ge s hs; omega)
    false (itemTrackBase_room p k before s hk hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload) i n hn

theorem itemPiece_ne_own_lastColumn (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ≠ (itemLastColumn p k before s hk hs hload).point n :=
  cappedInterval_ne_own_last_innerColumn (itemLastColumn_ordinary p k before s hk hs hload)
    trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s) (by have h := p.itemDimers_ge s hs; omega)
    false (itemTrackBase_room p k before s hk hload) (itemFirstColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload) i n hn

theorem rightFirstColumn_mem_own_Hsupport (p : ConstructionParameters) :
    (rightFirstColumn p).owner ∈ hSupport (canonicalRightPiece p).word (canonicalRightPiece p).fold := by
  apply mem_of_eq (rightPiece_hSupport_eq p)
  exact dimerHIndex_mem_Hsites p.side trackEdgeFrame _ _ false 0 (by omega) 0

theorem rightPiece_ne_own_firstColumn (p : ConstructionParameters)
    (i : Fin (canonicalRightPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalRightPiece p).fold.pos i ≠ (rightFirstColumn p).point n :=
  cappedInterval_ne_own_first_innerColumn (rightFirstColumn_ordinary p) trackEdgeFrame
    (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega) false
    (rightFillerTrackBase_room p) (rightFinalColumn p) rfl
    (by rw [rightPiece_lastHIndex]; exact rightFinalColumn_track_owner p) i n hn

theorem leftLastColumn_mem_own_Hsupport (p : ConstructionParameters) :
    (leftLastColumn p).owner ∈ hSupport (canonicalLeftPiece p).word (canonicalLeftPiece p).fold := by
  apply mem_of_eq (leftPiece_hSupport_eq p)
  apply Finset.mem_insert_of_mem
  apply Finset.mem_erase.mpr
  constructor
  · intro heq
    rw [leftLastColumn_owner] at heq
    have hi := octEdgeZigzag_injective (by have h := p.side_ge; omega) trackEdgeFrame heq
    have hl := p.leftFiller_ge
    omega
  · rw [leftLastColumn_owner, ← leftFillerLast_index]
    exact dimerHIndex_mem_Hsites p.side trackEdgeFrame 0 (p.leftFiller - 1) false (p.leftFiller - 1) le_rfl 1

theorem leftPiece_ne_own_lastColumn (p : ConstructionParameters)
    (i : Fin (canonicalLeftPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalLeftPiece p).fold.pos i ≠ (leftLastColumn p).point n := by
  have hC := leftLastColumn_ordinary p
  have howners : DimerLinkOwnerExcluded p.side trackEdgeFrame 0 (p.leftFiller - 1) false (leftLastColumn p).owner := by
    rw [leftLastColumn_owner, ← leftFillerLast_index]
    exact dimerLinkOwnerExcluded_last (by have h := p.side_ge; omega) trackEdgeFrame 0 (p.leftFiller - 1) false
  apply capped_clear (leftLastColumn p) _ _ (entryLocalColumn p none).seed (leftLastColumn p).seed
    (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p))
    (entryLocalColumn p none).seed_dangling (leftLastColumn p).seed_dangling n hn _ i
  intro j
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs with hj
  · exact inside_clear (leftLastColumn p) _ (leftFillerStart_mem_oct p) n
  · let r : Fin (dimerChain (p.leftFiller - 1 + 1)).length := ⟨j.val, by
      have hlen := leftFiller_word_length p
      have hs := dimerChain_succ_length (p.leftFiller - 1)
      have hj' := j.isLt
      omega⟩
    have h := edgeDimerFold_ne_ordinaryInnerColumn hC trackEdgeFrame 0 (p.leftFiller - 1) false
      (leftFiller_room p) howners r n
    rw [edgeDimerFold_pos] at h
    exact h

theorem exitCapColumn_ne_entry_owner (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) (r : ℕ) :
    (exitCapColumn p k hk).owner ≠ octEdgeZigzag p.side entryEdgeFrame r := by
  rw [exitCapColumn_owner]
  exact (entryEdge_ne_exitEdge_before_corner (by have h := p.side_ge; omega)
    r (10 * p.exitSlot k + 10) (by have h := p.exit_column_triangle_room k; omega)).symm

theorem exitCapColumn_ne_track_owner (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) (r : ℕ) :
    (exitCapColumn p k hk).owner ≠ octEdgeZigzag p.side trackEdgeFrame r := by
  intro heq
  have hy := congrArg (fun x : Site => x.val 1) heq
  change (exitCapColumn p k hk).owner.val 1 = (octEdgeZigzag p.side trackEdgeFrame r).val 1 at hy
  rw [exitCapColumn_owner, exitEdgeZigzag_coordinates (by have h := p.side_ge; omega),
    trackEdgeZigzag_coordinates (by have h := p.side_ge; omega)] at hy
  dsimp [exitEdgeCoordinates, trackEdgeCoordinates] at hy
  omega

theorem exitPiece_lastHIndex (p : ConstructionParameters) (k : ℕ) :
    dimerHIndex (10 * p.exitSlot k + 6) true 2 1 = 10 * p.exitSlot k + 10 := by
  dsimp [dimerHIndex, dimerFlip]

theorem exitCapColumn_mem_own_Hsupport (p : ConstructionParameters) (k : Fin (p.bins + 1)) :
    (exitCapColumn p k.val (by have h := k.isLt; omega)).owner ∈
      hSupport (canonicalSeparatorPiece p k).word (canonicalSeparatorPiece p k).fold := by
  apply mem_of_eq (separatorPiece_hSupport_eq p k)
  apply Finset.mem_union_right
  rw [exitCapColumn_owner, ← exitPiece_lastHIndex]
  exact dimerHIndex_mem_Hsites p.side exitEdgeFrame _ 2 true 2 le_rfl 1

theorem separatorPiece_ne_own_exitColumn (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (i : Fin (canonicalSeparatorPiece p k).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalSeparatorPiece p k).fold.pos i ≠
      (exitCapColumn p k.val (by have h := k.isLt; omega)).point n := by
  have hk : k.val ≤ p.bins := by have h := k.isLt; omega
  let C := exitCapColumn p k.val hk
  have hC : OrdinaryInnerColumn p C := exitCapColumn_ordinary p k.val hk
  have hA : C.owner ∉ edgeDimerHsites p.side entryEdgeFrame (6 * (k.val + 1)) 0 := by
    intro hx
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hx
    exact exitCapColumn_ne_entry_owner p k.val hk _ hr.symm
  have hB : C.owner ∉ edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k.val) 1 := by
    intro hx
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hx
    exact exitCapColumn_ne_track_owner p k.val hk _ hr.symm
  have hD : DimerLinkOwnerExcluded p.side exitEdgeFrame (10 * p.exitSlot k.val + 6) 2 true C.owner := by
    dsimp only [C]
    rw [exitCapColumn_owner, ← exitPiece_lastHIndex]
    exact dimerLinkOwnerExcluded_last (by have h := p.side_ge; omega) exitEdgeFrame _ 2 true
  apply capped_clear C _ _ (entryLocalColumn p (some k)).seed C.seed
    (cappedSeparatorFold_sites p k.val hk _ _ rfl (exitCapColumn_owner p k.val hk))
    (entryLocalColumn p (some k)).seed_dangling C.seed_dangling n hn _ i
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
  · exact fun r => edgeDimerFold_ne_ordinaryInnerColumn hC exitEdgeFrame _ _ true (separatorExit_room p k.val) hD r n

private theorem wordsDisjoint_of_mem_ne (ps : List PositionedWord) (hp : ps.Pairwise WordsDisjoint)
    {u v : PositionedWord} (hu : u ∈ ps) (hv : v ∈ ps) (hne : u ≠ v) : WordsDisjoint u v := by
  revert hp hu hv hne
  induction ps with
  | nil => intro hp hu; cases hu
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

theorem ordinaryColumn_clear_of_pairwise {p : ConstructionParameters} {C : DanglingColumn p.side}
    (hC : OrdinaryInnerColumn p C) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : ((canonicalTaggedBodies p items d ha).map CappedUnit.piece).Pairwise WordsDisjoint)
    (own : PositionedWord) (hown : own ∈ (canonicalTaggedBodies p items d ha).map CappedUnit.piece)
    (howner : C.owner ∈ hSupport own.word own.fold)
    (hself : ∀ i n, 1 ≤ n → own.fold.pos i ≠ C.point n)
    (u : CappedUnit p.side) (hu : u ∈ canonicalTaggedBodies p items d ha)
    (i : Fin u.piece.word.length) (n : ℕ) (hn : 1 ≤ n) : u.piece.fold.pos i ≠ C.point n := by
  by_cases heq : own = u.piece
  · subst own
    exact hself i n hn
  · have hdis := wordsDisjoint_of_mem_ne _ hp hown (List.mem_map.mpr ⟨u, hu, rfl⟩) heq
    have hnot : C.owner ∉ hSupport u.piece.word u.piece.fold := by
      intro hx
      exact Finset.disjoint_left.mp hdis (hSupport_subset_sites (S := own.word) own.fold howner)
        (hSupport_subset_sites (S := u.piece.word) u.piece.fold hx)
    exact canonicalTaggedBodies_property p items d ha _ (canonicalLocal_ordinaryColumn_of_not_mem hC ha n hn) u hu hnot i

theorem canonicalLeftPiece_mem_taggedPieces (p : ConstructionParameters) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    canonicalLeftPiece p ∈ (canonicalTaggedBodies p items d ha).map CappedUnit.piece := by
  rw [canonicalTaggedBodies_pieces_families]
  apply List.mem_flatten.mpr
  refine ⟨[canonicalLeftPiece p], ?_, List.mem_cons_self⟩
  dsimp only [canonicalPieceFamilies]
  apply List.mem_cons_of_mem _
  apply List.mem_cons_of_mem _
  apply List.mem_cons_of_mem _
  exact List.mem_cons_self

theorem canonicalRightPiece_mem_taggedPieces (p : ConstructionParameters) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    canonicalRightPiece p ∈ (canonicalTaggedBodies p items d ha).map CappedUnit.piece := by
  rw [canonicalTaggedBodies_pieces_families]
  apply List.mem_flatten.mpr
  refine ⟨[canonicalRightPiece p], ?_, List.mem_cons_self⟩
  dsimp only [canonicalPieceFamilies]
  apply List.mem_cons_of_mem _
  apply List.mem_cons_of_mem _
  apply List.mem_cons_of_mem _
  apply List.mem_cons_of_mem _
  apply List.mem_cons_of_mem _
  exact List.mem_cons_self

theorem canonicalSeparatorPiece_mem_taggedPieces (p : ConstructionParameters) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) (k : Fin (p.bins + 1)) :
    canonicalSeparatorPiece p k ∈ (canonicalTaggedBodies p items d ha).map CappedUnit.piece := by
  rw [canonicalTaggedBodies_pieces_families]
  apply List.mem_flatten.mpr
  refine ⟨canonicalSeparatorPieces p, ?_, List.mem_ofFn.mpr ⟨k, rfl⟩⟩
  dsimp only [canonicalPieceFamilies]
  apply List.mem_cons_of_mem _
  apply List.mem_cons_of_mem _
  exact List.mem_cons_self

theorem leftLastColumn_clear_of_pairwise (p : ConstructionParameters) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : ((canonicalTaggedBodies p items d ha).map CappedUnit.piece).Pairwise WordsDisjoint)
    (u : CappedUnit p.side) (hu : u ∈ canonicalTaggedBodies p items d ha)
    (i : Fin u.piece.word.length) (n : ℕ) (hn : 1 ≤ n) : u.piece.fold.pos i ≠ (leftLastColumn p).point n :=
  ordinaryColumn_clear_of_pairwise (leftLastColumn_ordinary p) items d ha hp _
    (canonicalLeftPiece_mem_taggedPieces p items d ha)
    (leftLastColumn_mem_own_Hsupport p) (leftPiece_ne_own_lastColumn p) u hu i n hn

theorem itemFirstColumn_clear_of_pairwise (p : ConstructionParameters) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : ((canonicalTaggedBodies p items d ha).map CappedUnit.piece).Pairwise WordsDisjoint)
    (k before s : ℕ) (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (hown : canonicalItemPiece p k before s hk hs hload ∈ (canonicalTaggedBodies p items d ha).map CappedUnit.piece)
    (u : CappedUnit p.side) (hu : u ∈ canonicalTaggedBodies p items d ha)
    (i : Fin u.piece.word.length) (n : ℕ) (hn : 1 ≤ n) : u.piece.fold.pos i ≠ (itemFirstColumn p k before s hk hs hload).point n :=
  ordinaryColumn_clear_of_pairwise (itemFirstColumn_ordinary p k before s hk hs hload) items d ha hp _ hown
    (itemFirstColumn_mem_own_Hsupport p k before s hk hs hload) (itemPiece_ne_own_firstColumn p k before s hk hs hload) u hu i n hn

theorem itemLastColumn_clear_of_pairwise (p : ConstructionParameters) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : ((canonicalTaggedBodies p items d ha).map CappedUnit.piece).Pairwise WordsDisjoint)
    (k before s : ℕ) (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (hown : canonicalItemPiece p k before s hk hs hload ∈ (canonicalTaggedBodies p items d ha).map CappedUnit.piece)
    (u : CappedUnit p.side) (hu : u ∈ canonicalTaggedBodies p items d ha)
    (i : Fin u.piece.word.length) (n : ℕ) (hn : 1 ≤ n) : u.piece.fold.pos i ≠ (itemLastColumn p k before s hk hs hload).point n :=
  ordinaryColumn_clear_of_pairwise (itemLastColumn_ordinary p k before s hk hs hload) items d ha hp _ hown
    (itemLastColumn_mem_own_Hsupport p k before s hk hs hload) (itemPiece_ne_own_lastColumn p k before s hk hs hload) u hu i n hn

theorem rightFirstColumn_clear_of_pairwise (p : ConstructionParameters) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : ((canonicalTaggedBodies p items d ha).map CappedUnit.piece).Pairwise WordsDisjoint)
    (u : CappedUnit p.side) (hu : u ∈ canonicalTaggedBodies p items d ha)
    (i : Fin u.piece.word.length) (n : ℕ) (hn : 1 ≤ n) : u.piece.fold.pos i ≠ (rightFirstColumn p).point n :=
  ordinaryColumn_clear_of_pairwise (rightFirstColumn_ordinary p) items d ha hp _
    (canonicalRightPiece_mem_taggedPieces p items d ha)
    (rightFirstColumn_mem_own_Hsupport p) (rightPiece_ne_own_firstColumn p) u hu i n hn

theorem exitCapColumn_clear_of_pairwise (p : ConstructionParameters) (items : List ℕ) (d : PackedBins p items)
    (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (hp : ((canonicalTaggedBodies p items d ha).map CappedUnit.piece).Pairwise WordsDisjoint)
    (k : Fin (p.bins + 1))
    (u : CappedUnit p.side) (hu : u ∈ canonicalTaggedBodies p items d ha)
    (i : Fin u.piece.word.length) (n : ℕ) (hn : 1 ≤ n) :
    u.piece.fold.pos i ≠ (exitCapColumn p k.val (by have h := k.isLt; omega)).point n :=
  ordinaryColumn_clear_of_pairwise (exitCapColumn_ordinary p k.val (by have h := k.isLt; omega)) items d ha hp _
    (canonicalSeparatorPiece_mem_taggedPieces p items d ha k)
    (exitCapColumn_mem_own_Hsupport p k) (separatorPiece_ne_own_exitColumn p k) u hu i n hn

theorem terminalWordPiece_ne_any_positiveColumn (p : ConstructionParameters) (C : DanglingColumn p.side)
    (i : Fin (terminalWordPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (terminalWordPiece p).fold.pos i ≠ C.point n := by
  change (if i.val = 0 then (terminalColumn p).owner else (terminalColumn p).seed) ≠ _
  split_ifs
  · exact inside_clear C _ (terminalColumn p).owner_mem n
  · exact FarField.dangling_ne_positive_column (terminalColumn p).seed_dangling C n hn

end ProteinFolding.Tetrahedral.NearField

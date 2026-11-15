import ProteinFolding.Tetrahedral.NearFieldSeparatorIntervalSeparation
import ProteinFolding.Tetrahedral.NearFieldTrackFillerSeparation

/-! Actual separator/filler/item cross relations, with every local cap. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 500000
set_option maxRecDepth 4096

theorem separatorHsupport_disjoint_track_interval (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (base n : ℕ) (hn : 0 < n) (hroom : base + 2 * n ≤ 2 * p.side - 1)
    (hcenter : Disjoint (edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k) 1)
      (edgeDimerHsites p.side trackEdgeFrame base (n - 1))) :
    Disjoint (hSupport (p.separatorWord k) (separatorFold p k hk))
      (edgeDimerHsites p.side trackEdgeFrame base (n - 1)) := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have he := p.entry_column_triangle_room k hk
  have hx := p.exit_column_triangle_room k
  rw [separatorFold_hSupport, Finset.disjoint_union_left, Finset.disjoint_union_left]
  exact ⟨⟨edgeDimerHsites_disjoint_other_pair hm entryEdgeFrame trackEdgeFrame
    (6 * (k + 1)) 0 base (n - 1) (by omega) (by omega) (by omega) (Or.inl (by decide)), hcenter⟩,
    edgeDimerHsites_disjoint_other_pair hm exitEdgeFrame trackEdgeFrame
      (10 * p.exitSlot k + 6) 2 base (n - 1) (by omega) (by omega) (by omega) (Or.inl (by decide))⟩

theorem separatorHsupport_disjoint_item (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (b before s : ℕ) (hb : b < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    Disjoint (hSupport (p.separatorWord k) (separatorFold p k hk))
      (edgeDimerHsites p.side trackEdgeFrame (itemTrackBase p b before) (p.itemDimers s - 1)) := by
  have hn := p.itemDimers_ge s hs
  apply separatorHsupport_disjoint_track_interval p k hk _ _ (by omega) (itemTrackBase_room p b before s hb hload)
  apply edgeDimerHsites_disjoint_intervals (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame
  by_cases hkb : k ≤ b
  · left
    have hmono := p.separatorIndex_mono hkb
    dsimp [itemTrackBase]
    omega
  · right
    have hend := itemTrackBase_end_le p b before s hload
    have hmono := p.separatorIndex_mono (show b + 1 ≤ k by omega)
    omega

theorem separatorHsupport_disjoint_right (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Disjoint (hSupport (p.separatorWord k) (separatorFold p k hk))
      (edgeDimerHsites p.side trackEdgeFrame (rightFillerTrackBase p) (p.rightFiller - 1)) := by
  have hn := p.rightFiller_ge
  apply separatorHsupport_disjoint_track_interval p k hk _ _ (by omega) (rightFillerTrackBase_room p)
  apply edgeDimerHsites_disjoint_intervals (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame
  left
  have hmono := p.separatorIndex_mono hk
  dsimp [rightFillerTrackBase]
  omega

theorem separatorHsupport_disjoint_leftTrack (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Disjoint (hSupport (p.separatorWord k) (separatorFold p k hk))
      (edgeDimerHsites p.side trackEdgeFrame 0 (p.leftFiller - 1)) := by
  have hn := p.leftFiller_ge
  have hr := leftFiller_room p
  apply separatorHsupport_disjoint_track_interval p k hk 0 p.leftFiller (by omega) (by omega)
  apply edgeDimerHsites_disjoint_intervals (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame
  right
  dsimp [ConstructionParameters.separatorIndex]
  omega

theorem entryTwo_not_separator_hSupport (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    octEdgeZigzag p.side entryEdgeFrame 2 ∉ hSupport (p.separatorWord k) (separatorFold p k hk) := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  have hx := p.exit_column_triangle_room k
  rw [separatorFold_hSupport]
  intro h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact edgeDimerHsites_not_mem_of_indices (by omega) entryEdgeFrame (6 * (k + 1)) 0 2
        (fun t ht => by omega) h
    · exact entryTwo_not_track_interval p (2 * p.separatorIndex k) 2 (by decide)
        (separatorCenter_room p k hk) h
  · exact edgeDimerHsites_not_mem_other_pair hm exitEdgeFrame (10 * p.exitSlot k + 6) 2
      (by omega) (by omega) entryEdgeFrame 2 (by omega) (Or.inl (by decide)) h

theorem canonicalItemPiece_ne_separatorPiece (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (b before s : ℕ) (hb : b < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (i : Fin (canonicalItemPiece p b before s hb hs hload).word.length)
    (j : Fin (canonicalSeparatorPiece p k).word.length) :
    (canonicalItemPiece p b before s hb hs hload).fold.pos i ≠ (canonicalSeparatorPiece p k).fold.pos j :=
  cappedInterval_ne_cappedSeparator_of_Hdis p k.val (by have h := k.isLt; omega)
    trackEdgeFrame (itemTrackBase p b before) (p.itemDimers s) (by have h := p.itemDimers_ge s hs; omega)
    false (itemTrackBase_room p b before s hb hload) (Or.inl (by decide))
    (separatorHsupport_disjoint_item p k.val (by have h := k.isLt; omega) b before s hb hs hload)
    (itemFirstColumn p b before s hb hs hload) (itemLastColumn p b before s hb hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p b before s hb hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)];
        exact itemLastColumn_owner p b before s hb hs hload)
    (entryLocalColumn p (some k)) (exitCapColumn p k.val (by have h := k.isLt; omega)) rfl
    (exitCapColumn_owner p k.val (by have h := k.isLt; omega)) i j

theorem canonicalSeparatorPiece_itemPiece_disjoint (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (b before s : ℕ) (hb : b < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    WordsDisjoint (canonicalSeparatorPiece p k) (canonicalItemPiece p b before s hb hs hload) :=
  ((foldSites_disjoint_iff _ _).mpr (canonicalItemPiece_ne_separatorPiece p k b before s hb hs hload)).symm

private theorem rightLast_dimerOwner (p : ConstructionParameters) :
    (rightFinalColumn p).owner = octEdgeZigzag p.side trackEdgeFrame
      (dimerHIndex (rightFillerTrackBase p) false (p.rightFiller - 1) 1) := by
  rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
  have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
  have hi : rightFillerTrackBase p + 2 * p.rightFiller - 1 = 2 * p.side - 3 := by
    dsimp [rightFillerTrackBase]
    omega
  rw [hi]
  exact rightFinalColumn_track_owner p

theorem canonicalRightPiece_ne_separatorPiece (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (i : Fin (canonicalRightPiece p).word.length) (j : Fin (canonicalSeparatorPiece p k).word.length) :
    (canonicalRightPiece p).fold.pos i ≠ (canonicalSeparatorPiece p k).fold.pos j :=
  cappedInterval_ne_cappedSeparator_of_Hdis p k.val (by have h := k.isLt; omega)
    trackEdgeFrame (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega)
    false (rightFillerTrackBase_room p) (Or.inl (by decide))
    (separatorHsupport_disjoint_right p k.val (by have h := k.isLt; omega))
    (rightFirstColumn p) (rightFinalColumn p) rfl (rightLast_dimerOwner p)
    (entryLocalColumn p (some k)) (exitCapColumn p k.val (by have h := k.isLt; omega)) rfl
    (exitCapColumn_owner p k.val (by have h := k.isLt; omega)) i j

theorem canonicalSeparatorPiece_rightPiece_disjoint (p : ConstructionParameters) (k : Fin (p.bins + 1)) :
    WordsDisjoint (canonicalSeparatorPiece p k) (canonicalRightPiece p) :=
  ((foldSites_disjoint_iff _ _).mpr (canonicalRightPiece_ne_separatorPiece p k)).symm

theorem canonicalLeftPiece_ne_separatorPiece (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (i : Fin (canonicalLeftPiece p).word.length) (j : Fin (canonicalSeparatorPiece p k).word.length) :
    (canonicalLeftPiece p).fold.pos i ≠ (canonicalSeparatorPiece p k).fold.pos j := by
  have hk : k.val ≤ p.bins := by have h := k.isLt; omega
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  let C := entryLocalColumn p (some k)
  let D := exitCapColumn p k.val hk
  have hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k.val + 1)) := rfl
  have hD := exitCapColumn_owner p k.val hk
  have hdis := separatorHsupport_disjoint_leftTrack p k.val hk
  have hEnot := entryTwo_not_separator_hSupport p k.val hk
  have hRnot : (leftLastColumn p).owner ∉ hSupport (p.separatorWord k.val) (separatorFold p k.val hk) := by
    intro h
    apply Finset.disjoint_left.mp hdis h
    rw [leftLastColumn_owner p, ← leftFillerLast_index p]
    exact dimerHIndex_mem_Hsites p.side trackEdgeFrame 0 (p.leftFiller - 1) false (p.leftFiller - 1) le_rfl 1
  apply frameTrack_property_of_capped_sites (canonicalLeftPiece p).fold (leftFillerFold p)
    (entryLocalColumn p none).seed (leftLastColumn p).seed
    (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p))
    (fun x => x ≠ (canonicalSeparatorPiece p k).fold.pos j) _ _ _ i
  · exact (cappedSeparatorFold_ne_cap_of_owner_not_mem_all p k.val hk C D hC hD
      (entryLocalColumn p none) hEnot j).symm
  · intro r
    by_cases hr : r.val = 0
    · rw [leftFillerFold_first p r hr]
      exact (cappedSeparatorFold_ne_octSite_of_not_mem_hSupport p k.val hk C D hC hD
        _ (leftFillerStart_mem_oct p) hEnot j).symm
    · rw [leftFillerFold_pos, leftFillerCurve, if_neg hr]
      let s : Fin (dimerChain (p.leftFiller - 1 + 1)).length := ⟨r.val, by
        have h1 := dimerChain_succ_length (p.leftFiller - 1)
        have h2 := leftFiller_word_length p
        have h3 := r.isLt
        omega⟩
      have h := edgeDimerFold_ne_cappedSeparator_of_Hdis p k.val hk trackEdgeFrame 0
        (p.leftFiller - 1) false (leftFiller_room p) (Or.inl (by decide)) hdis C D hC hD s j
      rw [edgeDimerFold_pos] at h
      exact h
  · exact (cappedSeparatorFold_ne_cap_of_owner_not_mem_all p k.val hk C D hC hD
      (leftLastColumn p) hRnot j).symm

theorem canonicalSeparatorPiece_leftPiece_disjoint (p : ConstructionParameters) (k : Fin (p.bins + 1)) :
    WordsDisjoint (canonicalSeparatorPiece p k) (canonicalLeftPiece p) :=
  ((foldSites_disjoint_iff _ _).mpr (canonicalLeftPiece_ne_separatorPiece p k)).symm

end ProteinFolding.Tetrahedral.NearField

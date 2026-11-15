import ProteinFolding.Tetrahedral.NearFieldCanonicalRightPiece
import ProteinFolding.Tetrahedral.NearFieldItemFamily
import ProteinFolding.Tetrahedral.NearFieldLeftFillerSupport
import ProteinFolding.Tetrahedral.NearFieldFrameTrackCoreSeparation

/-! The special left filler and the ordinary item/right intervals are
pairwise disjoint as complete capped local words. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

theorem cappedIntervalDimerFold_ne_cap_of_owner_not_mem {m : ℕ} (hm : 1 ≤ m)
    (F : OctEdgeFrame) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1))
    (E : DanglingColumn m) (hnot : E.owner ∉ edgeDimerHsites m F base (n - 1))
    (i : Fin (capWord (dimerChain n)).length) :
    (cappedIntervalDimerFold hm F base n hn reverse hroom C D hC hD).pos i ≠ E.seed :=
  transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold hm F base (n - 1) reverse (by omega) C D hC hD) (fun x => x ≠ E.seed)
    (cappedEdgeDimerFold_ne_cap_of_owner_not_mem hm F base (n - 1) reverse (by omega) C D hC hD E hnot) i

theorem cappedIntervalDimerFold_ne_octSite_of_not_mem {m : ℕ} (hm : 1 ≤ m)
    (F : OctEdgeFrame) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1))
    (x : Site) (hx : x ∈ octahedron m) (hnot : x ∉ edgeDimerHsites m F base (n - 1))
    (i : Fin (capWord (dimerChain n)).length) :
    (cappedIntervalDimerFold hm F base n hn reverse hroom C D hC hD).pos i ≠ x :=
  transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold hm F base (n - 1) reverse (by omega) C D hC hD) (fun y => y ≠ x)
    (cappedEdgeDimerFold_ne_octSite_of_not_mem_Hsites hm F base (n - 1) reverse (by omega) C D hC hD x hx hnot) i

theorem edgeDimerFold_ne_cappedInterval_of_Hdis {m : ℕ} (hm : 1 ≤ m) (F G : OctEdgeFrame)
    (base q base' n : ℕ) (hn : 0 < n) (reverse reverse' : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (hroom' : base' + 2 * n ≤ 2 * m - 1)
    (hdis : Disjoint (edgeDimerHsites m F base q) (edgeDimerHsites m G base' (n - 1)))
    (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m G (dimerHIndex base' reverse' 0 0))
    (hD : D.owner = octEdgeZigzag m G (dimerHIndex base' reverse' (n - 1) 1))
    (i : Fin (dimerChain (q + 1)).length) (r : Fin (capWord (dimerChain n)).length) :
    (edgeDimerFold hm F base q reverse hroom).pos i ≠
      (cappedIntervalDimerFold hm G base' n hn reverse' hroom' C D hC hD).pos r := by
  have hCm : C.owner ∈ edgeDimerHsites m G base' (n - 1) := by
    rw [hC]
    exact dimerHIndex_mem_Hsites m G base' (n - 1) reverse' 0 (by omega) 0
  have hDm : D.owner ∈ edgeDimerHsites m G base' (n - 1) := by
    rw [hD]
    exact dimerHIndex_mem_Hsites m G base' (n - 1) reverse' (n - 1) le_rfl 1
  have hCnot : C.owner ∉ edgeDimerHsites m F base q := fun h => Finset.disjoint_left.mp hdis h hCm
  have hDnot : D.owner ∉ edgeDimerHsites m F base q := fun h => Finset.disjoint_left.mp hdis h hDm
  unfold cappedIntervalDimerFold
  apply transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold hm G base' (n - 1) reverse' (by omega) C D hC hD)
    (fun x => (edgeDimerFold hm F base q reverse hroom).pos i ≠ x)
  intro j
  exact cappedEdgeDimerFold_property hm G base' (n - 1) reverse' (by omega) C D hC hD _
    (edgeDimerFold_ne_cap_of_owner_not_mem hm F base q reverse hroom C hCnot i)
    (fun s => edgeDimerFolds_disjoint hm F G base q base' (n - 1) reverse reverse' hroom (by omega) hdis i s)
    (edgeDimerFold_ne_cap_of_owner_not_mem hm F base q reverse hroom D hDnot i) j

theorem entryTwo_not_track_interval (p : ConstructionParameters) (base n : ℕ) (hn : 0 < n)
    (hroom : base + 2 * n ≤ 2 * p.side - 1) :
    octEdgeZigzag p.side entryEdgeFrame 2 ∉ edgeDimerHsites p.side trackEdgeFrame base (n - 1) := by
  have hm : 3 ≤ p.side := by have h := p.side_ge; omega
  intro hx
  obtain ⟨t, _, heq⟩ := Finset.mem_image.mp hx
  have ht := t.isLt
  exact innerEdgePoint_ne_other_pair hm entryEdgeFrame 2 (by omega) (by have h := p.side_ge; omega)
    trackEdgeFrame (base + t.val) (by omega) (Or.inl (by decide)) heq.symm

theorem cappedLeftFillerFold_ne_trackInterval (p : ConstructionParameters) (L R : DanglingColumn p.side)
    (hL : L.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hR : R.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2))
    (base n : ℕ) (hn : 0 < n) (hroom : base + 2 * n ≤ 2 * p.side - 1)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side trackEdgeFrame (dimerHIndex base false 0 0))
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (dimerHIndex base false (n - 1) 1))
    (hdis : Disjoint (edgeDimerHsites p.side trackEdgeFrame 0 (p.leftFiller - 1))
      (edgeDimerHsites p.side trackEdgeFrame base (n - 1)))
    (i : Fin (capWord (dimerChain p.leftFiller)).length) (r : Fin (capWord (dimerChain n)).length) :
    (cappedLeftFillerFold p L R hL hR).pos i ≠
      (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
        trackEdgeFrame base n hn false hroom C D hC hD).pos r := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hEnot := entryTwo_not_track_interval p base n hn hroom
  have hRmem : R.owner ∈ edgeDimerHsites p.side trackEdgeFrame 0 (p.leftFiller - 1) := by
    rw [hR, ← leftFillerLast_index p]
    exact dimerHIndex_mem_Hsites p.side trackEdgeFrame 0 (p.leftFiller - 1) false (p.leftFiller - 1) le_rfl 1
  have hRnot := fun h => Finset.disjoint_left.mp hdis hRmem h
  let g := cappedIntervalDimerFold hm trackEdgeFrame base n hn false hroom C D hC hD
  apply frameTrack_property_of_capped_sites (cappedLeftFillerFold p L R hL hR) (leftFillerFold p)
    L.seed R.seed (cappedLeftFillerFold_sites p L R hL hR) (fun x => x ≠ g.pos r) _ _ _ i
  · exact (cappedIntervalDimerFold_ne_cap_of_owner_not_mem hm trackEdgeFrame base n hn false hroom C D hC hD
      L (by rw [hL]; exact hEnot) r).symm
  · intro j
    by_cases hj : j.val = 0
    · rw [leftFillerFold_first p j hj]
      exact (cappedIntervalDimerFold_ne_octSite_of_not_mem hm trackEdgeFrame base n hn false hroom C D hC hD
        _ (leftFillerStart_mem_oct p) hEnot r).symm
    · rw [leftFillerFold_pos, leftFillerCurve, if_neg hj]
      let s : Fin (dimerChain (p.leftFiller - 1 + 1)).length := ⟨j.val, by
        have h1 := dimerChain_succ_length (p.leftFiller - 1)
        have h2 := leftFiller_word_length p
        have h3 := j.isLt
        omega⟩
      have h := edgeDimerFold_ne_cappedInterval_of_Hdis hm trackEdgeFrame trackEdgeFrame
        0 (p.leftFiller - 1) base n hn false false (leftFiller_room p) hroom hdis C D hC hD s r
      rw [edgeDimerFold_pos] at h
      exact h
  · exact (cappedIntervalDimerFold_ne_cap_of_owner_not_mem hm trackEdgeFrame base n hn false hroom C D hC hD
      R hRnot r).symm

theorem leftTrackHsites_disjoint_item (p : ConstructionParameters) (k before s : ℕ) (hs : 0 < s) :
    Disjoint (edgeDimerHsites p.side trackEdgeFrame 0 (p.leftFiller - 1))
      (edgeDimerHsites p.side trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s - 1)) := by
  apply edgeDimerHsites_disjoint_intervals (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame
  left
  have hl := p.leftFiller_ge
  dsimp [itemTrackBase, ConstructionParameters.separatorIndex]
  omega

theorem canonicalLeftPiece_itemPiece_disjoint (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    WordsDisjoint (canonicalLeftPiece p) (canonicalItemPiece p k before s hk hs hload) := by
  apply (foldSites_disjoint_iff _ _).mpr
  exact cappedLeftFillerFold_ne_trackInterval p _ _ rfl (leftLastColumn_owner p)
    (itemTrackBase p k before) (p.itemDimers s) (by have h := p.itemDimers_ge s hs; omega)
    (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by
      rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
      exact itemLastColumn_owner p k before s hk hs hload)
    (leftTrackHsites_disjoint_item p k before s hs)

private theorem trackA_owner {m : ℕ} (hm : 1 ≤ m) (a : ℕ) (ha : a < m) :
    (trackAColumn hm a ha).owner = octEdgeZigzag m trackEdgeFrame (2 * a) := rfl

private theorem rightFirst_dimerOwner (p : ConstructionParameters) :
    (rightFirstColumn p).owner = octEdgeZigzag p.side trackEdgeFrame
      (dimerHIndex (rightFillerTrackBase p) false 0 0) := by
  have hi : 2 * (p.separatorIndex p.bins + 2) =
      dimerHIndex (rightFillerTrackBase p) false 0 0 := by
    dsimp [dimerHIndex, dimerFlip, rightFillerTrackBase]
  dsimp only [rightFirstColumn]
  rw [trackA_owner]
  exact congrArg (octEdgeZigzag p.side trackEdgeFrame) hi

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

theorem leftTrackHsites_disjoint_right (p : ConstructionParameters) :
    Disjoint (edgeDimerHsites p.side trackEdgeFrame 0 (p.leftFiller - 1))
      (edgeDimerHsites p.side trackEdgeFrame (rightFillerTrackBase p) (p.rightFiller - 1)) := by
  apply edgeDimerHsites_disjoint_intervals (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame
  left
  have hl := p.leftFiller_ge
  dsimp [rightFillerTrackBase, ConstructionParameters.separatorIndex]
  omega

theorem canonicalLeftPiece_rightPiece_disjoint (p : ConstructionParameters) :
    WordsDisjoint (canonicalLeftPiece p) (canonicalRightPiece p) := by
  apply (foldSites_disjoint_iff _ _).mpr
  exact cappedLeftFillerFold_ne_trackInterval p (entryLocalColumn p none) (leftLastColumn p)
    rfl (leftLastColumn_owner p) (rightFillerTrackBase p) p.rightFiller
    (by have h := p.rightFiller_ge; omega) (rightFillerTrackBase_room p)
    (rightFirstColumn p) (rightFinalColumn p) (rightFirst_dimerOwner p) (rightLast_dimerOwner p)
    (leftTrackHsites_disjoint_right p)

theorem itemHsites_disjoint_right (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    Disjoint (edgeDimerHsites p.side trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s - 1))
      (edgeDimerHsites p.side trackEdgeFrame (rightFillerTrackBase p) (p.rightFiller - 1)) := by
  have hend := itemTrackBase_end_le p k before s hload
  have hmono := p.separatorIndex_mono (show k + 1 ≤ p.bins by omega)
  have hn := p.itemDimers_ge s hs
  apply edgeDimerHsites_disjoint_intervals (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame
  left
  dsimp [rightFillerTrackBase]
  omega

theorem canonicalItemPiece_rightPiece_disjoint (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    WordsDisjoint (canonicalItemPiece p k before s hk hs hload) (canonicalRightPiece p) :=
  cappedIntervalDimerFolds_disjoint (m := p.side) (by have h := p.side_ge; omega)
    trackEdgeFrame trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s)
    (rightFillerTrackBase p) p.rightFiller
    (by have h := p.itemDimers_ge s hs; omega) (by have h := p.rightFiller_ge; omega)
    false false (itemTrackBase_room p k before s hk hload) (rightFillerTrackBase_room p)
    (itemHsites_disjoint_right p k before s hk hs hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (rightFirstColumn p) (rightFinalColumn p)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by
      rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
      exact itemLastColumn_owner p k before s hk hs hload)
    (rightFirst_dimerOwner p) (rightLast_dimerOwner p)

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.NearFieldEntryCapFamily
import ProteinFolding.Tetrahedral.NearFieldCanonicalSeparatorPieces
import ProteinFolding.Tetrahedral.NearFieldCanonicalRightPiece
import ProteinFolding.Tetrahedral.NearFieldFrameTrackCoreSeparation
import ProteinFolding.Tetrahedral.FarFieldMixedCaps

/-! Positive-height clearance of each selected borrowed entry column from
the actual separator and reserved track words, including their local caps. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096

attribute [local irreducible] ConstructionParameters.side

private theorem trackA_owner {m : ℕ} (hm : 1 ≤ m) (a : ℕ) (ha : a < m) :
    (trackAColumn hm a ha).owner = octEdgeZigzag m trackEdgeFrame (2 * a) := rfl

private theorem inside_ne_selected (p : ConstructionParameters) (a : EntryCapIndex p)
    (x : Site) (hx : x ∈ octahedron p.side) (n : ℕ) :
    x ≠ (selectedEntryColumn p a).point n := by
  intro heq
  rw [heq] at hx
  exact (selectedEntryColumn p a).point_outside n hx

theorem edgeDimerFold_ne_selectedEntryColumn (p : ConstructionParameters) (a : EntryCapIndex p)
    (F : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * p.side - 1)
    (hpair : q = 0 ∨ F.k ≠ 2 ∨ F.j ≠ 3)
    (i : Fin (dimerChain (q + 1)).length) (n : ℕ) (hn : 1 ≤ n) :
    (edgeDimerFold (by have h := p.side_ge; omega) F base q reverse hroom).pos i ≠
      (selectedEntryColumn p a).point n := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  rcases edgeDimerFold_pos_cases hm F base q reverse hroom i with
    ⟨j, hj, s, hs⟩ | ⟨j, hj, s, hs⟩
  · rw [hs]
    exact inside_ne_selected p a _
      (edgeDimerHsites_subset_oct hm F base q hroom
        (dimerHIndex_mem_Hsites p.side F base q reverse j hj s)) n
  · rw [hs]
    have hb := dimerLinkIndex_bounds base reverse j
    have hp : F.k ≠ 2 ∨ F.j ≠ 3 := by
      rcases hpair with h | h
      · omega
      · exact h
    exact edgePPPFold_ne_selectedEntryColumn p a F _ (by omega) hp s n hn

theorem cappedInterval_ne_selectedEntryColumn (p : ConstructionParameters) (a : EntryCapIndex p)
    (F : OctEdgeFrame) (base l : ℕ) (hl : 0 < l) (reverse : Bool)
    (hroom : base + 2 * l ≤ 2 * p.side - 1) (hpair : F.k ≠ 2 ∨ F.j ≠ 3)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (l - 1) 1))
    (i : Fin (capWord (dimerChain l)).length) (n : ℕ) (hn : 1 ≤ n) :
    (cappedIntervalDimerFold (by have h := p.side_ge; omega) F base l hl reverse hroom C D hC hD).pos i ≠
      (selectedEntryColumn p a).point n := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hroom' : base + 2 * (l - 1 + 1) ≤ 2 * p.side - 1 := by omega
  exact transportWordFold_property (congrArg capWord (positive_dimer_word l hl))
    (cappedEdgeDimerFold hm F base (l - 1) reverse hroom' C D hC hD)
    (fun x => x ≠ (selectedEntryColumn p a).point n)
    (cappedEdgeDimerFold_property hm F base (l - 1) reverse hroom' C D hC hD
      (fun x => x ≠ (selectedEntryColumn p a).point n)
      (FarField.dangling_ne_positive_column C.seed_dangling _ n hn)
      (fun j => edgeDimerFold_ne_selectedEntryColumn p a F base (l - 1) reverse hroom' (Or.inr hpair) j n hn)
      (FarField.dangling_ne_positive_column D.seed_dangling _ n hn)) i

theorem leftFillerFold_ne_selectedEntryColumn (p : ConstructionParameters) (a : EntryCapIndex p)
    (i : Fin (dimerChain p.leftFiller).length) (n : ℕ) (hn : 1 ≤ n) :
    (leftFillerFold p).pos i ≠ (selectedEntryColumn p a).point n := by
  rw [leftFillerFold_pos, leftFillerCurve]
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    exact inside_ne_selected p a _ (leftFillerStart_mem_oct p) n
  · rw [if_neg hi]
    let j : Fin (dimerChain (p.leftFiller - 1 + 1)).length := ⟨i.val, by
      have hl := leftFiller_word_length p
      have hs := dimerChain_succ_length (p.leftFiller - 1)
      have hi' := i.isLt
      omega⟩
    have h := edgeDimerFold_ne_selectedEntryColumn p a trackEdgeFrame 0 (p.leftFiller - 1) false
      (leftFiller_room p) (Or.inr (Or.inl (by decide))) j n hn
    rw [edgeDimerFold_pos] at h
    exact h

theorem canonicalLeftPiece_ne_selectedEntryColumn (p : ConstructionParameters) (a : EntryCapIndex p)
    (i : Fin (canonicalLeftPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalLeftPiece p).fold.pos i ≠ (selectedEntryColumn p a).point n :=
  frameTrack_property_of_capped_sites (canonicalLeftPiece p).fold (leftFillerFold p)
    (entryLocalColumn p none).seed (leftLastColumn p).seed
    (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p))
    (fun x => x ≠ (selectedEntryColumn p a).point n)
    (FarField.dangling_ne_positive_column (entryLocalColumn p none).seed_dangling _ n hn)
    (fun j => leftFillerFold_ne_selectedEntryColumn p a j n hn)
    (FarField.dangling_ne_positive_column (leftLastColumn p).seed_dangling _ n hn) i

theorem canonicalItemPiece_ne_selectedEntryColumn (p : ConstructionParameters) (a : EntryCapIndex p)
    (k before s : ℕ) (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ≠ (selectedEntryColumn p a).point n :=
  cappedInterval_ne_selectedEntryColumn p a trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s)
    (by have h := p.itemDimers_ge s hs; omega) false (itemTrackBase_room p k before s hk hload)
    (Or.inl (by decide)) (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
        exact itemLastColumn_owner p k before s hk hs hload) i n hn

theorem canonicalRightPiece_ne_selectedEntryColumn (p : ConstructionParameters) (a : EntryCapIndex p)
    (i : Fin (canonicalRightPiece p).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalRightPiece p).fold.pos i ≠ (selectedEntryColumn p a).point n := by
  have hfirst : (rightFirstColumn p).owner = octEdgeZigzag p.side trackEdgeFrame
      (dimerHIndex (rightFillerTrackBase p) false 0 0) := by
    have hi : 2 * (p.separatorIndex p.bins + 2) =
        dimerHIndex (rightFillerTrackBase p) false 0 0 := by
      dsimp [dimerHIndex, dimerFlip, rightFillerTrackBase]
    dsimp only [rightFirstColumn]
    rw [trackA_owner]
    exact congrArg (octEdgeZigzag p.side trackEdgeFrame) hi
  have hlast : (rightFinalColumn p).owner = octEdgeZigzag p.side trackEdgeFrame
      (dimerHIndex (rightFillerTrackBase p) false (p.rightFiller - 1) 1) := by
    rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
    have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := by
      simp only [ConstructionParameters.side]
    have hi : rightFillerTrackBase p + 2 * p.rightFiller - 1 = 2 * p.side - 3 := by
      dsimp [rightFillerTrackBase]
      omega
    rw [hi]
    exact rightFinalColumn_track_owner p
  exact cappedInterval_ne_selectedEntryColumn p a trackEdgeFrame (rightFillerTrackBase p) p.rightFiller
    (by have h := p.rightFiller_ge; omega) false (rightFillerTrackBase_room p) (Or.inl (by decide))
    (rightFirstColumn p) (rightFinalColumn p) hfirst hlast i n hn

theorem separatorFold_ne_selectedEntryColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (a : EntryCapIndex p) (i : Fin (p.separatorWord k).length) (n : ℕ) (hn : 1 ≤ n) :
    (separatorFold p k hk).pos i ≠ (selectedEntryColumn p a).point n := by
  apply separatorFold_property p k hk (fun x => x ≠ (selectedEntryColumn p a).point n) _ _ _ _ _ i
  · exact fun j => edgeDimerFold_ne_selectedEntryColumn p a entryEdgeFrame _ 0 false
      (separatorEntry_room p k hk) (Or.inl rfl) j n hn
  · intro j
    rw [entryTetherWordFold_pos]
    exact entryTetherFold_ne_selectedEntryColumn p k hk a n _
  · exact fun j => edgeDimerFold_ne_selectedEntryColumn p a trackEdgeFrame _ 1 true
      (separatorCenter_room p k hk) (Or.inr (Or.inl (by decide))) j n hn
  · intro j
    rw [exitTetherWordFold_pos]
    exact exitTetherFold_ne_selectedEntryColumn p k hk a n _
  · exact fun j => edgeDimerFold_ne_selectedEntryColumn p a exitEdgeFrame _ 2 true
      (separatorExit_room p k) (Or.inr (Or.inl (by decide))) j n hn

theorem canonicalSeparatorPiece_ne_selectedEntryColumn (p : ConstructionParameters)
    (k : Fin (p.bins + 1)) (a : EntryCapIndex p)
    (i : Fin (canonicalSeparatorPiece p k).word.length) (n : ℕ) (hn : 1 ≤ n) :
    (canonicalSeparatorPiece p k).fold.pos i ≠ (selectedEntryColumn p a).point n := by
  have hk : k.val ≤ p.bins := by have h := k.isLt; omega
  let C := entryLocalColumn p (some k)
  let D := exitCapColumn p k.val hk
  exact frameTrack_property_of_capped_sites (canonicalSeparatorPiece p k).fold (separatorFold p k.val hk)
    C.seed D.seed (cappedSeparatorFold_sites p k.val hk C D rfl (exitCapColumn_owner p k.val hk))
    (fun x => x ≠ (selectedEntryColumn p a).point n)
    (FarField.dangling_ne_positive_column C.seed_dangling _ n hn)
    (fun j => separatorFold_ne_selectedEntryColumn p k.val hk a j n hn)
    (FarField.dangling_ne_positive_column D.seed_dangling _ n hn) i

end ProteinFolding.Tetrahedral.NearField

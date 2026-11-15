import ProteinFolding.Tetrahedral.NearFieldFrameTrackCoreSeparation
import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import ProteinFolding.Tetrahedral.NearFieldActualFrameFold
import ProteinFolding.Tetrahedral.NearFieldCanonicalTrackPieces

/-! Complete capped-frame separation for actual inner track intervals
and every actual item. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem cappedInterval_ne_frameFold_of_exclusions (p : ConstructionParameters)
    (F : OctEdgeFrame) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * p.side - 1) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side F (dimerHIndex base reverse (n - 1) 1))
    (hH : ∀ j : FrameHRunIndex p, ∀ s : Fin (frameHRunWord p j).length,
      (frameHRunFold p j).pos s ∉ edgeDimerHsites p.side F base (n - 1))
    (hstart : ∀ j : FrameLinkIndex p,
      frameStartH p.side (frameLinkParameter j) (frameLinkKind j) ∉ edgeDimerHsites p.side F base (n - 1))
    (hend : ∀ j : FrameLinkIndex p,
      frameEndH p.side (frameLinkParameter j) (frameLinkKind j) ∉ edgeDimerHsites p.side F base (n - 1))
    (hcap : ∀ b : Bool,
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).owner ∉
        edgeDimerHsites p.side F base (n - 1))
    (i : Fin (capWord (dimerChain n)).length) (t : Fin p.frameWord.length) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      F base n hn reverse hroom C D hC hD).pos i ≠ (frameFold p).pos t := by
  let f := cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
    F base n hn reverse hroom C D hC hD
  have hcaps (b : Bool) : f.pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).seed :=
    transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
      (cappedEdgeDimerFold (by have h := p.side_ge; omega : 1 ≤ p.side)
        F base (n - 1) reverse (by omega) C D hC hD)
      (fun x => x ≠ (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).seed)
      (fun r => cappedEdgeDimerFold_ne_cap_of_owner_not_mem
        (by have h := p.side_ge; omega : 1 ≤ p.side) F base (n - 1)
        reverse (by omega) C D hC hD _ (hcap b) r) i
  exact frameTrack_property_of_capped_sites (frameFold p) (frameCoreFold p)
    (frameFirstColumn p).seed (frameLastColumn p).seed (frameFold_sites p)
    (fun x => f.pos i ≠ x) (hcaps true)
    (cappedInterval_ne_frameCoreFold_of_exclusions p F base n hn reverse hroom C D hC hD hH hstart hend i)
    (hcaps false) t

theorem cappedInnerTrack_ne_frameFold (p : ConstructionParameters) (base n : ℕ) (hn : 0 < n)
    (hlo : 2 ≤ base) (hhi : base + 2 * n + 1 ≤ 2 * p.side - 2) (reverse : Bool)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side trackEdgeFrame (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (dimerHIndex base reverse (n - 1) 1))
    (i : Fin (capWord (dimerChain n)).length) (t : Fin p.frameWord.length) :
    (cappedIntervalDimerFold (m := p.side) (by have h := p.side_ge; omega)
      trackEdgeFrame base n hn reverse (by omega) C D hC hD).pos i ≠ (frameFold p).pos t :=
  cappedInterval_ne_frameFold_of_exclusions p trackEdgeFrame base n hn reverse (by omega) C D hC hD
    (innerTrack_frameHRun_pos_not_mem p base (n - 1) hlo (by omega))
    (fun j => innerTrack_frameStart_not_mem (by have h := p.side_ge; omega : 3 ≤ p.side)
      base (n - 1) hlo (by omega) (frameLinkParameter j) (frameLinkKind j)
      (frameLinkParameter_ge p j) (frameLinkParameter_room p j))
    (fun j => innerTrack_frameEnd_not_mem (by have h := p.side_ge; omega : 3 ≤ p.side)
      base (n - 1) hlo (by omega) (frameLinkParameter j) (frameLinkKind j)
      (frameLinkParameter_ge p j) (frameLinkParameter_room p j))
    (innerTrack_frameEndpoint_owner_not_mem p base (n - 1) hlo (by omega)) i t

theorem itemTrackBase_inner_margin (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hload : before + s ≤ p.capacity) :
    2 ≤ itemTrackBase p k before ∧
      itemTrackBase p k before + 2 * p.itemDimers s + 1 ≤ 2 * p.side - 2 := by
  have hend := itemTrackBase_end_le p k before s hload
  have hmono := p.separatorIndex_mono (show k + 1 ≤ p.bins by omega)
  have hright := p.rightFiller_ge
  have hside : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
  constructor
  · dsimp [itemTrackBase]
    omega
  · omega

theorem canonicalItemPiece_ne_frameFold (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) (t : Fin p.frameWord.length) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ≠ (frameFold p).pos t := by
  have hmargin := itemTrackBase_inner_margin p k before s hk hload
  exact cappedInnerTrack_ne_frameFold p (itemTrackBase p k before) (p.itemDimers s)
    (by have h := p.itemDimers_ge s hs; omega) hmargin.1 hmargin.2 false
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by
      rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
      exact itemLastColumn_owner p k before s hk hs hload) i t

theorem canonicalItemPiece_frameWordPiece_disjoint (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    WordsDisjoint (canonicalItemPiece p k before s hk hs hload) (frameWordPiece p) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalItemPiece_ne_frameFold p k before s hk hs hload)

end ProteinFolding.Tetrahedral.NearField


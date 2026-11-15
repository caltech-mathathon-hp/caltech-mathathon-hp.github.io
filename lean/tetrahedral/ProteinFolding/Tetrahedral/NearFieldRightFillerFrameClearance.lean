import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import ProteinFolding.Tetrahedral.NearFieldRightFillerFrameOwners
import ProteinFolding.Tetrahedral.NearFieldFrameTrackSeparation

/-! The complete AB right filler avoids the complete actual frame. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

private theorem trackA_owner {m : ℕ} (hm : 1 ≤ m) (a : ℕ) (ha : a < m) :
    (trackAColumn hm a ha).owner = octEdgeZigzag m trackEdgeFrame (2 * a) := rfl

private theorem rightFirstColumn_dimer_owner (p : ConstructionParameters) :
    (rightFirstColumn p).owner = octEdgeZigzag p.side trackEdgeFrame
      (dimerHIndex (rightFillerTrackBase p) false 0 0) := by
  have hi : 2 * (p.separatorIndex p.bins + 2) =
      dimerHIndex (rightFillerTrackBase p) false 0 0 := by
    dsimp [dimerHIndex, dimerFlip, rightFillerTrackBase]
  dsimp only [rightFirstColumn]
  rw [trackA_owner]
  exact congrArg (octEdgeZigzag p.side trackEdgeFrame) hi

private theorem rightFinalColumn_dimer_owner (p : ConstructionParameters) :
    (rightFinalColumn p).owner = octEdgeZigzag p.side trackEdgeFrame
      (dimerHIndex (rightFillerTrackBase p) false (p.rightFiller - 1) 1) := by
  rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
  have he := rightFillerTrackBase_end p
  have hi : rightFillerTrackBase p + 2 * p.rightFiller - 1 = 2 * p.side - 3 := by omega
  rw [hi]
  exact rightFinalColumn_track_owner p

theorem canonicalRightPiece_ne_frameFold (p : ConstructionParameters)
    (i : Fin (canonicalRightPiece p).word.length) (t : Fin p.frameWord.length) :
    (canonicalRightPiece p).fold.pos i ≠ (frameFold p).pos t := by
  exact cappedInterval_ne_frameFold_of_exclusions p trackEdgeFrame
    (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega) false
    (rightFillerTrackBase_room p) (rightFirstColumn p) (rightFinalColumn p)
    (rightFirstColumn_dimer_owner p) (rightFinalColumn_dimer_owner p)
    (frameHRunFold_not_rightFillerHsites p)
    (fun j => by
      simpa only [Bool.false_eq_true, if_false] using rightFiller_excludes_frameH p
        (frameLinkParameter j) (frameLinkKind j) (frameLinkParameter_ge p j) (frameLinkParameter_room p j) false)
    (fun j => by
      simpa only [ite_true] using rightFiller_excludes_frameH p
        (frameLinkParameter j) (frameLinkKind j) (frameLinkParameter_ge p j) (frameLinkParameter_room p j) true)
    (frameEndpointColumn_not_rightFillerHsites p) i t

theorem canonicalRightPiece_frameWordPiece_disjoint (p : ConstructionParameters) :
    WordsDisjoint (canonicalRightPiece p) (frameWordPiece p) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalRightPiece_ne_frameFold p)

end ProteinFolding.Tetrahedral.NearField

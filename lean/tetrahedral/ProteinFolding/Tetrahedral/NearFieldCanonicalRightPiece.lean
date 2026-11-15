import ProteinFolding.Tetrahedral.NearFieldCanonicalTrackPieces
import ProteinFolding.Tetrahedral.NearFieldRightFinalColumn

/-! The actual AB right filler with both physical endpoint columns. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096

def rightFirstColumn (p : ConstructionParameters) : DanglingColumn p.side :=
  trackAColumn (m := p.side) (by have h := p.side_ge; omega) (p.separatorIndex p.bins + 2) (by
    have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
    omega)

private theorem rightFillerWordPiece_first_seed (p : ConstructionParameters)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side trackEdgeFrame (rightFillerTrackBase p))
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.side - 3)) :
    (rightFillerWordPiece p C D hC hD).first = C.seed := rfl

private theorem rightFillerWordPiece_last_seed (p : ConstructionParameters)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side trackEdgeFrame (rightFillerTrackBase p))
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.side - 3)) :
    (rightFillerWordPiece p C D hC hD).last = D.seed := rfl

def canonicalRightPiece (p : ConstructionParameters) : PositionedWord :=
  rightFillerWordPiece p (rightFirstColumn p) (rightFinalColumn p) rfl (rightFinalColumn_track_owner p)

theorem canonicalRightPiece_word (p : ConstructionParameters) :
    (canonicalRightPiece p).word = capWord (dimerChain p.rightFiller) := rfl

theorem canonicalRightPiece_first (p : ConstructionParameters) :
    (canonicalRightPiece p).first = (rightFirstColumn p).seed :=
  rightFillerWordPiece_first_seed p (rightFirstColumn p) (rightFinalColumn p) rfl
    (rightFinalColumn_track_owner p)

theorem canonicalRightPiece_last (p : ConstructionParameters) :
    (canonicalRightPiece p).last = (rightFinalColumn p).seed :=
  rightFillerWordPiece_last_seed p (rightFirstColumn p) (rightFinalColumn p) rfl
    (rightFinalColumn_track_owner p)

theorem canonicalRightPiece_hSupport (p : ConstructionParameters) :
    hSupport (canonicalRightPiece p).word (canonicalRightPiece p).fold ⊆ octahedron p.side :=
  cappedIntervalDimerPiece_hSupport_subset_oct (m := p.side) (by have h := p.side_ge; omega)
    trackEdgeFrame (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega)
    false (rightFillerTrackBase_room p) (rightFirstColumn p) (rightFinalColumn p)
    (by simpa only [dimerHIndex, dimerFlip] using
      (show (rightFirstColumn p).owner = octEdgeZigzag p.side trackEdgeFrame (rightFillerTrackBase p) from rfl))
    (by
      rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
      have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
      have hi : rightFillerTrackBase p + 2 * p.rightFiller - 1 = 2 * p.side - 3 := by
        dsimp [rightFillerTrackBase]
        omega
      rw [hi]
      exact rightFinalColumn_track_owner p)

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.NearFieldCanonicalSeparatorPieces
import ProteinFolding.Tetrahedral.NearFieldPackedItemFamily
import ProteinFolding.Tetrahedral.NearFieldCanonicalRightPiece
import ProteinFolding.Tetrahedral.NearFieldExitCapFamily
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletons
import ProteinFolding.Tetrahedral.NearFieldCanonicalRings
import ProteinFolding.Tetrahedral.NearFieldActualFrameFold
import ProteinFolding.Tetrahedral.ReductionTM2BulkCappedFamily

/-! Actual local folds in precisely the source machine's unit order.
Only a packing witness and the proved bulk acyclicity are inputs. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 500000
set_option maxRecDepth 4096

def canonicalSingletonPieces (p : ConstructionParameters) : List PositionedWord :=
  [canonicalSingletonPiece p.side (by have h := p.side_ge; omega) 0,
    canonicalSingletonPiece p.side (by have h := p.side_ge; omega) 1,
    canonicalSingletonPiece p.side (by have h := p.side_ge; omega) 2]

theorem canonicalSingletonPieces_words (p : ConstructionParameters) :
    (canonicalSingletonPieces p).map PositionedWord.word =
      [capWord [Residue.H], capWord [Residue.H], capWord [Residue.H]] := rfl

theorem frameWordPiece_word (p : ConstructionParameters) :
    (frameWordPiece p).word = capWord (p.framePart1 ++ p.framePart2) :=
  (frame_capWord_eq p).symm

theorem terminalWordPiece_word (p : ConstructionParameters) :
    (terminalWordPiece p).word = [Residue.H, Residue.P] := rfl

end ProteinFolding.Tetrahedral.NearField

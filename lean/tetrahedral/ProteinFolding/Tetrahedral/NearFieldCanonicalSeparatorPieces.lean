import ProteinFolding.Tetrahedral.NearFieldCanonicalTrackPieces
import ProteinFolding.Tetrahedral.NearFieldExitCapFamily
import Mathlib.Data.List.FinRange

/-! The actual capped separator list without ring or bulk dependencies. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096

def canonicalSeparatorPiece (p : ConstructionParameters) (k : Fin (p.bins + 1)) : PositionedWord :=
  separatorWordPiece p k.val (by have h := k.isLt; omega)
    (entryLocalColumn p (some k)) (exitCapColumn p k.val (by have h := k.isLt; omega)) rfl
    (exitCapColumn_owner p k.val (by have h := k.isLt; omega))

def canonicalSeparatorPieces (p : ConstructionParameters) : List PositionedWord :=
  List.ofFn (canonicalSeparatorPiece p)

theorem canonicalSeparatorPieces_words (p : ConstructionParameters) :
    (canonicalSeparatorPieces p).map PositionedWord.word =
      (List.range (p.bins + 1)).map (fun k => capWord (p.separatorWord k)) := by
  rw [canonicalSeparatorPieces, List.map_ofFn, List.ofFn_eq_map]
  have he := congrArg (List.map (fun k => capWord (p.separatorWord k)))
    (List.map_coe_finRange (p.bins + 1))
  simpa only [List.map_map, Function.comp_def] using he

end ProteinFolding.Tetrahedral.NearField

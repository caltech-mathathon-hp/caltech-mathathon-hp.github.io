import ProteinFolding.Tetrahedral.NearFieldFramePieceOrder

/-! The geometric frame pieces concatenate to the literal builder word. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096

theorem pieceWords_append (ps qs : List PositionedWord) :
    pieceWords (ps ++ qs) = pieceWords ps ++ pieceWords qs := by
  simp only [pieceWords, List.flatMap_append]

theorem flatMap_constant_word {α : Type*} (xs : List α) (w : Sequence) :
    xs.flatMap (fun _ => w) = repeatWord w xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.length_cons, repeatWord, ih]

theorem frameEntryPairs_words (p : ConstructionParameters) :
    pieceWords ((frameEntryPairs p).map (frameCorePiece p)) =
      repeatWord (List.replicate 6 .P ++ List.replicate 4 .H) p.bins := by
  simp only [pieceWords, List.flatMap_map, frameEntryPairs]
  rw [List.flatMap_assoc]
  have hw (t : Fin p.bins) :
      (frameSlotPair p false t.castSucc).flatMap (fun i => (frameCorePiece p i).word) =
        List.replicate 6 .P ++ List.replicate 4 .H := by
    have ht : t.val ≠ p.bins := by have h := t.isLt; omega
    change (List.replicate (nearFrameLength (1 : Fin 6) - 2) Residue.P ++
      List.replicate (if t.val = p.bins then p.frameTail1 else 4) Residue.H) ++ [] = _
    rw [show nearFrameLength (1 : Fin 6) = 8 by decide, if_neg ht, List.append_nil]
  simp_rw [hw]
  rw [flatMap_constant_word, List.length_finRange]

theorem frameExitPairs_words (p : ConstructionParameters) :
    pieceWords ((frameExitPairs p).map (frameCorePiece p)) =
      repeatWord (List.replicate 10 .P ++ List.replicate 4 .H) (p.bins + 1) := by
  simp only [pieceWords, List.flatMap_map, frameExitPairs]
  rw [List.flatMap_assoc]
  have hw (t : Fin (p.bins + 1)) :
      (frameSlotPair p true t).flatMap (fun i => (frameCorePiece p i).word) =
        List.replicate 10 .P ++ List.replicate 4 .H := by
    change (List.replicate (nearFrameLength (4 : Fin 6) - 2) Residue.P ++ List.replicate 4 Residue.H) ++ [] = _
    rw [show nearFrameLength (4 : Fin 6) = 12 by decide, List.append_nil]
  simp_rw [hw]
  rw [flatMap_constant_word, List.length_reverse, List.length_finRange]

theorem frameCorePieces_words (p : ConstructionParameters) :
    pieceWords (frameCorePieces p) = p.framePart1 ++ p.framePart2 := by
  change pieceWords ((frameCoreOrder p).map (frameCorePiece p)) = _
  simp only [frameCoreOrder, List.map_append, pieceWords_append,
    frameEntryPairs_words, frameExitPairs_words]
  simp [pieceWords, frameSlotPair, frameCorePiece, frameLinkPiece, frameLinkWord, frameLinkKind,
    frameHRunPiece, frameHRunWord, frameHRunData, nearFrameLength,
    ConstructionParameters.framePart1, ConstructionParameters.framePart2, List.append_assoc]

end ProteinFolding.Tetrahedral.NearField

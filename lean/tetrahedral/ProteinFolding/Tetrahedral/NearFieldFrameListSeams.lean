import ProteinFolding.Tetrahedral.NearFieldFramePieceOrder
import ProteinFolding.Tetrahedral.NearFieldFrameSlotSeams

/-! The complete ordered slot blocks, including the two long tail runs. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 150000
set_option maxRecDepth 4096

def frameEntryAllPieces (p : ConstructionParameters) : List PositionedWord :=
  (List.finRange (p.bins + 1)).flatMap (fun t =>
    [frameLinkPiece p (.inr (false, t)), frameHRunPiece p (.inr (false, t))])

def frameExitAllPieces (p : ConstructionParameters) : List PositionedWord :=
  (List.finRange (p.bins + 1)).reverse.flatMap (fun t =>
    [frameLinkPiece p (.inr (true, t)), frameHRunPiece p (.inr (true, t))])

theorem frameEntryAllPieces_seams (p : ConstructionParameters) : piecesSeams (frameEntryAllPieces p) := by
  apply pairedPieces_seams _ _ _ (frameSlot_internal_seam p false)
  apply List.isChain_iff_get.mpr
  intro i hi
  apply frameEntrySlots_seam
  simp only [List.get_eq_getElem, List.getElem_finRange, Fin.coe_cast]

theorem frameExitAllPieces_seams (p : ConstructionParameters) : piecesSeams (frameExitAllPieces p) := by
  apply pairedPieces_seams _ _ _ (frameSlot_internal_seam p true)
  apply List.isChain_reverse.mpr
  apply List.isChain_iff_get.mpr
  intro i hi
  apply frameExitSlots_seam
  simp only [List.get_eq_getElem, List.getElem_finRange, Fin.coe_cast]

theorem pairedList_head {α : Type*} (xs : List α) (a b : α → PositionedWord) :
    (xs.flatMap (fun x => [a x, b x])).head? = xs.head?.map a := by
  cases xs <;> rfl

theorem pairedList_last {α : Type*} (xs : List α) (a b : α → PositionedWord) :
    (xs.flatMap (fun x => [a x, b x])).getLast? = xs.getLast?.map b := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y xs =>
      change ([a x, b x] ++ (y :: xs).flatMap (fun z => [a z, b z])).getLast? = _
      rw [List.getLast?_append_of_ne_nil _ (by simp)]
      simpa only [List.getLast?_cons_cons] using ih

theorem finRange_succ_head (n : ℕ) : (List.finRange (n + 1)).head? = some 0 := by
  rw [List.finRange_succ]
  rfl

theorem finRange_succ_last (n : ℕ) : (List.finRange (n + 1)).getLast? = some (Fin.last n) := by
  rw [List.finRange_succ_last]
  simp

theorem frameEntryAllPieces_head (p : ConstructionParameters) :
    (frameEntryAllPieces p).head? = some (frameLinkPiece p (.inr (false, 0))) := by
  rw [frameEntryAllPieces, pairedList_head, finRange_succ_head]
  rfl

theorem frameEntryAllPieces_last (p : ConstructionParameters) :
    (frameEntryAllPieces p).getLast? = some (frameHRunPiece p (.inr (false, Fin.last p.bins))) := by
  rw [frameEntryAllPieces, pairedList_last, finRange_succ_last]
  rfl

theorem frameExitAllPieces_head (p : ConstructionParameters) :
    (frameExitAllPieces p).head? = some (frameLinkPiece p (.inr (true, Fin.last p.bins))) := by
  rw [frameExitAllPieces, pairedList_head, List.head?_reverse, finRange_succ_last]
  rfl

theorem frameExitAllPieces_last (p : ConstructionParameters) :
    (frameExitAllPieces p).getLast? = some (frameHRunPiece p (.inr (true, 0))) := by
  rw [frameExitAllPieces, pairedList_last, List.getLast?_reverse, finRange_succ_head]
  rfl

theorem frameCorePieces_slot_blocks (p : ConstructionParameters) :
    frameCorePieces p =
      [frameHRunPiece p (.inl 0), frameLinkPiece p (.inl 0), frameHRunPiece p (.inl 1)] ++
      frameEntryAllPieces p ++
      [frameLinkPiece p (.inl 1), frameHRunPiece p (.inl 2), frameLinkPiece p (.inl 2), frameHRunPiece p (.inl 3)] ++
      frameExitAllPieces p ++ [frameLinkPiece p (.inl 3), frameHRunPiece p (.inl 4)] := by
  simp only [frameCorePieces, frameCoreOrder, List.map_append, List.map_cons, List.map_nil,
    frameCorePiece, frameEntryAllPieces, frameExitAllPieces, frameEntryPairs, frameExitPairs,
    List.finRange_succ_last, List.flatMap_append, List.flatMap_map, List.map_flatMap,
    List.flatMap_cons, List.flatMap_nil, frameSlotPair, List.map_cons, List.map_nil,
    List.append_nil, List.append_assoc, Function.comp_def]

end ProteinFolding.Tetrahedral.NearField

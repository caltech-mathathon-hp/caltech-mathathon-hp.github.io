import ProteinFolding.Tetrahedral.NearFieldFrameListSeams
import ProteinFolding.Tetrahedral.NearFieldFrameFixedSeams
import ProteinFolding.Tetrahedral.NearFieldFramePieceWords
import ProteinFolding.Tetrahedral.NearFieldWordTransport
import ProteinFolding.Tetrahedral.NearFieldAssemblySupport
import ProteinFolding.Tetrahedral.NearFieldPositionedProperties

/-! One actual self-avoiding fold of both literal frame parts. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

theorem frameCorePieces_seams (p : ConstructionParameters) : piecesSeams (frameCorePieces p) := by
  rw [frameCorePieces_slot_blocks, piecesSeams_iff_isChain]
  have he := (piecesSeams_iff_isChain _).mp (frameEntryAllPieces_seams p)
  have hx := (piecesSeams_iff_isChain _).mp (frameExitAllPieces_seams p)
  obtain ⟨h01, h12, h23⟩ := frame_initial_seams p
  obtain ⟨h34, h45, h56, h67, h78⟩ := frame_middle_seams p
  obtain ⟨h89, h9a⟩ := frame_final_seams p
  have hea := he.append (List.IsChain.singleton (frameLinkPiece p (.inl 1)))
    (by simpa [frameEntryAllPieces_last] using h34)
  have hxa := hx.append (List.IsChain.singleton (frameLinkPiece p (.inl 3)))
    (by simpa [frameExitAllPieces_last] using h89)
  have heb := hea.cons' (x := frameHRunPiece p (.inl 1)) (by
    simpa [List.head?_append, frameEntryAllPieces_head] using h23)
  have hxb := hxa.cons' (x := frameHRunPiece p (.inl 3)) (by
    simpa [List.head?_append, frameExitAllPieces_head] using h78)
  simpa [List.isChain_append, List.isChain_cons_cons, frameEntryAllPieces_head,
    frameEntryAllPieces_last, frameExitAllPieces_head, frameExitAllPieces_last,
    h01, h12, h23, h34, h45, h56, h67, h78, h89, h9a] using And.intro heb hxb

noncomputable def frameCoreAssembly (p : ConstructionParameters) : PieceAssembly (frameCorePieces p) :=
  assemblePieces (frameCorePieces p)
    (by simp [frameCorePieces, frameCoreOrder])
    (frameCorePieces_pairwise p) (frameCorePieces_seams p)

noncomputable def frameCoreFold (p : ConstructionParameters) :
    Fold tetrahedralLattice (p.framePart1 ++ p.framePart2).length :=
  transportWordFold ((frameCoreAssembly p).word_eq.trans (frameCorePieces_words p))
    (frameCoreAssembly p).piece.fold

end ProteinFolding.Tetrahedral.NearField

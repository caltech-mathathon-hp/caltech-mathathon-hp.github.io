import ProteinFolding.Tetrahedral.NearFieldFrameSlotSeams

/-! The fixed initial links and all three corners of the literal frame. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

theorem frameHRun_to_link_seam (p : ConstructionParameters) (i : FrameHRunIndex p) (j : FrameLinkIndex p)
    (h : (frameHRunPiece p i).last =
      octEdgeZigzag p.side (nearFrameRouteFrame (frameLinkKind j))
        (nearFrameStartIndex p.side (frameLinkParameter j) (frameLinkKind j))) :
    tetrahedralLattice.Adj (frameHRunPiece p i).last (frameLinkPiece p j).first := by
  rw [h]
  exact frameLinkPiece_first_seam p j

theorem frameLink_to_HRun_seam (p : ConstructionParameters) (i : FrameLinkIndex p) (j : FrameHRunIndex p)
    (h : octEdgeZigzag p.side (nearFrameRouteFrame (frameLinkKind i))
        (nearFrameEndIndex p.side (frameLinkParameter i) (frameLinkKind i)) = (frameHRunPiece p j).first) :
    tetrahedralLattice.Adj (frameLinkPiece p i).last (frameHRunPiece p j).first := by
  have hs := frameLinkPiece_last_seam p i
  rwa [h] at hs

theorem entryEdgeEnd_eq_exitEdgeEnd (p : ConstructionParameters) :
    octEdgeZigzag p.side entryEdgeFrame (2 * p.side - 2) =
      octEdgeZigzag p.side exitEdgeFrame (2 * p.side - 2) := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply Subtype.ext
  rw [entryEdgeZigzag_coordinates hm, exitEdgeZigzag_coordinates hm]
  funext c
  fin_cases c <;> dsimp [entryEdgeCoordinates, exitEdgeCoordinates, octRadius] <;> omega

theorem frame_initial_seams (p : ConstructionParameters) :
    tetrahedralLattice.Adj (frameHRunPiece p (.inl 0)).last (frameLinkPiece p (.inl 0)).first ∧
    tetrahedralLattice.Adj (frameLinkPiece p (.inl 0)).last (frameHRunPiece p (.inl 1)).first ∧
    tetrahedralLattice.Adj (frameHRunPiece p (.inl 1)).last (frameLinkPiece p (.inr (false, 0))).first := by
  refine ⟨frameHRun_to_link_seam p _ _ ?_, frameLink_to_HRun_seam p _ _ ?_, frameHRun_to_link_seam p _ _ ?_⟩
  all_goals norm_num [frameHRunPiece, frameHRunFirst, frameHRunLast, frameHRunData,
    frameLinkKind, frameLinkParameter, nearFrameRouteFrame, nearFrameStartIndex, nearFrameEndIndex, Fin.ext_iff]

theorem frame_middle_seams (p : ConstructionParameters) :
    tetrahedralLattice.Adj (frameHRunPiece p (.inr (false, Fin.last p.bins))).last (frameLinkPiece p (.inl 1)).first ∧
    tetrahedralLattice.Adj (frameLinkPiece p (.inl 1)).last (frameHRunPiece p (.inl 2)).first ∧
    tetrahedralLattice.Adj (frameHRunPiece p (.inl 2)).last (frameLinkPiece p (.inl 2)).first ∧
    tetrahedralLattice.Adj (frameLinkPiece p (.inl 2)).last (frameHRunPiece p (.inl 3)).first ∧
    tetrahedralLattice.Adj (frameHRunPiece p (.inl 3)).last
      (frameLinkPiece p (.inr (true, Fin.last p.bins))).first := by
  have h1 := p.frameTail1_add
  have h2 := p.frameTail2_add
  have h1p := p.frameTail1_ge_three
  have h2p := p.frameTail2_ge_three
  have hm := p.side_ge
  refine ⟨frameHRun_to_link_seam p _ _ ?_, frameLink_to_HRun_seam p _ _ ?_,
    frameHRun_to_link_seam p _ _ ?_, frameLink_to_HRun_seam p _ _ ?_, frameHRun_to_link_seam p _ _ ?_⟩
  · norm_num [frameHRunPiece, frameHRunLast, frameHRunData, frameLinkKind, frameLinkParameter,
      nearFrameRouteFrame, nearFrameStartIndex, Fin.ext_iff]
    congr 1
    omega
  · norm_num [frameHRunPiece, frameHRunFirst, frameHRunData, frameLinkKind, frameLinkParameter,
      nearFrameRouteFrame, nearFrameEndIndex, Fin.ext_iff]
  · simpa [frameHRunPiece, frameHRunLast, frameHRunData, frameLinkKind, frameLinkParameter,
      nearFrameRouteFrame, nearFrameStartIndex, Fin.ext_iff] using entryEdgeEnd_eq_exitEdgeEnd p
  · norm_num [frameHRunPiece, frameHRunFirst, frameHRunData, frameLinkKind, frameLinkParameter,
      nearFrameRouteFrame, nearFrameEndIndex, Fin.ext_iff]
    congr 1
    omega
  · norm_num [frameHRunPiece, frameHRunLast, frameHRunData, frameLinkKind, frameLinkParameter,
      nearFrameRouteFrame, nearFrameStartIndex, Fin.ext_iff]


theorem frame_final_seams (p : ConstructionParameters) :
    tetrahedralLattice.Adj (frameHRunPiece p (.inr (true, 0))).last (frameLinkPiece p (.inl 3)).first ∧
    tetrahedralLattice.Adj (frameLinkPiece p (.inl 3)).last (frameHRunPiece p (.inl 4)).first := by
  refine ⟨frameHRun_to_link_seam p _ _ ?_, frameLink_to_HRun_seam p _ _ ?_⟩
  all_goals norm_num [frameHRunPiece, frameHRunFirst, frameHRunLast, frameHRunData,
    frameLinkKind, frameLinkParameter, nearFrameRouteFrame, nearFrameStartIndex, nearFrameEndIndex, Fin.ext_iff]

end ProteinFolding.Tetrahedral.NearField


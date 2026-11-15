import ProteinFolding.Tetrahedral.FrameForcingMiddleCorner
import ProteinFolding.Tetrahedral.FrameForcingConfiguration

/-! The middle small-face corner is omitted by the actual frame; all of
its octahedral neighbours occur strictly inside that frame factor. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

theorem shared_corner_not_frame (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord)
    (F : ActualFrameConfiguration p.side (hSupport p.frameWord P.toFold)
      p.frameGaps1 p.frameGaps2 P.site p.framePart1.length)
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b) :
    octEdgeZigzag p.side F.first (2 * p.side - 3) ∉ hSupport p.frameWord P.toFold := by
  have hm := p.side_ge
  have hcorner := shared_middle_corner_eq p.side (by omega) F.first F.second F.next_big hsmall ha F.next_end_face
  have hlen := p.frameGaps1_length_pos
  have hlast := p.frame_last_run_offset.2
  change frameAdvanceAt p.frameGaps1 (p.frameGaps1.length - 1) = 2 * p.side - 4 at hlast
  have hlastNext : frameAdvanceAt p.frameGaps1 (p.frameGaps1.length - 1 + 1) = 2 * p.side - 2 := by
    rw [show p.frameGaps1.length - 1 + 1 = p.frameGaps1.length by omega]
    simpa only [frameAdvanceAt, List.take_length] using p.frameGaps1_budget
  intro hmem
  rcases F.support_cases _ hmem with ⟨j, hj, heq⟩ | ⟨j, hj, heq⟩
  · have hindex := octEdgeZigzag_injective (by omega : 1 ≤ p.side) F.first heq
    exact frameAdvanceAt_avoids_gap p.frameGaps1 F.allowed₁ (p.frameGaps1.length - 1) (by omega)
      (2 * p.side - 3) (by omega) (by omega) j hj hindex.symm
  · rw [hcorner] at heq
    have hindex := octEdgeZigzag_injective (by omega : 1 ≤ p.side) F.second heq
    have hfirst : frameAdvanceAt p.frameGaps2 0 = 0 := rfl
    have hnext : frameAdvanceAt p.frameGaps2 (0 + 1) = 2 := rfl
    exact frameAdvanceAt_avoids_gap p.frameGaps2 F.allowed₂ 0 p.frameGaps2_length_pos
      1 (by omega) (by omega) j hj hindex.symm

theorem shared_corner_not_vertex (p : ConstructionParameters) (F : OctEdgeFrame) :
    octEdgeZigzag p.side F (2 * p.side - 3) ∉ octVertices p.side := by
  have hm := p.side_ge
  intro hmem
  exact sublattices_disjoint _ (octVertices_inA hmem) (end_corner_faces p.side (by omega) F).1

theorem frame_middle_span_strict (p : ConstructionParameters) :
    p.framePart1.length + 6 < p.frameWord.length := by
  have htail := p.frameTail2_ge_three
  simp only [frameWord, framePart2, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

theorem shared_corner_neighbours_in_frame (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord)
    (F : ActualFrameConfiguration p.side (hSupport p.frameWord P.toFold)
      p.frameGaps1 p.frameGaps2 P.site p.framePart1.length)
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b)
    (q : Site) (hlower : -octRadius p.side - 1 ≤ tetraCoordinate p.side q.val F.first.j)
    (hadj : tetrahedralLattice.Adj (octEdgeZigzag p.side F.first (2 * p.side - 3)) q) :
    ∃ r, 1 ≤ r ∧ r + 1 < p.frameWord.length ∧ q = P.site r := by
  have hm := p.side_ge
  have hmid := p.framePart1_length_ge_five
  have hspan := p.frame_middle_span_strict
  have hmiddleBounds : 1 ≤ p.framePart1.length ∧ p.framePart1.length + 1 < p.frameWord.length := by omega
  have hInBounds : 1 ≤ p.framePart1.length - 4 ∧ p.framePart1.length - 4 + 1 < p.frameWord.length := by omega
  have hOutBounds : 1 ≤ p.framePart1.length + 4 ∧ p.framePart1.length + 4 + 1 < p.frameWord.length := by omega
  have hpos₁ := p.frameGaps1_length_pos
  have hIn := F.indices_first (p.frameGaps1.length - 1) (by omega)
  change P.site (1 + frameHOffset p.frameGaps1 (p.frameGaps1.length - 1)) =
    octEdgeZigzag p.side F.first (((p.frameGaps1.take (p.frameGaps1.length - 1)).map frameGapAdvance).sum) at hIn
  rw [p.frame_last_run_offset.1, p.frame_last_run_offset.2] at hIn
  have hpos₂ := p.frameGaps2_length_pos
  have hOut := F.indices_second 1 (by omega)
  change P.site (p.framePart1.length + 4) = octEdgeZigzag p.side F.second 2 at hOut
  rcases shared_middle_corner_neighbours_of_bound p.side (by omega) F.first F.second
    F.next_big hsmall ha F.next_end_face q hlower hadj with h | h | h
  · exact ⟨p.framePart1.length, hmiddleBounds.1, hmiddleBounds.2, h.trans F.end_first.symm⟩
  · exact ⟨p.framePart1.length - 4, hInBounds.1, hInBounds.2, h.trans hIn.symm⟩
  · exact ⟨p.framePart1.length + 4, hOutBounds.1, hOutBounds.2, h.trans hOut.symm⟩

end ProteinFolding.Tetrahedral.ConstructionParameters

import ProteinFolding.Tetrahedral.FrameForcingTrackSupport
import ProteinFolding.Tetrahedral.FrameForcingCornerSupport

/-! No track site is occupied by the literal forced frame. The two start
sites and the last corner are exactly skipped frame indices. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem frameGaps2_last_eq (p : ConstructionParameters) :
    p.frameGaps2[p.frameGaps2.length - 1]'(by have h := p.frameGaps2_length_pos; omega) = 3 := by
  unfold frameGaps2
  exact getElem_append_last_singleton _ 3

theorem frameGaps2_last_advance (p : ConstructionParameters) :
    frameAdvanceAt p.frameGaps2 (p.frameGaps2.length - 1) = 2 * p.side - 4 ∧
      frameAdvanceAt p.frameGaps2 p.frameGaps2.length = 2 * p.side - 2 := by
  have hp := p.frameGaps2_length_pos
  have hnext := frameAdvanceAt_next p.frameGaps2 (p.frameGaps2.length - 1) (by omega)
  have hi : p.frameGaps2.length - 1 + 1 = p.frameGaps2.length := by omega
  rw [hi, p.frameGaps2_last_eq] at hnext
  have hbudget : frameAdvanceAt p.frameGaps2 p.frameGaps2.length = 2 * p.side - 2 := by
    simpa only [frameAdvanceAt, List.take_length] using p.frameGaps2_budget
  change frameAdvanceAt p.frameGaps2 p.frameGaps2.length =
    frameAdvanceAt p.frameGaps2 (p.frameGaps2.length - 1) + 2 at hnext
  have hm := p.side_ge
  exact ⟨by omega, hbudget⟩

theorem frameTrackPoint_not_frame (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord)
    (F : ActualFrameConfiguration p.side (hSupport p.frameWord P.toFold)
      p.frameGaps1 p.frameGaps2 P.site p.framePart1.length)
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b)
    (r : ℕ) (hr : r < 2 * p.side - 2) :
    frameTrackPoint p.side F.first r ∉ hSupport p.frameWord P.toFold := by
  have hm := p.side_ge
  have hm1 : 1 ≤ p.side := by omega
  intro hmem
  rcases F.support_cases _ hmem with ⟨j, hj, heq⟩ | ⟨j, hj, heq⟩
  · have hh : frameH2 p.side F.first (frameTrackPoint p.side F.first r) ≤ 2 := by
      rw [heq]
      exact (entry_edge_height_data p.side hm1 F.first _).2.1
    rw [frameTrackPoint_H2 p.side hm1 F.first r] at hh
    have hrsmall : r = 0 ∨ r = 1 := by clear * - hh; omega
    have hpos := p.frameGaps1_length_pos
    rcases hrsmall with rfl | rfl
    · change octEdgeZigzag p.side F.first 2 = _ at heq
      have hi := octEdgeZigzag_injective hm1 F.first heq
      exact frameAdvanceAt_avoids_gap p.frameGaps1 F.allowed₁ 0 hpos 2
        (by change 0 < 2; decide) (by change 2 < 3; decide) j hj hi.symm
    · change octEdgeZigzag p.side F.first.smallOtherSide 1 = _ at heq
      rw [← start_corner_shared p.side hm1 F.first] at heq
      have hi := octEdgeZigzag_injective hm1 F.first heq
      exact frameAdvanceAt_avoids_gap p.frameGaps1 F.allowed₁ 0 hpos 1
        (by change 0 < 1; decide) (by change 1 < 3; decide) j hj hi.symm
  · have hh : -2 ≤ frameK2 p.side F.first (frameTrackPoint p.side F.first r) := by
      rw [heq]
      exact (intended_exit_height_data p.side hm1 F.first F.second F.next_big hsmall ha _).2.1
    by_cases hzero : r = 0
    · rw [hzero, frameTrackPoint, if_pos rfl, (entry_edge_height_data p.side hm1 F.first 2).2.2] at hh
      clear * - hh hm
      dsimp [octRadius] at hh
      omega
    · rw [frameTrackPoint, if_neg hzero, (track_edge_height_data p.side hm1 F.first r).2] at hh
      have hlast : r = 2 * p.side - 3 := by
        clear * - hh hr
        dsimp [octRadius] at hh
        omega
      rw [frameTrackPoint, if_neg hzero, hlast,
        track_end_corner_eq_exit_end_corner p.side (by omega) F.first F.second
          F.next_big hsmall ha F.next_end_face] at heq
      have hi := octEdgeZigzag_injective hm1 F.second heq
      have hpos := p.frameGaps2_length_pos
      have hlastAdv := p.frameGaps2_last_advance
      exact frameAdvanceAt_avoids_gap p.frameGaps2 F.allowed₂ (p.frameGaps2.length - 1) (by omega)
        (2 * p.side - 3) (by omega) (by simpa only [show p.frameGaps2.length - 1 + 1 = p.frameGaps2.length by omega] using (show 2 * p.side - 3 < frameAdvanceAt p.frameGaps2 p.frameGaps2.length by omega))
        j hj hi.symm

theorem frameTrackPoint_mem_remaining (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord)
    (F : ActualFrameConfiguration p.side (hSupport p.frameWord P.toFold)
      p.frameGaps1 p.frameGaps2 P.site p.framePart1.length)
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b)
    (r : ℕ) (hr : r < 2 * p.side - 2) :
    frameTrackPoint p.side F.first r ∈ p.frameRemainingEdges P := by
  have hm := p.side_ge
  apply Finset.mem_sdiff.mpr
  refine ⟨frameTrackPoint_mem_deleted p.side (by omega) F.first r hr, ?_⟩
  intro hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact p.frameTrackPoint_not_frame P F hsmall ha r hr h
  · exact frameTrackPoint_not_vertex p.side (by omega) F.first r hr h

end ProteinFolding.Tetrahedral.ConstructionParameters

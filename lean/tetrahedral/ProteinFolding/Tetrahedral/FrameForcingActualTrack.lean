import ProteinFolding.Tetrahedral.FrameForcingTrackIsolation
import ProteinFolding.Tetrahedral.FrameForcingTrackFrameSupport
import ProteinFolding.Tetrahedral.FrameForcingPerfectMatching
import ProteinFolding.Tetrahedral.FrameForcingTrackMatching

/-! The actual reduction's dimers fill the isolated complete track and
therefore occupy its unique even/odd physical pairs. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem frameTrackSites_isolated_remaining (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord)
    (F : ActualFrameConfiguration p.side (hSupport p.frameWord P.toFold)
      p.frameGaps1 p.frameGaps2 P.site p.framePart1.length)
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b) (terminal : Site) :
    ∀ x ∈ frameTrackSites p.side F.first, ∀ y ∈ (p.frameRemainingEdges P).erase terminal,
      tetrahedralLattice.Adj x y → y ∈ frameTrackSites p.side F.first := by
  have hm := p.side_ge
  have hsubset : (p.frameRemainingEdges P).erase terminal ⊆ bulkDeletedEdges p.side := by
    intro x hx
    exact (Finset.mem_sdiff.mp (Finset.mem_erase.mp hx).2).1
  have hguard (x : Site) (hx : x ∈ hSupport p.frameWord P.toFold) :
      x ∉ (p.frameRemainingEdges P).erase terminal := by
    intro h
    exact (Finset.mem_sdiff.mp (Finset.mem_erase.mp h).2).2 (Finset.mem_union_left _ hx)
  apply frameTrackSites_isolated p.side (by omega) F.first F.second F.next_big hsmall ha F.next_end_face
    _ hsubset
  · apply hguard
    exact F.nodes₁ 0 (Nat.zero_le _)
  · apply hguard
    have h := F.nodes₂ p.frameGaps2.length le_rfl
    rw [p.frameGaps2_last_advance.2] at h
    exact h
  · apply hguard
    have h := F.nodes₁ 1 (by have h := p.frameGaps1_length_pos; omega)
    change octEdgeZigzag p.side F.first 3 ∈ _ at h
    exact h
  · apply hguard
    have h := F.nodes₂ (p.frameGaps2.length - 1) (Nat.sub_le _ _)
    change octEdgeZigzag p.side F.second (frameAdvanceAt p.frameGaps2 (p.frameGaps2.length - 1)) ∈ _ at h
    rw [p.frameGaps2_last_advance.1] at h
    exact h

theorem actual_track_subset_dimers (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (pre post : Sequence) (hframe : p.reductionWord items bulkLengths gaps = pre ++ p.frameWord ++ post)
    (F : ActualFrameConfiguration p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).toFold)
      p.frameGaps1 p.frameGaps2
      (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).site p.framePart1.length)
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b) :
    frameTrackSites p.side F.first ⊆ (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).covered := by
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe
  have hm := p.side_ge
  have hterminal := p.shared_corner_is_first items bulkLengths gaps f hsupport hvertices pre post hframe F hsmall ha
  rw [p.actual_dimers_perfect_matching items bulkLengths gaps htotal hbulk f hsupport hvertices pre post hframe F hsmall ha]
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  have hr' := Finset.mem_range.mp hr
  apply Finset.mem_erase.mpr
  refine ⟨?_, p.frameTrackPoint_mem_remaining P F hsmall ha r hr'⟩
  rw [hterminal]
  exact frameTrackPoint_ne_terminal_corner p.side (by omega) F.first r

theorem actual_track_pairs_closed (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (pre post : Sequence) (hframe : p.reductionWord items bulkLengths gaps = pre ++ p.frameWord ++ post)
    (F : ActualFrameConfiguration p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).toFold)
      p.frameGaps1 p.frameGaps2
      (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).site p.framePart1.length)
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b) :
    ∀ i, (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).point (i, false) ∈ frameTrackSites p.side F.first ↔
      (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).point (i, true) ∈ frameTrackSites p.side F.first := by
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe
  let D := foldDimerPairs (p.reductionWord items bulkLengths gaps) f
  have hfull := p.actual_dimers_perfect_matching items bulkLengths gaps htotal hbulk f hsupport hvertices pre post hframe F hsmall ha
  have hclosed := p.frameTrackSites_isolated_remaining P F hsmall ha (foldSiteAt f 0)
  have hmem (i b) : D.point (i, b) ∈ (p.frameRemainingEdges P).erase (foldSiteAt f 0) := by
    rw [← hfull]
    exact Finset.mem_image.mpr ⟨(i,b), Finset.mem_univ _, rfl⟩
  intro i
  exact ⟨fun hi => hclosed _ hi _ (hmem i true) (foldDimerPairs_adjacent _ f i),
    fun hi => hclosed _ hi _ (hmem i false) (foldDimerPairs_adjacent _ f i).symm⟩

theorem actual_track_even_pair (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (pre post : Sequence) (hframe : p.reductionWord items bulkLengths gaps = pre ++ p.frameWord ++ post)
    (F : ActualFrameConfiguration p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).toFold)
      p.frameGaps1 p.frameGaps2
      (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).site p.framePart1.length)
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b)
    (k : ℕ) (hk : 2 * k < 2 * p.side - 2) :
    ∃ i b, frameTrackPoint p.side F.first (2 * k) =
        (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).point (i, b) ∧
      frameTrackPoint p.side F.first (2 * k + 1) =
        (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).point (i, !b) := by
  have hm := p.side_ge
  exact FinitePairFamily.track_even_pair _ p.side (by omega) F.first
    (p.actual_track_subset_dimers items bulkLengths gaps htotal hbulk f hsupport hvertices pre post hframe F hsmall ha)
    (p.actual_track_pairs_closed items bulkLengths gaps htotal hbulk f hsupport hvertices pre post hframe F hsmall ha)
    (foldDimerPairs_adjacent _ f) k hk

end ProteinFolding.Tetrahedral.ConstructionParameters

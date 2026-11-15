import ProteinFolding.Tetrahedral.FrameForcingTerminal
import ProteinFolding.Tetrahedral.FrameForcingMatchingSingleton
import ProteinFolding.Tetrahedral.FrameForcingMatchingPairs

/-! The actual HH dimers fill all nonvertex edge sites left after the
literal frame and the forced first monomer. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem shared_corner_in_remaining (p : ConstructionParameters) (P : OctWordPath p.side p.frameWord)
    (F : ActualFrameConfiguration p.side (hSupport p.frameWord P.toFold)
      p.frameGaps1 p.frameGaps2 P.site p.framePart1.length)
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b) :
    octEdgeZigzag p.side F.first (2 * p.side - 3) ∈ p.frameRemainingEdges P := by
  rw [frameRemainingEdges, Finset.mem_sdiff, Finset.mem_union, bulkDeletedEdges_mem_iff]
  have hm := p.side_ge
  have hedge := octEdgeZigzag_mem (by omega : 1 ≤ p.side) F.first
    (by omega : 2 * p.side - 3 < 2 * p.side - 1)
  refine ⟨⟨(octEdgeSite_surface p.side hedge).1, F.first.k, F.first.j, F.first.kj, hedge⟩, ?_⟩
  exact not_or.mpr ⟨p.shared_corner_not_frame P F hsmall ha, p.shared_corner_not_vertex F.first⟩

theorem actual_dimers_perfect_matching (p : ConstructionParameters)
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
    (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).covered =
      (p.frameRemainingEdges (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe)).erase
        (foldSiteAt f 0) := by
  let S := p.reductionWord items bulkLengths gaps
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe
  have hterminal := p.shared_corner_is_first items bulkLengths gaps f hsupport hvertices pre post hframe F hsmall ha
  have hfirst : foldSiteAt f 0 ∈ p.frameRemainingEdges P := by
    rw [hterminal]
    exact p.shared_corner_in_remaining P F hsmall ha
  have hD : Fintype.card (DimerOccurrence S) = p.reductionDimerCount := by
    rw [Fintype.card_coe, dimerStartIndices_card]
    exact p.reductionWord_dimerStartCount items bulkLengths gaps htotal hbulk
  have hzero : 0 < S.length := by
    dsimp only [S]
    rw [reductionWord, assembleReductionWord, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  apply (foldDimerPairs S f).covered_eq_erase_one (p.frameRemainingEdges P) (foldSiteAt f 0)
    (p.actual_dimers_subset_remaining S f hsupport hvertices pre post hframe)
  · rw [p.frameRemainingEdges_card P, hD]
  · exact hfirst
  · exact foldDimerPairs_first_not_covered S f hzero

end ProteinFolding.Tetrahedral.ConstructionParameters

import ProteinFolding.Tetrahedral.FrameForcing
import ProteinFolding.Tetrahedral.FrameForcingCornerSupport
import ProteinFolding.Tetrahedral.FrameForcingTerminalFactor

/-! The first monomer is the middle small-face corner forced by the actual
frame. All three possible H neighbours are already internal frame positions. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem shared_corner_is_first (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (pre post : Sequence) (hframe : p.reductionWord items bulkLengths gaps = pre ++ p.frameWord ++ post)
    (F : ActualFrameConfiguration p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).toFold)
      p.frameGaps1 p.frameGaps2
      (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).site p.framePart1.length)
    (hsmall : F.second.j = F.first.j) (ha : F.second.a = F.first.b) :
    foldSiteAt f 0 = octEdgeZigzag p.side F.first (2 * p.side - 3) := by
  let S := p.reductionWord items bulkLengths gaps
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe
  have hm1 : 1 ≤ p.side := le_trans (by decide : 1 ≤ 336) p.side_ge
  have hbound : 2 * p.side - 3 < 2 * p.side - 1 := by
    have hm := p.side_ge
    clear * - hm
    omega
  obtain ⟨lastPre, hlast⟩ := p.reductionWord_ends_P items bulkLengths gaps
  exact first_of_factor_corner S lastPre hlast f p.side hsupport hvertices pre p.frameWord post hframe
    (octEdgeZigzag p.side F.first (2 * p.side - 3))
    (octEdgeSite_surface p.side (octEdgeZigzag_mem hm1 F.first hbound)).1
    (p.shared_corner_not_vertex F.first) (p.shared_corner_not_frame P F hsmall ha)
    (oct_neighbours_of_lower_bound p.side F.first.j (octEdgeZigzag p.side F.first (2 * p.side - 3)) p.frameWord P.site
      (p.shared_corner_neighbours_in_frame P F hsmall ha))

def HasTerminalFrame (p : ConstructionParameters) (S : Sequence)
    (f : Fold tetrahedralLattice S.length) (hsupport : hSupport S f = octahedron p.side) : Prop :=
  ∃ (pre post : Sequence) (hframe : S = pre ++ p.frameWord ++ post),
    ∃ F : ActualFrameConfiguration p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).toFold)
      p.frameGaps1 p.frameGaps2
      (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post hframe).site p.framePart1.length,
      F.second.j = F.first.j ∧ F.second.a = F.first.b ∧
        foldSiteAt f 0 = octEdgeZigzag p.side F.first (2 * p.side - 3)

theorem reductionWord_terminal_frame (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hpos : ∀ s ∈ items, 0 < s)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side) :
    p.HasTerminalFrame (p.reductionWord items bulkLengths gaps) f hsupport := by
  obtain ⟨pre, post, hframe, F, hsmall, ha⟩ := p.reductionWord_shared_frame items bulkLengths gaps htotal hpos hbulk f hsupport hvertices
  exact ⟨pre, post, hframe, F, hsmall, ha,
    p.shared_corner_is_first items bulkLengths gaps f hsupport hvertices pre post hframe F hsmall ha⟩

end ProteinFolding.Tetrahedral.ConstructionParameters

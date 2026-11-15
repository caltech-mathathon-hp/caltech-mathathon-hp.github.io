import ProteinFolding.Tetrahedral.FrameForcingConfiguration
import ProteinFolding.Tetrahedral.FrameForcingActualChains

/-! The actual word forces every declared dimer chain meeting an entry
slot to have one dimer, and every chain meeting an exit slot to have at most three. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

theorem actual_chain_entry_slot_length (p : ConstructionParameters) (S : Sequence)
    (f : Fold tetrahedralLattice S.length) (hsupport : hSupport S f = octahedron p.side)
    (hvertices : (phpIndices S).image f.pos = octVertices p.side)
    (framePre framePost : Sequence) (hframe : S = framePre ++ p.frameWord ++ framePost)
    (F : ForcedFrameFamily p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport framePre p.frameWord framePost hframe).toFold)
      p.frameGaps1 p.frameGaps2)
    (chainPre chainPost : Sequence) (q : ℕ) (hchain : S = chainPre ++ capWord (dimerChain q) ++ chainPost)
    (k : ℕ) (hklo : 1 ≤ k) (hkhi : k ≤ p.bins + 1)
    (hmeet : ∃ i b, (factorDimerPairs S f chainPre chainPost q hchain).point (i, b) ∈
      edgeBlock p.side F.first (6 * k) 2) : q = 1 := by
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport framePre p.frameWord framePost hframe
  have hsub := p.actual_dimers_subset_remaining S f hsupport hvertices framePre framePost hframe
  have hA := (p.forced_family_entry_slot _ F k hklo hkhi).2
  have hT := p.forced_family_entry_slot_P3_closed _ F k hklo hkhi
  have hcard := factorDimerPairs_component_card S f p.side hsupport chainPre chainPost q hchain
    (p.frameRemainingEdges P) (edgeBlock p.side F.first (6 * k) 2) hsub hA hT hmeet
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  rw [edgeBlock_card p.side hm F.first] at hcard
  obtain ⟨i, _, _⟩ := hmeet
  have hi := i.isLt
  omega

theorem actual_chain_exit_slot_length (p : ConstructionParameters) (S : Sequence)
    (f : Fold tetrahedralLattice S.length) (hsupport : hSupport S f = octahedron p.side)
    (hvertices : (phpIndices S).image f.pos = octVertices p.side)
    (framePre framePost : Sequence) (hframe : S = framePre ++ p.frameWord ++ framePost)
    (F : ForcedFrameFamily p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport framePre p.frameWord framePost hframe).toFold)
      p.frameGaps1 p.frameGaps2)
    (chainPre chainPost : Sequence) (q : ℕ) (hchain : S = chainPre ++ capWord (dimerChain q) ++ chainPost)
    (k : ℕ) (hk : k ≤ p.bins)
    (hmeet : ∃ i b, (factorDimerPairs S f chainPre chainPost q hchain).point (i, b) ∈
      edgeBlock p.side F.second (2 * p.side - (10 * k + 13)) 6) : q ≤ 3 := by
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport framePre p.frameWord framePost hframe
  have hsub := p.actual_dimers_subset_remaining S f hsupport hvertices framePre framePost hframe
  have hA := (p.forced_family_exit_slot _ F k hk).2
  have hT := p.forced_family_exit_slot_P3_closed _ F k hk
  have hcard := factorDimerPairs_component_card S f p.side hsupport chainPre chainPost q hchain
    (p.frameRemainingEdges P) (edgeBlock p.side F.second (2 * p.side - (10 * k + 13)) 6) hsub hA hT hmeet
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  rw [edgeBlock_card p.side hm F.second] at hcard
  omega

end ProteinFolding.Tetrahedral.ConstructionParameters

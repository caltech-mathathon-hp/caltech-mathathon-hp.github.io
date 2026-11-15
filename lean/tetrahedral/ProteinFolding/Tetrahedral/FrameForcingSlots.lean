import ProteinFolding.Tetrahedral.FrameForcingGapFamily

/-! Every prescribed two-site entry slot and six-site exit slot is occupied
by the actual HH pairs. This holds for both possible frame incidences. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

theorem forced_family_entry_slot (p : ConstructionParameters) (H : Finset Site)
    (F : ForcedFrameFamily p.side H p.frameGaps1 p.frameGaps2)
    (k : ℕ) (hklo : 1 ≤ k) (hkhi : k ≤ p.bins + 1) :
    edgeBlock p.side F.first (6 * k) 2 ⊆ bulkDeletedEdges p.side \ (H ∪ octVertices p.side) ∧
      (∀ x ∈ edgeBlock p.side F.first (6 * k) 2,
        ∀ y ∈ bulkDeletedEdges p.side \ (H ∪ octVertices p.side),
        tetrahedralLattice.Adj x y → y ∈ edgeBlock p.side F.first (6 * k) 2) := by
  obtain ⟨j, hj, hbefore, hafter⟩ := p.frameGaps1_slot_indices k hklo hkhi
  have hm := p.side_ge
  have hfamily := p.family_side_bound
  exact F.gap_block (by omega) j hj (6 * k) 2 hbefore hafter (by omega) (by omega)

theorem forced_family_exit_slot (p : ConstructionParameters) (H : Finset Site)
    (F : ForcedFrameFamily p.side H p.frameGaps1 p.frameGaps2)
    (k : ℕ) (hk : k ≤ p.bins) :
    edgeBlock p.side F.second (2 * p.side - (10 * k + 13)) 6 ⊆
        bulkDeletedEdges p.side \ (H ∪ octVertices p.side) ∧
      (∀ x ∈ edgeBlock p.side F.second (2 * p.side - (10 * k + 13)) 6,
        ∀ y ∈ bulkDeletedEdges p.side \ (H ∪ octVertices p.side),
        tetrahedralLattice.Adj x y →
          y ∈ edgeBlock p.side F.second (2 * p.side - (10 * k + 13)) 6) := by
  obtain ⟨j, hj, hbefore, hafter⟩ := p.frameGaps2_slot_indices k hk
  have hm := p.side_ge
  have hfamily := p.family_side_bound
  exact F.swap.gap_block (by omega) j hj (2 * p.side - (10 * k + 13)) 6
    (by omega) (by omega) (by omega) (by omega)

theorem reductionWord_frame_slots_covered (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side)
    (pre post : Sequence) (heq : p.reductionWord items bulkLengths gaps = pre ++ p.frameWord ++ post) :
    ∃ F : ForcedFrameFamily p.side
      (hSupport p.frameWord (OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq).toFold)
      p.frameGaps1 p.frameGaps2,
      (∀ k, 1 ≤ k → k ≤ p.bins + 1 → edgeBlock p.side F.first (6 * k) 2 ⊆
        (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).covered) ∧
      (∀ k, k ≤ p.bins → edgeBlock p.side F.second (2 * p.side - (10 * k + 13)) 6 ⊆
        (foldDimerPairs (p.reductionWord items bulkLengths gaps) f).covered) := by
  let P := OctWordPath.ofFoldOccurrence f p.side hsupport pre p.frameWord post heq
  obtain ⟨F⟩ := p.frameWord_forced_family P
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  refine ⟨F, ?_, ?_⟩
  · intro k hklo hkhi
    obtain ⟨hW, hclosed⟩ := p.forced_family_entry_slot _ F k hklo hkhi
    exact p.reductionWord_even_component_covered items bulkLengths gaps htotal hbulk f hsupport hvertices
      pre post heq _ hW (by rw [edgeBlock_card p.side hm F.first]) hclosed
  · intro k hk
    obtain ⟨hW, hclosed⟩ := p.forced_family_exit_slot _ F k hk
    exact p.reductionWord_even_component_covered items bulkLengths gaps htotal hbulk f hsupport hvertices
      pre post heq _ hW (by rw [edgeBlock_card p.side hm F.second]) hclosed

end ProteinFolding.Tetrahedral.ConstructionParameters

import ProteinFolding.Tetrahedral.FrameForcingPackingExtraction
import ProteinFolding.Tetrahedral.FrameForcingEligibleBinChains
import ProteinFolding.Tetrahedral.FrameForcingActualSeparatorBlocks
import ProteinFolding.Tetrahedral.FrameForcingItemChainSize
import ProteinFolding.Tetrahedral.ReductionSoundnessPrelude

/-! Complete packing extraction from an actual normalized reduction fold.
The literal reduction supplies its frame, all separator windows, whole-item
bin confinement and the exact occurrence-preserving source partition. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem reductionWord_packing_of_normalized_fold (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hpos : ∀ s ∈ items, 0 < s)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side) :
    ∃ parts : List (List ℕ), parts.length = p.bins ∧ items.Perm parts.flatten ∧
      ∀ part ∈ parts, part.sum = p.capacity := by
  classical
  let c := (ReductionDimerProvenance.catalogue p items bulkLengths gaps hbulk).val
  letI := c.finiteIndex
  obtain ⟨framePre, framePost, hframe, F, hsmall, ha⟩ :=
    p.reductionWord_shared_frame items bulkLengths gaps htotal hpos hbulk f hsupport hvertices
  have hpositive := ReductionDimerProvenance.chain_positive p items bulkLengths gaps hbulk hpos
  have hcount₁ := ReductionDimerProvenance.small_chain_card p items bulkLengths gaps hbulk hpos 1 (Or.inl rfl)
  have hcount₃ := ReductionDimerProvenance.small_chain_card p items bulkLengths gaps hbulk hpos 3 (Or.inr (Or.inr rfl))
  have hsingles := p.actual_catalogue_singleton_sites items bulkLengths gaps htotal hbulk f hsupport hvertices
    framePre framePost hframe F.toForcedFrameFamily c hpositive hcount₁
  have hexits := p.actual_catalogue_exit_sites items bulkLengths gaps htotal hbulk f hsupport hvertices
    framePre framePost hframe F.toForcedFrameFamily c hpositive hcount₁ hcount₃
  obtain ⟨starts, hwindow, hexhaust⟩ := p.actual_separator_blocks items bulkLengths gaps htotal hpos hbulk
    f hsupport hvertices framePre framePost hframe F hsmall ha
  have htrack := p.actual_track_subset_dimers items bulkLengths gaps htotal hbulk f hsupport hvertices
    framePre framePost hframe F hsmall ha
  have hclasssize (t : c.Index) (hne₁ : c.q t ≠ 1) (hne₂ : c.q t ≠ 2) (hne₃ : c.q t ≠ 3)
      (hbound : c.q t ≤ p.binDimers + p.sigma + 6) : t ∈ c.itemIndices := by
    have hitem := ReductionDimerProvenance.chain_is_item_of_bin_size p items bulkLengths gaps hbulk
      t hne₁ hne₂ hne₃ hbound
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hitem⟩
  refine c.packing_of_bin_classification f p F.first starts hwindow htrack items c.itemIndices
    (fun t => (c.tag t).itemValue) ?_ ?_ ?_ ?_ ?_
  · exact ReductionDimerProvenance.items_perm_indices p items bulkLengths gaps hbulk
  · intro t ht
    exact (ReductionDimerProvenance.item_index_size p items bulkLengths gaps hbulk hpos t ht).1
  · intro t ht
    exact (ReductionDimerProvenance.item_index_size p items bulkLengths gaps hbulk hpos t ht).2
  · exact htotal.trans (Nat.mul_comm _ _)
  · intro k t hmeet
    exact c.bin_chain_eligible f p hsupport F.first F.second F.next_big hsmall ha starts hwindow
      hexhaust hsingles hexits c.itemIndices hclasssize k t hmeet

theorem reductionWord_threshold_packing (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hpos : ∀ s ∈ items, 0 < s)
    (hbulkMass : 24 * p.side + bulkLengths.sum = octahedralNumber p.side + 42)
    (hbulkRuns : ∀ n ∈ bulkLengths, 3 ≤ n)
    (hfold : HPStringFold (p.reductionWord items bulkLengths gaps)
      (2 * (octahedralNumber p.side : ℤ) - 2 * (p.side ^ 2 : ℕ))) :
    ∃ parts : List (List ℕ), parts.length = p.bins ∧ items.Perm parts.flatten ∧
      ∀ part ∈ parts, part.sum = p.capacity := by
  obtain ⟨f, hsupport, hvertices⟩ :=
    (p.reductionWord_threshold_iff_normal_form items bulkLengths gaps htotal hbulkMass hbulkRuns).mp hfold
  exact p.reductionWord_packing_of_normalized_fold items bulkLengths gaps htotal hpos hbulkRuns f hsupport hvertices

end ProteinFolding.Tetrahedral.ConstructionParameters

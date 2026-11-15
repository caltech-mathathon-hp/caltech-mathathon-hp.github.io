import ProteinFolding.Tetrahedral.FrameForcingFromCatalogue
import ProteinFolding.Tetrahedral.ReductionDimerProvenanceCounts
import ProteinFolding.Tetrahedral.ReductionDimerProvenanceSeparator

/-! Concrete Section 7 frame forcing for the actual reduction word.
After normalization of H support and the six PHP vertices, both frame edges
and their intended common small face follow from the written word itself. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

theorem reductionWord_shared_frame (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) (hpos : ∀ s ∈ items, 0 < s)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hsupport : hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side)
    (hvertices : (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side) :
    p.HasSharedFrame (p.reductionWord items bulkLengths gaps) f hsupport := by
  let c := (ReductionDimerProvenance.catalogue p items bulkLengths gaps hbulk).val
  have hpositive := ReductionDimerProvenance.chain_positive p items bulkLengths gaps hbulk hpos
  have hcount₁ := ReductionDimerProvenance.small_chain_card p items bulkLengths gaps hbulk hpos 1 (Or.inl rfl)
  have hcount₃ := ReductionDimerProvenance.small_chain_card p items bulkLengths gaps hbulk hpos 3 (Or.inr (Or.inr rfl))
  obtain ⟨pre, post, iE, iX, hsep, hE, hX, _, _, hpreE, hpreX⟩ :=
    ReductionDimerProvenance.separator_witnesses p items bulkLengths gaps hbulk 0 (by omega)
  apply p.shared_frame_of_actual_catalogue items bulkLengths gaps htotal hbulk f hsupport hvertices
    c hpositive hcount₁ hcount₃ pre post hsep iE iX hE hX hpreE
  simpa only [ReductionDimerProvenance.separatorExitOffset, Nat.add_assoc] using hpreX

end ProteinFolding.Tetrahedral.ConstructionParameters

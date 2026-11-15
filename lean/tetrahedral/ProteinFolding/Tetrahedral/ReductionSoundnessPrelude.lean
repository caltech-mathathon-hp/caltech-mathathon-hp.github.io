import ProteinFolding.Tetrahedral.ReductionWordCounts
import ProteinFolding.Tetrahedral.SoundnessDimers

/-! Apply geometric rigidity to the literal reduction word. The exact bulk
mass and its minimum run lengths are explicit inputs; the bulk cover must
provide these, as well as the construction needed for completeness. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

theorem reductionWord_threshold_normal_form (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity)
    (hbulkMass : 24 * p.side + bulkLengths.sum = octahedralNumber p.side + 42)
    (hbulkRuns : ∀ n ∈ bulkLengths, 3 ≤ n)
    (f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length)
    (hscore : 2 * (octahedralNumber p.side : ℤ) - 2 * (p.side ^ 2 : ℕ) ≤
      (bondCount (p.reductionWord items bulkLengths gaps) f : ℤ)) :
    ∃ c ∈ hSupport (p.reductionWord items bulkLengths gaps) f,
      hSupport (p.reductionWord items bulkLengths gaps) (normalizeFold f c) = octahedron p.side ∧
      (phpIndices (p.reductionWord items bulkLengths gaps)).image (normalizeFold f c).pos =
        octVertices p.side ∧
      bondCount (p.reductionWord items bulkLengths gaps) (normalizeFold f c) =
        2 * octahedralNumber p.side - 2 * p.side ^ 2 := by
  have hm : 2 ≤ p.side := by have h := p.side_ge; omega
  have hcount := p.reductionWord_hydrophobicCount items bulkLengths gaps htotal hbulkMass
  have hN : p.side ^ 2 ≤ octahedralNumber p.side := by unfold octahedralNumber; omega
  have hscore' : 2 * octahedralNumber p.side - 2 * p.side ^ 2 ≤
      bondCount (p.reductionWord items bulkLengths gaps) f := by omega
  obtain ⟨c, hc, hshape, heq⟩ := fold_threshold_normalizes _ f p.side (by omega) hcount hscore'
  refine ⟨c, hc, hshape, ?_, heq⟩
  exact six_phpIndices_fill_vertices _ (normalizeFold f c) p.side hm hshape
    (p.reductionWord_phpIndices_card items bulkLengths gaps hbulkRuns)

theorem reductionWord_threshold_iff_normal_form (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity)
    (hbulkMass : 24 * p.side + bulkLengths.sum = octahedralNumber p.side + 42)
    (hbulkRuns : ∀ n ∈ bulkLengths, 3 ≤ n) :
    HPStringFold (p.reductionWord items bulkLengths gaps)
      (2 * (octahedralNumber p.side : ℤ) - 2 * (p.side ^ 2 : ℕ)) ↔
      ∃ f : Fold tetrahedralLattice (p.reductionWord items bulkLengths gaps).length,
        hSupport (p.reductionWord items bulkLengths gaps) f = octahedron p.side ∧
        (phpIndices (p.reductionWord items bulkLengths gaps)).image f.pos = octVertices p.side := by
  have hm : 2 ≤ p.side := by have h := p.side_ge; omega
  have hcount := p.reductionWord_hydrophobicCount items bulkLengths gaps htotal hbulkMass
  rw [octahedral_threshold_iff_oct_support _ p.side (by omega) hcount]
  constructor
  · rintro ⟨f, hshape⟩
    exact ⟨f, hshape, six_phpIndices_fill_vertices _ f p.side hm hshape
      (p.reductionWord_phpIndices_card items bulkLengths gaps hbulkRuns)⟩
  · rintro ⟨f, hshape, _⟩
    exact ⟨f, hshape⟩

end ProteinFolding.Tetrahedral.ConstructionParameters

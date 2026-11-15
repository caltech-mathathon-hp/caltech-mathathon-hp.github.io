import ProteinFolding.Tetrahedral.OctahedralEdges

/-! Small model checks and axiom reports for the octahedral geometry. -/

namespace ProteinFolding.Tetrahedral.OctahedralChecks

private def origin : Site := ⟨fun _ => 0, by left; constructor <;> decide⟩

example : (octahedron 0).card = 0 := by rw [octahedron_card_formula]; decide
example : (octahedron 1).card = 1 := by rw [octahedron_card_formula]; decide
example : (octahedron 2).card = 10 := by rw [octahedron_card_formula]; decide
example : (octahedron 3).card = 35 := by rw [octahedron_card_formula]; decide
example : (octahedron 4).card = 84 := by rw [octahedron_card_formula]; decide
example : (finiteLayer (octahedron 4) 0).card = 16 := by
  rw [card_octahedron_central_layer]
  decide
example : (finiteLayer (octahedron 4) 3).card = 6 := by
  exact card_octahedron_odd_layer 4 1
example : (finiteLayer (octahedron 4) (-3)).card = 6 := by
  rw [card_octahedron_layer_neg]
  exact card_octahedron_odd_layer 4 1

example : internalEdgeCount (octahedron 1) = 0 := by
  rw [octahedron_internalEdgeCount, octahedralNumber_formula]
  decide
example : internalEdgeCount (octahedron 2) = 12 := by
  rw [octahedron_internalEdgeCount, octahedralNumber_formula]
  decide
example : internalEdgeCount (octahedron 3) = 52 := by
  rw [octahedron_internalEdgeCount, octahedralNumber_formula]
  decide
example : boundaryCount (octahedron 1) = 4 := by rw [octahedron_boundaryCount]; decide
example : boundaryCount (octahedron 2) = 16 := by rw [octahedron_boundaryCount]; decide
example : boundaryCount (octahedron 3) = 36 := by rw [octahedron_boundaryCount]; decide

private theorem origin_mem_one : origin ∈ octahedron 1 := by
  rw [mem_octahedron]
  decide

-- The m=1 exception to the later six-distinct-vertex statement is explicit.
example : octahedron 1 = {origin} := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    have heq := Finset.mem_singleton.mp hp
    subst p
    exact origin_mem_one
  · rw [Finset.card_singleton, octahedron_card_formula]
    decide

example (d : Fin 4) : step origin d ∉ octahedron 1 := by
  rw [step_not_mem_octahedron_A 1 (show InASublattice origin.val by decide) origin_mem_one]
  fin_cases d <;> rfl

end ProteinFolding.Tetrahedral.OctahedralChecks

#print axioms ProteinFolding.Tetrahedral.mem_octahedron
#print axioms ProteinFolding.Tetrahedral.tetraCoordinate_eq_dot
#print axioms ProteinFolding.Tetrahedral.inOctahedron_iff_A
#print axioms ProteinFolding.Tetrahedral.inOctahedron_iff_B
#print axioms ProteinFolding.Tetrahedral.tetraCoordinate_step_A
#print axioms ProteinFolding.Tetrahedral.tetraCoordinate_step_B
#print axioms ProteinFolding.Tetrahedral.step_not_mem_octahedron_A
#print axioms ProteinFolding.Tetrahedral.step_not_mem_octahedron_B
#print axioms ProteinFolding.Tetrahedral.dangling_unique_inside
#print axioms ProteinFolding.Tetrahedral.dangling_not_adjacent
#print axioms ProteinFolding.Tetrahedral.octMirror_adj_iff
#print axioms ProteinFolding.Tetrahedral.card_octahedron_even_layer
#print axioms ProteinFolding.Tetrahedral.card_octahedron_odd_layer
#print axioms ProteinFolding.Tetrahedral.card_octahedron_layer_neg
#print axioms ProteinFolding.Tetrahedral.octahedron_card
#print axioms ProteinFolding.Tetrahedral.octahedron_card_formula
#print axioms ProteinFolding.Tetrahedral.octahedron_internalEdgeCount_add
#print axioms ProteinFolding.Tetrahedral.octahedron_internalEdgeCount
#print axioms ProteinFolding.Tetrahedral.octahedron_boundaryCount

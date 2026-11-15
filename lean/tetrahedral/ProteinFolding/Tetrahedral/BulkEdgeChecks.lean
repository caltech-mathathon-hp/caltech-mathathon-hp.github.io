import ProteinFolding.Tetrahedral.BulkEdgeCount

namespace ProteinFolding.Tetrahedral

example : (bulkDeletedEdges 3).card = 30 := by
  have h := bulkDeletedEdges_card_add (m := 3) (by decide)
  omega

example : (bulkDeletedEdges 4).card = 54 := by
  have h := bulkDeletedEdges_card_add (m := 4) (by decide)
  omega

example : (bulkInterior 3).card = 5 := by
  have h := bulkInterior_card_add (m := 3) (by decide)
  have hN : octahedralNumber 3 = 35 := by rw [octahedralNumber_formula]; rfl
  rw [hN] at h
  omega

#print axioms deleted_even_central_iff
#print axioms deleted_even_positive_iff
#print axioms deleted_odd_central_iff
#print axioms deleted_odd_positive_iff
#print axioms evenDeletedLayer_card_central
#print axioms evenDeletedLayer_card_positive
#print axioms oddDeletedLayer_card_central
#print axioms oddDeletedLayer_card_positive
#print axioms bulkDeletedEdges_card_add
#print axioms bulkInterior_card_add_edges
#print axioms bulkInterior_card_add

end ProteinFolding.Tetrahedral

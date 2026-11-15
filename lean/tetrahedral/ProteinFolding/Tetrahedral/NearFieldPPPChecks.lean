import ProteinFolding.Tetrahedral.NearFieldPPPPairwise
import ProteinFolding.Tetrahedral.NearFieldPPPSeparation
import ProteinFolding.Tetrahedral.NearFieldPPPTrackColumns

namespace ProteinFolding.Tetrahedral

example : columnOpposite entryEdgeFrame.k = entryEdgeFrame.j := by decide
example : columnOpposite exitEdgeFrame.k ≠ exitEdgeFrame.j := by decide
example : columnOpposite trackEdgeFrame.k ≠ trackEdgeFrame.j := by decide

#print axioms facePPPSite_injective
#print axioms facePPPFold
#print axioms faceFourStep_eq_twoStep
#print axioms facePPPFold_first_seam
#print axioms facePPPFold_last_seam
#print axioms facePPPFold_mem_skin_one
#print axioms edgePPP_endpoint
#print axioms edgePPPFold_mem_skin_one
#print axioms facePPP_middle_not_dangling
#print axioms facePPP_middle_column_owner
#print axioms facePPPFold_column_owner
#print axioms edgePPPFold_column_owner
#print axioms edgePPPFold_ne_column_of_owner_ne
#print axioms edgePPPFold_height
#print axioms edgePPPFolds_disjoint_of_parity_or_gap
#print axioms trackPPPFold_coordinates
#print axioms trackPPPFold_ne_frameP_from_first
#print axioms trackPPPFold_column_owner
#print axioms trackPPPFold_ne_bulkColumn
#print axioms facePPP_middle_normal_not_dangling
#print axioms no_four_distinct_directions_avoiding
#print axioms facePPP_middles_ne_of_endpoints_disjoint
#print axioms facePPPFolds_disjoint_of_endpoints_disjoint

end ProteinFolding.Tetrahedral

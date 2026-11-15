import ProteinFolding.Tetrahedral.BulkNearEdgeReference0
import ProteinFolding.Tetrahedral.BulkNearEdgeReference1
import ProteinFolding.Tetrahedral.BulkNearEdgeReference2
import ProteinFolding.Tetrahedral.BulkNearEdgeReference3
import ProteinFolding.Tetrahedral.BulkNearEdgeReference4
import ProteinFolding.Tetrahedral.BulkNearEdgeReference5
import ProteinFolding.Tetrahedral.BulkNearEdgeReference6
import ProteinFolding.Tetrahedral.BulkNearEdgeReference7
import ProteinFolding.Tetrahedral.BulkNearEdgeReference8
import ProteinFolding.Tetrahedral.BulkNearEdgeReference9

/-! The full near-edge degree certificate assembled from ten independently
kernel-checked anchor values. -/

namespace ProteinFolding.Tetrahedral

theorem bulkNearEdge_reference_damaged_degree_split (F : OctEdgeFrame) (t : Fin 10)
    (odd : Bool) (d : Fin 4) :
    bulkFastDamaged 50 (bulkEdgeCandidate 50 F t.val odd d (by decide)) →
      2 ≤ (bulkFastCoverDirections 50 (bulkEdgeCandidate 50 F t.val odd d (by decide))).card := by
  fin_cases t
  · exact bulkNearEdge_reference_damaged_degree_0 F odd d
  · exact bulkNearEdge_reference_damaged_degree_1 F odd d
  · exact bulkNearEdge_reference_damaged_degree_2 F odd d
  · exact bulkNearEdge_reference_damaged_degree_3 F odd d
  · exact bulkNearEdge_reference_damaged_degree_4 F odd d
  · exact bulkNearEdge_reference_damaged_degree_5 F odd d
  · exact bulkNearEdge_reference_damaged_degree_6 F odd d
  · exact bulkNearEdge_reference_damaged_degree_7 F odd d
  · exact bulkNearEdge_reference_damaged_degree_8 F odd d
  · exact bulkNearEdge_reference_damaged_degree_9 F odd d

end ProteinFolding.Tetrahedral

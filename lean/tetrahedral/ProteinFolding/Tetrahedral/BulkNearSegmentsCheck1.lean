import ProteinFolding.Tetrahedral.BulkNearVertexEliminators
import ProteinFolding.Tetrahedral.BulkNearSupportBatch1_0
import ProteinFolding.Tetrahedral.BulkNearSupportBatch1_1
import ProteinFolding.Tetrahedral.BulkNearSupportBatch1_2
import ProteinFolding.Tetrahedral.BulkNearSupportBatch1_3

/-! Original public support theorem, using opaque vertex metadata. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem bulkNearSegment_reference_quick_1 (i : Fin 234)
    (hv : bulkNearSegmentVertex i = 1) :
    BulkSegmentQuickCheck 50 (bulkNearSegmentSupport i) (bulkNearSegmentRoot i)
      (bulkNearSegmentRank i) (bulkNearSegmentPrev i) := by
  exact bulkNearVertex_cases_1 BulkNearSupportQuickCheck
    bulkNearSupportBatch_1_0.1
    bulkNearSupportBatch_1_0.2.1
    bulkNearSupportBatch_1_0.2.2.1
    bulkNearSupportBatch_1_0.2.2.2.1
    bulkNearSupportBatch_1_0.2.2.2.2.1
    bulkNearSupportBatch_1_0.2.2.2.2.2.1
    bulkNearSupportBatch_1_0.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_0.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_0.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_0.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_0.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_0.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_0.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_0.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearSupportBatch_1_1.1
    bulkNearSupportBatch_1_1.2.1
    bulkNearSupportBatch_1_1.2.2.1
    bulkNearSupportBatch_1_1.2.2.2.1
    bulkNearSupportBatch_1_1.2.2.2.2.1
    bulkNearSupportBatch_1_1.2.2.2.2.2.1
    bulkNearSupportBatch_1_1.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_1.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_1.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_1.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_1.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_1.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_1.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_1.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearSupportBatch_1_2.1
    bulkNearSupportBatch_1_2.2.1
    bulkNearSupportBatch_1_2.2.2.1
    bulkNearSupportBatch_1_2.2.2.2.1
    bulkNearSupportBatch_1_2.2.2.2.2.1
    bulkNearSupportBatch_1_2.2.2.2.2.2.1
    bulkNearSupportBatch_1_2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearSupportBatch_1_3.1
    bulkNearSupportBatch_1_3.2.1
    bulkNearSupportBatch_1_3.2.2.1
    bulkNearSupportBatch_1_3.2.2.2.1
    bulkNearSupportBatch_1_3.2.2.2.2.1
    bulkNearSupportBatch_1_3.2.2.2.2.2.1
    bulkNearSupportBatch_1_3.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_3.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_3.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_3.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_3.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_3.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_1_3.2.2.2.2.2.2.2.2.2.2.2.2
    i hv

end ProteinFolding.Tetrahedral

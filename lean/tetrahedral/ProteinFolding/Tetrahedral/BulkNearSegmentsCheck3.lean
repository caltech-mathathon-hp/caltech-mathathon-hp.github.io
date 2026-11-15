import ProteinFolding.Tetrahedral.BulkNearVertexEliminators
import ProteinFolding.Tetrahedral.BulkNearSupportBatch3_0
import ProteinFolding.Tetrahedral.BulkNearSupportBatch3_1
import ProteinFolding.Tetrahedral.BulkNearSupportBatch3_2

/-! Original public support theorem, using opaque vertex metadata. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem bulkNearSegment_reference_quick_3 (i : Fin 234)
    (hv : bulkNearSegmentVertex i = 3) :
    BulkSegmentQuickCheck 50 (bulkNearSegmentSupport i) (bulkNearSegmentRoot i)
      (bulkNearSegmentRank i) (bulkNearSegmentPrev i) := by
  exact bulkNearVertex_cases_3 BulkNearSupportQuickCheck
    bulkNearSupportBatch_3_0.1
    bulkNearSupportBatch_3_0.2.1
    bulkNearSupportBatch_3_0.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearSupportBatch_3_1.1
    bulkNearSupportBatch_3_1.2.1
    bulkNearSupportBatch_3_1.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearSupportBatch_3_2.1
    bulkNearSupportBatch_3_2.2.1
    bulkNearSupportBatch_3_2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_3_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    i hv

end ProteinFolding.Tetrahedral

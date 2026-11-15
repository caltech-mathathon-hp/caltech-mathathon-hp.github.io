import ProteinFolding.Tetrahedral.BulkNearVertexEliminators
import ProteinFolding.Tetrahedral.BulkNearSupportBatch2_0
import ProteinFolding.Tetrahedral.BulkNearSupportBatch2_1
import ProteinFolding.Tetrahedral.BulkNearSupportBatch2_2

/-! Original public support theorem, using opaque vertex metadata. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem bulkNearSegment_reference_quick_2 (i : Fin 234)
    (hv : bulkNearSegmentVertex i = 2) :
    BulkSegmentQuickCheck 50 (bulkNearSegmentSupport i) (bulkNearSegmentRoot i)
      (bulkNearSegmentRank i) (bulkNearSegmentPrev i) := by
  exact bulkNearVertex_cases_2 BulkNearSupportQuickCheck
    bulkNearSupportBatch_2_0.1
    bulkNearSupportBatch_2_0.2.1
    bulkNearSupportBatch_2_0.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearSupportBatch_2_1.1
    bulkNearSupportBatch_2_1.2.1
    bulkNearSupportBatch_2_1.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearSupportBatch_2_2.1
    bulkNearSupportBatch_2_2.2.1
    bulkNearSupportBatch_2_2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_2_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    i hv

end ProteinFolding.Tetrahedral

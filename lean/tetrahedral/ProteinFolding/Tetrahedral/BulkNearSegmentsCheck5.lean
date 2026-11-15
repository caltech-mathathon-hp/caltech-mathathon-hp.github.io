import ProteinFolding.Tetrahedral.BulkNearVertexEliminators
import ProteinFolding.Tetrahedral.BulkNearSupportBatch5_0

/-! Original public support theorem, using opaque vertex metadata. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem bulkNearSegment_reference_quick_5 (i : Fin 234)
    (hv : bulkNearSegmentVertex i = 5) :
    BulkSegmentQuickCheck 50 (bulkNearSegmentSupport i) (bulkNearSegmentRoot i)
      (bulkNearSegmentRank i) (bulkNearSegmentPrev i) := by
  exact bulkNearVertex_cases_5 BulkNearSupportQuickCheck
    bulkNearSupportBatch_5_0.1
    bulkNearSupportBatch_5_0.2.1
    bulkNearSupportBatch_5_0.2.2.1
    bulkNearSupportBatch_5_0.2.2.2.1
    bulkNearSupportBatch_5_0.2.2.2.2.1
    bulkNearSupportBatch_5_0.2.2.2.2.2.1
    bulkNearSupportBatch_5_0.2.2.2.2.2.2.1
    bulkNearSupportBatch_5_0.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_5_0.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_5_0.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_5_0.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_5_0.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_5_0.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_5_0.2.2.2.2.2.2.2.2.2.2.2.2.2
    i hv

end ProteinFolding.Tetrahedral

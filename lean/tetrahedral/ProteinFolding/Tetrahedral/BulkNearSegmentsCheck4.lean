import ProteinFolding.Tetrahedral.BulkNearVertexEliminators
import ProteinFolding.Tetrahedral.BulkNearSupportBatch4_0
import ProteinFolding.Tetrahedral.BulkNearSupportBatch4_1
import ProteinFolding.Tetrahedral.BulkNearSupportBatch4_2
import ProteinFolding.Tetrahedral.BulkNearSupportBatch4_3

/-! Original public support theorem, using opaque vertex metadata. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem bulkNearSegment_reference_quick_4 (i : Fin 234)
    (hv : bulkNearSegmentVertex i = 4) :
    BulkSegmentQuickCheck 50 (bulkNearSegmentSupport i) (bulkNearSegmentRoot i)
      (bulkNearSegmentRank i) (bulkNearSegmentPrev i) := by
  exact bulkNearVertex_cases_4 BulkNearSupportQuickCheck
    bulkNearSupportBatch_4_0.1
    bulkNearSupportBatch_4_0.2.1
    bulkNearSupportBatch_4_0.2.2.1
    bulkNearSupportBatch_4_0.2.2.2.1
    bulkNearSupportBatch_4_0.2.2.2.2.1
    bulkNearSupportBatch_4_0.2.2.2.2.2.1
    bulkNearSupportBatch_4_0.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_0.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_0.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_0.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_0.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_0.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_0.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_0.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearSupportBatch_4_1.1
    bulkNearSupportBatch_4_1.2.1
    bulkNearSupportBatch_4_1.2.2.1
    bulkNearSupportBatch_4_1.2.2.2.1
    bulkNearSupportBatch_4_1.2.2.2.2.1
    bulkNearSupportBatch_4_1.2.2.2.2.2.1
    bulkNearSupportBatch_4_1.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_1.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_1.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_1.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_1.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_1.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_1.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_1.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearSupportBatch_4_2.1
    bulkNearSupportBatch_4_2.2.1
    bulkNearSupportBatch_4_2.2.2.1
    bulkNearSupportBatch_4_2.2.2.2.1
    bulkNearSupportBatch_4_2.2.2.2.2.1
    bulkNearSupportBatch_4_2.2.2.2.2.2.1
    bulkNearSupportBatch_4_2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearSupportBatch_4_3.1
    bulkNearSupportBatch_4_3.2.1
    bulkNearSupportBatch_4_3.2.2.1
    bulkNearSupportBatch_4_3.2.2.2.1
    bulkNearSupportBatch_4_3.2.2.2.2.1
    bulkNearSupportBatch_4_3.2.2.2.2.2.1
    bulkNearSupportBatch_4_3.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_3.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_3.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_3.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_3.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_3.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearSupportBatch_4_3.2.2.2.2.2.2.2.2.2.2.2.2
    i hv

end ProteinFolding.Tetrahedral

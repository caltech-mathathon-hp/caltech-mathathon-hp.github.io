import ProteinFolding.Tetrahedral.BulkNearSegmentsData

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem bulkNearSegment_reference_quick_0 (i : Fin 234)
    (hv : bulkNearSegmentVertex i = 0) :
    BulkSegmentQuickCheck 50 (bulkNearSegmentSupport i) (bulkNearSegmentRoot i)
      (bulkNearSegmentRank i) (bulkNearSegmentPrev i) := by
  revert i
  decide

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkNearReferenceSpec

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem bulkNearBox_reference_1 (i : Fin 234) (hv : bulkNearSegmentVertex i = 1) :
    BulkNearBoxReferenceCheck i := by
  revert i
  unfold BulkNearBoxReferenceCheck InBulkVertexBox
  decide

end ProteinFolding.Tetrahedral

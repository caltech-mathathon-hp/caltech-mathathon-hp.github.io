import ProteinFolding.Tetrahedral.BulkNearCoreCertificates

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem bulkNearCore_reference_0 (i : Fin 234) (hv : bulkNearSegmentVertex i = 0) :
    BulkNearCoreEscapeCheck i := by
  unfold BulkNearCoreEscapeCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  revert i
  decide +kernel

end ProteinFolding.Tetrahedral


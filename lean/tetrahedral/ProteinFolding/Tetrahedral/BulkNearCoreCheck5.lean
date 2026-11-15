import ProteinFolding.Tetrahedral.BulkNearVertexEliminators
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch5_0

/-! The opaque metadata eliminator is instantiated only after its proof.
The public theorem retains the original core predicate. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem bulkNearCore_reference_5 (i : Fin 234)
    (hv : bulkNearSegmentVertex i = 5) : BulkNearCoreEscapeCheck i := by
  apply bulkNearCoreFastCheck_sound
  exact bulkNearVertex_cases_5 BulkNearCoreFastCheck
    bulkNearCoreFastBatch_5_0.1
    bulkNearCoreFastBatch_5_0.2.1
    bulkNearCoreFastBatch_5_0.2.2.1
    bulkNearCoreFastBatch_5_0.2.2.2.1
    bulkNearCoreFastBatch_5_0.2.2.2.2.1
    bulkNearCoreFastBatch_5_0.2.2.2.2.2.1
    bulkNearCoreFastBatch_5_0.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_5_0.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_5_0.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_5_0.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_5_0.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_5_0.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_5_0.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_5_0.2.2.2.2.2.2.2.2.2.2.2.2.2
    i hv

end ProteinFolding.Tetrahedral

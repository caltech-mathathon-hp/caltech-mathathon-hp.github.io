import ProteinFolding.Tetrahedral.BulkNearVertexEliminators
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch3_0
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch3_1
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch3_2

/-! The opaque metadata eliminator is instantiated only after its proof.
The public theorem retains the original core predicate. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem bulkNearCore_reference_3 (i : Fin 234)
    (hv : bulkNearSegmentVertex i = 3) : BulkNearCoreEscapeCheck i := by
  apply bulkNearCoreFastCheck_sound
  exact bulkNearVertex_cases_3 BulkNearCoreFastCheck
    bulkNearCoreFastBatch_3_0.1
    bulkNearCoreFastBatch_3_0.2.1
    bulkNearCoreFastBatch_3_0.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoreFastBatch_3_1.1
    bulkNearCoreFastBatch_3_1.2.1
    bulkNearCoreFastBatch_3_1.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoreFastBatch_3_2.1
    bulkNearCoreFastBatch_3_2.2.1
    bulkNearCoreFastBatch_3_2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_3_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    i hv

end ProteinFolding.Tetrahedral

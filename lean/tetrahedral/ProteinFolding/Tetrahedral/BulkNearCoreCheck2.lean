import ProteinFolding.Tetrahedral.BulkNearVertexEliminators
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch2_0
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch2_1
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch2_2

/-! The opaque metadata eliminator is instantiated only after its proof.
The public theorem retains the original core predicate. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem bulkNearCore_reference_2 (i : Fin 234)
    (hv : bulkNearSegmentVertex i = 2) : BulkNearCoreEscapeCheck i := by
  apply bulkNearCoreFastCheck_sound
  exact bulkNearVertex_cases_2 BulkNearCoreFastCheck
    bulkNearCoreFastBatch_2_0.1
    bulkNearCoreFastBatch_2_0.2.1
    bulkNearCoreFastBatch_2_0.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoreFastBatch_2_1.1
    bulkNearCoreFastBatch_2_1.2.1
    bulkNearCoreFastBatch_2_1.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoreFastBatch_2_2.1
    bulkNearCoreFastBatch_2_2.2.1
    bulkNearCoreFastBatch_2_2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_2_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    i hv

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkNearVertexEliminators
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch1_0
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch1_1
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch1_2
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch1_3

/-! The opaque metadata eliminator is instantiated only after its proof.
The public theorem retains the original core predicate. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem bulkNearCore_reference_1 (i : Fin 234)
    (hv : bulkNearSegmentVertex i = 1) : BulkNearCoreEscapeCheck i := by
  apply bulkNearCoreFastCheck_sound
  exact bulkNearVertex_cases_1 BulkNearCoreFastCheck
    bulkNearCoreFastBatch_1_0.1
    bulkNearCoreFastBatch_1_0.2.1
    bulkNearCoreFastBatch_1_0.2.2.1
    bulkNearCoreFastBatch_1_0.2.2.2.1
    bulkNearCoreFastBatch_1_0.2.2.2.2.1
    bulkNearCoreFastBatch_1_0.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_0.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_0.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_0.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_0.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_0.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_0.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_0.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_0.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoreFastBatch_1_1.1
    bulkNearCoreFastBatch_1_1.2.1
    bulkNearCoreFastBatch_1_1.2.2.1
    bulkNearCoreFastBatch_1_1.2.2.2.1
    bulkNearCoreFastBatch_1_1.2.2.2.2.1
    bulkNearCoreFastBatch_1_1.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_1.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_1.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_1.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_1.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_1.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_1.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_1.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_1.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoreFastBatch_1_2.1
    bulkNearCoreFastBatch_1_2.2.1
    bulkNearCoreFastBatch_1_2.2.2.1
    bulkNearCoreFastBatch_1_2.2.2.2.1
    bulkNearCoreFastBatch_1_2.2.2.2.2.1
    bulkNearCoreFastBatch_1_2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoreFastBatch_1_3.1
    bulkNearCoreFastBatch_1_3.2.1
    bulkNearCoreFastBatch_1_3.2.2.1
    bulkNearCoreFastBatch_1_3.2.2.2.1
    bulkNearCoreFastBatch_1_3.2.2.2.2.1
    bulkNearCoreFastBatch_1_3.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_3.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_3.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_3.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_3.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_3.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_3.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_1_3.2.2.2.2.2.2.2.2.2.2.2.2
    i hv

end ProteinFolding.Tetrahedral

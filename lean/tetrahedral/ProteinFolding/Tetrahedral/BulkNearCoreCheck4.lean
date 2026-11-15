import ProteinFolding.Tetrahedral.BulkNearVertexEliminators
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch4_0
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch4_1
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch4_2
import ProteinFolding.Tetrahedral.BulkNearCoreFastBatch4_3

/-! The opaque metadata eliminator is instantiated only after its proof.
The public theorem retains the original core predicate. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem bulkNearCore_reference_4 (i : Fin 234)
    (hv : bulkNearSegmentVertex i = 4) : BulkNearCoreEscapeCheck i := by
  apply bulkNearCoreFastCheck_sound
  exact bulkNearVertex_cases_4 BulkNearCoreFastCheck
    bulkNearCoreFastBatch_4_0.1
    bulkNearCoreFastBatch_4_0.2.1
    bulkNearCoreFastBatch_4_0.2.2.1
    bulkNearCoreFastBatch_4_0.2.2.2.1
    bulkNearCoreFastBatch_4_0.2.2.2.2.1
    bulkNearCoreFastBatch_4_0.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_0.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_0.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_0.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_0.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_0.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_0.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_0.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_0.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoreFastBatch_4_1.1
    bulkNearCoreFastBatch_4_1.2.1
    bulkNearCoreFastBatch_4_1.2.2.1
    bulkNearCoreFastBatch_4_1.2.2.2.1
    bulkNearCoreFastBatch_4_1.2.2.2.2.1
    bulkNearCoreFastBatch_4_1.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_1.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_1.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_1.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_1.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_1.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_1.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_1.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_1.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoreFastBatch_4_2.1
    bulkNearCoreFastBatch_4_2.2.1
    bulkNearCoreFastBatch_4_2.2.2.1
    bulkNearCoreFastBatch_4_2.2.2.2.1
    bulkNearCoreFastBatch_4_2.2.2.2.2.1
    bulkNearCoreFastBatch_4_2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoreFastBatch_4_3.1
    bulkNearCoreFastBatch_4_3.2.1
    bulkNearCoreFastBatch_4_3.2.2.1
    bulkNearCoreFastBatch_4_3.2.2.2.1
    bulkNearCoreFastBatch_4_3.2.2.2.2.1
    bulkNearCoreFastBatch_4_3.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_3.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_3.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_3.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_3.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_3.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_3.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoreFastBatch_4_3.2.2.2.2.2.2.2.2.2.2.2.2
    i hv

end ProteinFolding.Tetrahedral

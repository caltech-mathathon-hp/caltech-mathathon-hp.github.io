import ProteinFolding.Tetrahedral.BulkNearVertexEliminators
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch0
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch1
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch2
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch3
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch4
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch5
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch6
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch7
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch8
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch9
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch10
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch11
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch12
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch13
import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsBatch14

/-! Opaque index elimination assembles the independently checked literal statistics. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem bulkNearCoordinateStatistics_reference (i : Fin 234) :
    BulkNearCoordinateStatisticsCheck i :=
  bulkNearAllIndices_cases BulkNearCoordinateStatisticsCheck
    bulkNearCoordinateStatisticsBatch_0.1
    bulkNearCoordinateStatisticsBatch_0.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_1.1
    bulkNearCoordinateStatisticsBatch_1.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_2.1
    bulkNearCoordinateStatisticsBatch_2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_3.1
    bulkNearCoordinateStatisticsBatch_3.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_4.1
    bulkNearCoordinateStatisticsBatch_4.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_5.1
    bulkNearCoordinateStatisticsBatch_5.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_6.1
    bulkNearCoordinateStatisticsBatch_6.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_7.1
    bulkNearCoordinateStatisticsBatch_7.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_8.1
    bulkNearCoordinateStatisticsBatch_8.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_9.1
    bulkNearCoordinateStatisticsBatch_9.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_10.1
    bulkNearCoordinateStatisticsBatch_10.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_11.1
    bulkNearCoordinateStatisticsBatch_11.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_12.1
    bulkNearCoordinateStatisticsBatch_12.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_13.1
    bulkNearCoordinateStatisticsBatch_13.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_13.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    bulkNearCoordinateStatisticsBatch_14.1
    bulkNearCoordinateStatisticsBatch_14.2.1
    bulkNearCoordinateStatisticsBatch_14.2.2.1
    bulkNearCoordinateStatisticsBatch_14.2.2.2.1
    bulkNearCoordinateStatisticsBatch_14.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_14.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_14.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_14.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_14.2.2.2.2.2.2.2.2.1
    bulkNearCoordinateStatisticsBatch_14.2.2.2.2.2.2.2.2.2
    i

theorem bulkNearReferenceXhat_coordinates (i : Fin 234) :
    bulkNearReferenceXhat i = bulkNearCoordinateMin i + bulkNearCoordinateMax i :=
  bulkNearCoordinateStatisticsCheck_sound i (bulkNearCoordinateStatistics_reference i)

end ProteinFolding.Tetrahedral

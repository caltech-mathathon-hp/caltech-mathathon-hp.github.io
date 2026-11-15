import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsSpec

/-! Closed coordinate-statistic certificates, with no quantified index normalization. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem bulkNearCoordinateLiteral_0 :
    BulkNearCoordinateStatisticsCheck (0 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_1 :
    BulkNearCoordinateStatisticsCheck (1 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_2 :
    BulkNearCoordinateStatisticsCheck (2 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_3 :
    BulkNearCoordinateStatisticsCheck (3 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_4 :
    BulkNearCoordinateStatisticsCheck (4 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_5 :
    BulkNearCoordinateStatisticsCheck (5 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_6 :
    BulkNearCoordinateStatisticsCheck (6 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_7 :
    BulkNearCoordinateStatisticsCheck (7 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_8 :
    BulkNearCoordinateStatisticsCheck (8 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_9 :
    BulkNearCoordinateStatisticsCheck (9 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_10 :
    BulkNearCoordinateStatisticsCheck (10 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_11 :
    BulkNearCoordinateStatisticsCheck (11 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_12 :
    BulkNearCoordinateStatisticsCheck (12 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_13 :
    BulkNearCoordinateStatisticsCheck (13 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_14 :
    BulkNearCoordinateStatisticsCheck (14 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_15 :
    BulkNearCoordinateStatisticsCheck (15 : Fin 234) := by
  decide +kernel

theorem bulkNearCoordinateStatisticsBatch_0 :
    BulkNearCoordinateStatisticsCheck (0 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (1 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (2 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (3 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (4 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (5 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (6 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (7 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (8 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (9 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (10 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (11 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (12 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (13 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (14 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (15 : Fin 234) := by
  exact ⟨bulkNearCoordinateLiteral_0, bulkNearCoordinateLiteral_1, bulkNearCoordinateLiteral_2, bulkNearCoordinateLiteral_3, bulkNearCoordinateLiteral_4, bulkNearCoordinateLiteral_5, bulkNearCoordinateLiteral_6, bulkNearCoordinateLiteral_7, bulkNearCoordinateLiteral_8, bulkNearCoordinateLiteral_9, bulkNearCoordinateLiteral_10, bulkNearCoordinateLiteral_11, bulkNearCoordinateLiteral_12, bulkNearCoordinateLiteral_13, bulkNearCoordinateLiteral_14, bulkNearCoordinateLiteral_15⟩

end ProteinFolding.Tetrahedral

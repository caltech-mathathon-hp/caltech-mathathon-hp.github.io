import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsSpec

/-! Closed coordinate-statistic certificates, with no quantified index normalization. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem bulkNearCoordinateLiteral_224 :
    BulkNearCoordinateStatisticsCheck (224 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_225 :
    BulkNearCoordinateStatisticsCheck (225 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_226 :
    BulkNearCoordinateStatisticsCheck (226 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_227 :
    BulkNearCoordinateStatisticsCheck (227 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_228 :
    BulkNearCoordinateStatisticsCheck (228 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_229 :
    BulkNearCoordinateStatisticsCheck (229 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_230 :
    BulkNearCoordinateStatisticsCheck (230 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_231 :
    BulkNearCoordinateStatisticsCheck (231 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_232 :
    BulkNearCoordinateStatisticsCheck (232 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_233 :
    BulkNearCoordinateStatisticsCheck (233 : Fin 234) := by
  decide +kernel

theorem bulkNearCoordinateStatisticsBatch_14 :
    BulkNearCoordinateStatisticsCheck (224 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (225 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (226 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (227 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (228 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (229 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (230 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (231 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (232 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (233 : Fin 234) := by
  exact ⟨bulkNearCoordinateLiteral_224, bulkNearCoordinateLiteral_225, bulkNearCoordinateLiteral_226, bulkNearCoordinateLiteral_227, bulkNearCoordinateLiteral_228, bulkNearCoordinateLiteral_229, bulkNearCoordinateLiteral_230, bulkNearCoordinateLiteral_231, bulkNearCoordinateLiteral_232, bulkNearCoordinateLiteral_233⟩

end ProteinFolding.Tetrahedral

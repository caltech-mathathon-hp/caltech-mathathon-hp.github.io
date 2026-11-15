import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsSpec

/-! Closed coordinate-statistic certificates, with no quantified index normalization. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem bulkNearCoordinateLiteral_32 :
    BulkNearCoordinateStatisticsCheck (32 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_33 :
    BulkNearCoordinateStatisticsCheck (33 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_34 :
    BulkNearCoordinateStatisticsCheck (34 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_35 :
    BulkNearCoordinateStatisticsCheck (35 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_36 :
    BulkNearCoordinateStatisticsCheck (36 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_37 :
    BulkNearCoordinateStatisticsCheck (37 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_38 :
    BulkNearCoordinateStatisticsCheck (38 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_39 :
    BulkNearCoordinateStatisticsCheck (39 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_40 :
    BulkNearCoordinateStatisticsCheck (40 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_41 :
    BulkNearCoordinateStatisticsCheck (41 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_42 :
    BulkNearCoordinateStatisticsCheck (42 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_43 :
    BulkNearCoordinateStatisticsCheck (43 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_44 :
    BulkNearCoordinateStatisticsCheck (44 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_45 :
    BulkNearCoordinateStatisticsCheck (45 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_46 :
    BulkNearCoordinateStatisticsCheck (46 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_47 :
    BulkNearCoordinateStatisticsCheck (47 : Fin 234) := by
  decide +kernel

theorem bulkNearCoordinateStatisticsBatch_2 :
    BulkNearCoordinateStatisticsCheck (32 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (33 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (34 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (35 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (36 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (37 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (38 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (39 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (40 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (41 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (42 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (43 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (44 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (45 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (46 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (47 : Fin 234) := by
  exact ⟨bulkNearCoordinateLiteral_32, bulkNearCoordinateLiteral_33, bulkNearCoordinateLiteral_34, bulkNearCoordinateLiteral_35, bulkNearCoordinateLiteral_36, bulkNearCoordinateLiteral_37, bulkNearCoordinateLiteral_38, bulkNearCoordinateLiteral_39, bulkNearCoordinateLiteral_40, bulkNearCoordinateLiteral_41, bulkNearCoordinateLiteral_42, bulkNearCoordinateLiteral_43, bulkNearCoordinateLiteral_44, bulkNearCoordinateLiteral_45, bulkNearCoordinateLiteral_46, bulkNearCoordinateLiteral_47⟩

end ProteinFolding.Tetrahedral

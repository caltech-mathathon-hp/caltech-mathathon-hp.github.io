import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsSpec

/-! Closed coordinate-statistic certificates, with no quantified index normalization. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem bulkNearCoordinateLiteral_64 :
    BulkNearCoordinateStatisticsCheck (64 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_65 :
    BulkNearCoordinateStatisticsCheck (65 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_66 :
    BulkNearCoordinateStatisticsCheck (66 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_67 :
    BulkNearCoordinateStatisticsCheck (67 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_68 :
    BulkNearCoordinateStatisticsCheck (68 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_69 :
    BulkNearCoordinateStatisticsCheck (69 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_70 :
    BulkNearCoordinateStatisticsCheck (70 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_71 :
    BulkNearCoordinateStatisticsCheck (71 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_72 :
    BulkNearCoordinateStatisticsCheck (72 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_73 :
    BulkNearCoordinateStatisticsCheck (73 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_74 :
    BulkNearCoordinateStatisticsCheck (74 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_75 :
    BulkNearCoordinateStatisticsCheck (75 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_76 :
    BulkNearCoordinateStatisticsCheck (76 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_77 :
    BulkNearCoordinateStatisticsCheck (77 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_78 :
    BulkNearCoordinateStatisticsCheck (78 : Fin 234) := by
  decide +kernel

private theorem bulkNearCoordinateLiteral_79 :
    BulkNearCoordinateStatisticsCheck (79 : Fin 234) := by
  decide +kernel

theorem bulkNearCoordinateStatisticsBatch_4 :
    BulkNearCoordinateStatisticsCheck (64 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (65 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (66 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (67 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (68 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (69 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (70 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (71 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (72 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (73 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (74 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (75 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (76 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (77 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (78 : Fin 234) ∧
    BulkNearCoordinateStatisticsCheck (79 : Fin 234) := by
  exact ⟨bulkNearCoordinateLiteral_64, bulkNearCoordinateLiteral_65, bulkNearCoordinateLiteral_66, bulkNearCoordinateLiteral_67, bulkNearCoordinateLiteral_68, bulkNearCoordinateLiteral_69, bulkNearCoordinateLiteral_70, bulkNearCoordinateLiteral_71, bulkNearCoordinateLiteral_72, bulkNearCoordinateLiteral_73, bulkNearCoordinateLiteral_74, bulkNearCoordinateLiteral_75, bulkNearCoordinateLiteral_76, bulkNearCoordinateLiteral_77, bulkNearCoordinateLiteral_78, bulkNearCoordinateLiteral_79⟩

end ProteinFolding.Tetrahedral

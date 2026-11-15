import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_1_14 :
    BulkNearSupportQuickCheck (14 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_15 :
    BulkNearSupportQuickCheck (15 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_16 :
    BulkNearSupportQuickCheck (16 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_17 :
    BulkNearSupportQuickCheck (17 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_18 :
    BulkNearSupportQuickCheck (18 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_19 :
    BulkNearSupportQuickCheck (19 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_20 :
    BulkNearSupportQuickCheck (20 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_21 :
    BulkNearSupportQuickCheck (21 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_22 :
    BulkNearSupportQuickCheck (22 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_23 :
    BulkNearSupportQuickCheck (23 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_24 :
    BulkNearSupportQuickCheck (24 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_25 :
    BulkNearSupportQuickCheck (25 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_26 :
    BulkNearSupportQuickCheck (26 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_27 :
    BulkNearSupportQuickCheck (27 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_1_0 :
    BulkNearSupportQuickCheck (14 : Fin 234) ∧
    BulkNearSupportQuickCheck (15 : Fin 234) ∧
    BulkNearSupportQuickCheck (16 : Fin 234) ∧
    BulkNearSupportQuickCheck (17 : Fin 234) ∧
    BulkNearSupportQuickCheck (18 : Fin 234) ∧
    BulkNearSupportQuickCheck (19 : Fin 234) ∧
    BulkNearSupportQuickCheck (20 : Fin 234) ∧
    BulkNearSupportQuickCheck (21 : Fin 234) ∧
    BulkNearSupportQuickCheck (22 : Fin 234) ∧
    BulkNearSupportQuickCheck (23 : Fin 234) ∧
    BulkNearSupportQuickCheck (24 : Fin 234) ∧
    BulkNearSupportQuickCheck (25 : Fin 234) ∧
    BulkNearSupportQuickCheck (26 : Fin 234) ∧
    BulkNearSupportQuickCheck (27 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_1_14, bulkNearSupportLiteral_1_15, bulkNearSupportLiteral_1_16, bulkNearSupportLiteral_1_17, bulkNearSupportLiteral_1_18, bulkNearSupportLiteral_1_19, bulkNearSupportLiteral_1_20, bulkNearSupportLiteral_1_21, bulkNearSupportLiteral_1_22, bulkNearSupportLiteral_1_23, bulkNearSupportLiteral_1_24, bulkNearSupportLiteral_1_25, bulkNearSupportLiteral_1_26, bulkNearSupportLiteral_1_27⟩

end ProteinFolding.Tetrahedral

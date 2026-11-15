import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_1_28 :
    BulkNearSupportQuickCheck (28 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_29 :
    BulkNearSupportQuickCheck (29 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_30 :
    BulkNearSupportQuickCheck (30 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_31 :
    BulkNearSupportQuickCheck (31 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_32 :
    BulkNearSupportQuickCheck (32 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_33 :
    BulkNearSupportQuickCheck (33 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_34 :
    BulkNearSupportQuickCheck (34 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_35 :
    BulkNearSupportQuickCheck (35 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_36 :
    BulkNearSupportQuickCheck (36 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_37 :
    BulkNearSupportQuickCheck (37 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_38 :
    BulkNearSupportQuickCheck (38 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_39 :
    BulkNearSupportQuickCheck (39 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_40 :
    BulkNearSupportQuickCheck (40 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_41 :
    BulkNearSupportQuickCheck (41 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_1_1 :
    BulkNearSupportQuickCheck (28 : Fin 234) ∧
    BulkNearSupportQuickCheck (29 : Fin 234) ∧
    BulkNearSupportQuickCheck (30 : Fin 234) ∧
    BulkNearSupportQuickCheck (31 : Fin 234) ∧
    BulkNearSupportQuickCheck (32 : Fin 234) ∧
    BulkNearSupportQuickCheck (33 : Fin 234) ∧
    BulkNearSupportQuickCheck (34 : Fin 234) ∧
    BulkNearSupportQuickCheck (35 : Fin 234) ∧
    BulkNearSupportQuickCheck (36 : Fin 234) ∧
    BulkNearSupportQuickCheck (37 : Fin 234) ∧
    BulkNearSupportQuickCheck (38 : Fin 234) ∧
    BulkNearSupportQuickCheck (39 : Fin 234) ∧
    BulkNearSupportQuickCheck (40 : Fin 234) ∧
    BulkNearSupportQuickCheck (41 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_1_28, bulkNearSupportLiteral_1_29, bulkNearSupportLiteral_1_30, bulkNearSupportLiteral_1_31, bulkNearSupportLiteral_1_32, bulkNearSupportLiteral_1_33, bulkNearSupportLiteral_1_34, bulkNearSupportLiteral_1_35, bulkNearSupportLiteral_1_36, bulkNearSupportLiteral_1_37, bulkNearSupportLiteral_1_38, bulkNearSupportLiteral_1_39, bulkNearSupportLiteral_1_40, bulkNearSupportLiteral_1_41⟩

end ProteinFolding.Tetrahedral

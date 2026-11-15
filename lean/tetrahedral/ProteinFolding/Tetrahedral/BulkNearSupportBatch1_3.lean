import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_1_56 :
    BulkNearSupportQuickCheck (56 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_57 :
    BulkNearSupportQuickCheck (57 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_58 :
    BulkNearSupportQuickCheck (58 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_59 :
    BulkNearSupportQuickCheck (59 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_60 :
    BulkNearSupportQuickCheck (60 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_61 :
    BulkNearSupportQuickCheck (61 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_62 :
    BulkNearSupportQuickCheck (62 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_63 :
    BulkNearSupportQuickCheck (63 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_64 :
    BulkNearSupportQuickCheck (64 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_65 :
    BulkNearSupportQuickCheck (65 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_66 :
    BulkNearSupportQuickCheck (66 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_67 :
    BulkNearSupportQuickCheck (67 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_68 :
    BulkNearSupportQuickCheck (68 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_1_3 :
    BulkNearSupportQuickCheck (56 : Fin 234) ∧
    BulkNearSupportQuickCheck (57 : Fin 234) ∧
    BulkNearSupportQuickCheck (58 : Fin 234) ∧
    BulkNearSupportQuickCheck (59 : Fin 234) ∧
    BulkNearSupportQuickCheck (60 : Fin 234) ∧
    BulkNearSupportQuickCheck (61 : Fin 234) ∧
    BulkNearSupportQuickCheck (62 : Fin 234) ∧
    BulkNearSupportQuickCheck (63 : Fin 234) ∧
    BulkNearSupportQuickCheck (64 : Fin 234) ∧
    BulkNearSupportQuickCheck (65 : Fin 234) ∧
    BulkNearSupportQuickCheck (66 : Fin 234) ∧
    BulkNearSupportQuickCheck (67 : Fin 234) ∧
    BulkNearSupportQuickCheck (68 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_1_56, bulkNearSupportLiteral_1_57, bulkNearSupportLiteral_1_58, bulkNearSupportLiteral_1_59, bulkNearSupportLiteral_1_60, bulkNearSupportLiteral_1_61, bulkNearSupportLiteral_1_62, bulkNearSupportLiteral_1_63, bulkNearSupportLiteral_1_64, bulkNearSupportLiteral_1_65, bulkNearSupportLiteral_1_66, bulkNearSupportLiteral_1_67, bulkNearSupportLiteral_1_68⟩

end ProteinFolding.Tetrahedral

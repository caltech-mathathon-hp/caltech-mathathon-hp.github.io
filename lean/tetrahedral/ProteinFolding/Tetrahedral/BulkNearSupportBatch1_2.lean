import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_1_42 :
    BulkNearSupportQuickCheck (42 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_43 :
    BulkNearSupportQuickCheck (43 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_44 :
    BulkNearSupportQuickCheck (44 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_45 :
    BulkNearSupportQuickCheck (45 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_46 :
    BulkNearSupportQuickCheck (46 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_47 :
    BulkNearSupportQuickCheck (47 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_48 :
    BulkNearSupportQuickCheck (48 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_49 :
    BulkNearSupportQuickCheck (49 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_50 :
    BulkNearSupportQuickCheck (50 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_51 :
    BulkNearSupportQuickCheck (51 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_52 :
    BulkNearSupportQuickCheck (52 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_53 :
    BulkNearSupportQuickCheck (53 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_54 :
    BulkNearSupportQuickCheck (54 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_1_55 :
    BulkNearSupportQuickCheck (55 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_1_2 :
    BulkNearSupportQuickCheck (42 : Fin 234) ∧
    BulkNearSupportQuickCheck (43 : Fin 234) ∧
    BulkNearSupportQuickCheck (44 : Fin 234) ∧
    BulkNearSupportQuickCheck (45 : Fin 234) ∧
    BulkNearSupportQuickCheck (46 : Fin 234) ∧
    BulkNearSupportQuickCheck (47 : Fin 234) ∧
    BulkNearSupportQuickCheck (48 : Fin 234) ∧
    BulkNearSupportQuickCheck (49 : Fin 234) ∧
    BulkNearSupportQuickCheck (50 : Fin 234) ∧
    BulkNearSupportQuickCheck (51 : Fin 234) ∧
    BulkNearSupportQuickCheck (52 : Fin 234) ∧
    BulkNearSupportQuickCheck (53 : Fin 234) ∧
    BulkNearSupportQuickCheck (54 : Fin 234) ∧
    BulkNearSupportQuickCheck (55 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_1_42, bulkNearSupportLiteral_1_43, bulkNearSupportLiteral_1_44, bulkNearSupportLiteral_1_45, bulkNearSupportLiteral_1_46, bulkNearSupportLiteral_1_47, bulkNearSupportLiteral_1_48, bulkNearSupportLiteral_1_49, bulkNearSupportLiteral_1_50, bulkNearSupportLiteral_1_51, bulkNearSupportLiteral_1_52, bulkNearSupportLiteral_1_53, bulkNearSupportLiteral_1_54, bulkNearSupportLiteral_1_55⟩

end ProteinFolding.Tetrahedral

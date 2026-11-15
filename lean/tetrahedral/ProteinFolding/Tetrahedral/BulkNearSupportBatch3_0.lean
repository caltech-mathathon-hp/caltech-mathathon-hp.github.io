import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_3_117 :
    BulkNearSupportQuickCheck (117 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_118 :
    BulkNearSupportQuickCheck (118 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_119 :
    BulkNearSupportQuickCheck (119 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_120 :
    BulkNearSupportQuickCheck (120 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_121 :
    BulkNearSupportQuickCheck (121 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_122 :
    BulkNearSupportQuickCheck (122 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_123 :
    BulkNearSupportQuickCheck (123 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_124 :
    BulkNearSupportQuickCheck (124 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_125 :
    BulkNearSupportQuickCheck (125 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_126 :
    BulkNearSupportQuickCheck (126 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_127 :
    BulkNearSupportQuickCheck (127 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_128 :
    BulkNearSupportQuickCheck (128 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_129 :
    BulkNearSupportQuickCheck (129 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_130 :
    BulkNearSupportQuickCheck (130 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_131 :
    BulkNearSupportQuickCheck (131 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_132 :
    BulkNearSupportQuickCheck (132 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_3_0 :
    BulkNearSupportQuickCheck (117 : Fin 234) ∧
    BulkNearSupportQuickCheck (118 : Fin 234) ∧
    BulkNearSupportQuickCheck (119 : Fin 234) ∧
    BulkNearSupportQuickCheck (120 : Fin 234) ∧
    BulkNearSupportQuickCheck (121 : Fin 234) ∧
    BulkNearSupportQuickCheck (122 : Fin 234) ∧
    BulkNearSupportQuickCheck (123 : Fin 234) ∧
    BulkNearSupportQuickCheck (124 : Fin 234) ∧
    BulkNearSupportQuickCheck (125 : Fin 234) ∧
    BulkNearSupportQuickCheck (126 : Fin 234) ∧
    BulkNearSupportQuickCheck (127 : Fin 234) ∧
    BulkNearSupportQuickCheck (128 : Fin 234) ∧
    BulkNearSupportQuickCheck (129 : Fin 234) ∧
    BulkNearSupportQuickCheck (130 : Fin 234) ∧
    BulkNearSupportQuickCheck (131 : Fin 234) ∧
    BulkNearSupportQuickCheck (132 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_3_117, bulkNearSupportLiteral_3_118, bulkNearSupportLiteral_3_119, bulkNearSupportLiteral_3_120, bulkNearSupportLiteral_3_121, bulkNearSupportLiteral_3_122, bulkNearSupportLiteral_3_123, bulkNearSupportLiteral_3_124, bulkNearSupportLiteral_3_125, bulkNearSupportLiteral_3_126, bulkNearSupportLiteral_3_127, bulkNearSupportLiteral_3_128, bulkNearSupportLiteral_3_129, bulkNearSupportLiteral_3_130, bulkNearSupportLiteral_3_131, bulkNearSupportLiteral_3_132⟩

end ProteinFolding.Tetrahedral

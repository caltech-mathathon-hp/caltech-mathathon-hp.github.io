import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_3_133 :
    BulkNearSupportQuickCheck (133 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_134 :
    BulkNearSupportQuickCheck (134 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_135 :
    BulkNearSupportQuickCheck (135 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_136 :
    BulkNearSupportQuickCheck (136 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_137 :
    BulkNearSupportQuickCheck (137 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_138 :
    BulkNearSupportQuickCheck (138 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_139 :
    BulkNearSupportQuickCheck (139 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_140 :
    BulkNearSupportQuickCheck (140 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_141 :
    BulkNearSupportQuickCheck (141 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_142 :
    BulkNearSupportQuickCheck (142 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_143 :
    BulkNearSupportQuickCheck (143 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_144 :
    BulkNearSupportQuickCheck (144 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_145 :
    BulkNearSupportQuickCheck (145 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_146 :
    BulkNearSupportQuickCheck (146 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_147 :
    BulkNearSupportQuickCheck (147 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_148 :
    BulkNearSupportQuickCheck (148 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_3_1 :
    BulkNearSupportQuickCheck (133 : Fin 234) ∧
    BulkNearSupportQuickCheck (134 : Fin 234) ∧
    BulkNearSupportQuickCheck (135 : Fin 234) ∧
    BulkNearSupportQuickCheck (136 : Fin 234) ∧
    BulkNearSupportQuickCheck (137 : Fin 234) ∧
    BulkNearSupportQuickCheck (138 : Fin 234) ∧
    BulkNearSupportQuickCheck (139 : Fin 234) ∧
    BulkNearSupportQuickCheck (140 : Fin 234) ∧
    BulkNearSupportQuickCheck (141 : Fin 234) ∧
    BulkNearSupportQuickCheck (142 : Fin 234) ∧
    BulkNearSupportQuickCheck (143 : Fin 234) ∧
    BulkNearSupportQuickCheck (144 : Fin 234) ∧
    BulkNearSupportQuickCheck (145 : Fin 234) ∧
    BulkNearSupportQuickCheck (146 : Fin 234) ∧
    BulkNearSupportQuickCheck (147 : Fin 234) ∧
    BulkNearSupportQuickCheck (148 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_3_133, bulkNearSupportLiteral_3_134, bulkNearSupportLiteral_3_135, bulkNearSupportLiteral_3_136, bulkNearSupportLiteral_3_137, bulkNearSupportLiteral_3_138, bulkNearSupportLiteral_3_139, bulkNearSupportLiteral_3_140, bulkNearSupportLiteral_3_141, bulkNearSupportLiteral_3_142, bulkNearSupportLiteral_3_143, bulkNearSupportLiteral_3_144, bulkNearSupportLiteral_3_145, bulkNearSupportLiteral_3_146, bulkNearSupportLiteral_3_147, bulkNearSupportLiteral_3_148⟩

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_4_165 :
    BulkNearSupportQuickCheck (165 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_166 :
    BulkNearSupportQuickCheck (166 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_167 :
    BulkNearSupportQuickCheck (167 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_168 :
    BulkNearSupportQuickCheck (168 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_169 :
    BulkNearSupportQuickCheck (169 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_170 :
    BulkNearSupportQuickCheck (170 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_171 :
    BulkNearSupportQuickCheck (171 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_172 :
    BulkNearSupportQuickCheck (172 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_173 :
    BulkNearSupportQuickCheck (173 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_174 :
    BulkNearSupportQuickCheck (174 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_175 :
    BulkNearSupportQuickCheck (175 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_176 :
    BulkNearSupportQuickCheck (176 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_177 :
    BulkNearSupportQuickCheck (177 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_178 :
    BulkNearSupportQuickCheck (178 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_4_0 :
    BulkNearSupportQuickCheck (165 : Fin 234) ∧
    BulkNearSupportQuickCheck (166 : Fin 234) ∧
    BulkNearSupportQuickCheck (167 : Fin 234) ∧
    BulkNearSupportQuickCheck (168 : Fin 234) ∧
    BulkNearSupportQuickCheck (169 : Fin 234) ∧
    BulkNearSupportQuickCheck (170 : Fin 234) ∧
    BulkNearSupportQuickCheck (171 : Fin 234) ∧
    BulkNearSupportQuickCheck (172 : Fin 234) ∧
    BulkNearSupportQuickCheck (173 : Fin 234) ∧
    BulkNearSupportQuickCheck (174 : Fin 234) ∧
    BulkNearSupportQuickCheck (175 : Fin 234) ∧
    BulkNearSupportQuickCheck (176 : Fin 234) ∧
    BulkNearSupportQuickCheck (177 : Fin 234) ∧
    BulkNearSupportQuickCheck (178 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_4_165, bulkNearSupportLiteral_4_166, bulkNearSupportLiteral_4_167, bulkNearSupportLiteral_4_168, bulkNearSupportLiteral_4_169, bulkNearSupportLiteral_4_170, bulkNearSupportLiteral_4_171, bulkNearSupportLiteral_4_172, bulkNearSupportLiteral_4_173, bulkNearSupportLiteral_4_174, bulkNearSupportLiteral_4_175, bulkNearSupportLiteral_4_176, bulkNearSupportLiteral_4_177, bulkNearSupportLiteral_4_178⟩

end ProteinFolding.Tetrahedral

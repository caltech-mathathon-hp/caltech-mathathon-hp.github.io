import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_4_179 :
    BulkNearSupportQuickCheck (179 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_180 :
    BulkNearSupportQuickCheck (180 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_181 :
    BulkNearSupportQuickCheck (181 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_182 :
    BulkNearSupportQuickCheck (182 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_183 :
    BulkNearSupportQuickCheck (183 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_184 :
    BulkNearSupportQuickCheck (184 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_185 :
    BulkNearSupportQuickCheck (185 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_186 :
    BulkNearSupportQuickCheck (186 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_187 :
    BulkNearSupportQuickCheck (187 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_188 :
    BulkNearSupportQuickCheck (188 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_189 :
    BulkNearSupportQuickCheck (189 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_190 :
    BulkNearSupportQuickCheck (190 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_191 :
    BulkNearSupportQuickCheck (191 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_192 :
    BulkNearSupportQuickCheck (192 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_4_1 :
    BulkNearSupportQuickCheck (179 : Fin 234) ∧
    BulkNearSupportQuickCheck (180 : Fin 234) ∧
    BulkNearSupportQuickCheck (181 : Fin 234) ∧
    BulkNearSupportQuickCheck (182 : Fin 234) ∧
    BulkNearSupportQuickCheck (183 : Fin 234) ∧
    BulkNearSupportQuickCheck (184 : Fin 234) ∧
    BulkNearSupportQuickCheck (185 : Fin 234) ∧
    BulkNearSupportQuickCheck (186 : Fin 234) ∧
    BulkNearSupportQuickCheck (187 : Fin 234) ∧
    BulkNearSupportQuickCheck (188 : Fin 234) ∧
    BulkNearSupportQuickCheck (189 : Fin 234) ∧
    BulkNearSupportQuickCheck (190 : Fin 234) ∧
    BulkNearSupportQuickCheck (191 : Fin 234) ∧
    BulkNearSupportQuickCheck (192 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_4_179, bulkNearSupportLiteral_4_180, bulkNearSupportLiteral_4_181, bulkNearSupportLiteral_4_182, bulkNearSupportLiteral_4_183, bulkNearSupportLiteral_4_184, bulkNearSupportLiteral_4_185, bulkNearSupportLiteral_4_186, bulkNearSupportLiteral_4_187, bulkNearSupportLiteral_4_188, bulkNearSupportLiteral_4_189, bulkNearSupportLiteral_4_190, bulkNearSupportLiteral_4_191, bulkNearSupportLiteral_4_192⟩

end ProteinFolding.Tetrahedral

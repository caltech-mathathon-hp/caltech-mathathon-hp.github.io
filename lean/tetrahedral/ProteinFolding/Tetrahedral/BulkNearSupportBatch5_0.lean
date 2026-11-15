import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_5_220 :
    BulkNearSupportQuickCheck (220 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_221 :
    BulkNearSupportQuickCheck (221 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_222 :
    BulkNearSupportQuickCheck (222 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_223 :
    BulkNearSupportQuickCheck (223 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_224 :
    BulkNearSupportQuickCheck (224 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_225 :
    BulkNearSupportQuickCheck (225 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_226 :
    BulkNearSupportQuickCheck (226 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_227 :
    BulkNearSupportQuickCheck (227 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_228 :
    BulkNearSupportQuickCheck (228 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_229 :
    BulkNearSupportQuickCheck (229 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_230 :
    BulkNearSupportQuickCheck (230 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_231 :
    BulkNearSupportQuickCheck (231 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_232 :
    BulkNearSupportQuickCheck (232 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_5_233 :
    BulkNearSupportQuickCheck (233 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_5_0 :
    BulkNearSupportQuickCheck (220 : Fin 234) ∧
    BulkNearSupportQuickCheck (221 : Fin 234) ∧
    BulkNearSupportQuickCheck (222 : Fin 234) ∧
    BulkNearSupportQuickCheck (223 : Fin 234) ∧
    BulkNearSupportQuickCheck (224 : Fin 234) ∧
    BulkNearSupportQuickCheck (225 : Fin 234) ∧
    BulkNearSupportQuickCheck (226 : Fin 234) ∧
    BulkNearSupportQuickCheck (227 : Fin 234) ∧
    BulkNearSupportQuickCheck (228 : Fin 234) ∧
    BulkNearSupportQuickCheck (229 : Fin 234) ∧
    BulkNearSupportQuickCheck (230 : Fin 234) ∧
    BulkNearSupportQuickCheck (231 : Fin 234) ∧
    BulkNearSupportQuickCheck (232 : Fin 234) ∧
    BulkNearSupportQuickCheck (233 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_5_220, bulkNearSupportLiteral_5_221, bulkNearSupportLiteral_5_222, bulkNearSupportLiteral_5_223, bulkNearSupportLiteral_5_224, bulkNearSupportLiteral_5_225, bulkNearSupportLiteral_5_226, bulkNearSupportLiteral_5_227, bulkNearSupportLiteral_5_228, bulkNearSupportLiteral_5_229, bulkNearSupportLiteral_5_230, bulkNearSupportLiteral_5_231, bulkNearSupportLiteral_5_232, bulkNearSupportLiteral_5_233⟩

end ProteinFolding.Tetrahedral

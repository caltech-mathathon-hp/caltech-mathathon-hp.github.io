import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_4_207 :
    BulkNearSupportQuickCheck (207 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_208 :
    BulkNearSupportQuickCheck (208 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_209 :
    BulkNearSupportQuickCheck (209 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_210 :
    BulkNearSupportQuickCheck (210 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_211 :
    BulkNearSupportQuickCheck (211 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_212 :
    BulkNearSupportQuickCheck (212 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_213 :
    BulkNearSupportQuickCheck (213 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_214 :
    BulkNearSupportQuickCheck (214 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_215 :
    BulkNearSupportQuickCheck (215 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_216 :
    BulkNearSupportQuickCheck (216 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_217 :
    BulkNearSupportQuickCheck (217 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_218 :
    BulkNearSupportQuickCheck (218 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_219 :
    BulkNearSupportQuickCheck (219 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_4_3 :
    BulkNearSupportQuickCheck (207 : Fin 234) ∧
    BulkNearSupportQuickCheck (208 : Fin 234) ∧
    BulkNearSupportQuickCheck (209 : Fin 234) ∧
    BulkNearSupportQuickCheck (210 : Fin 234) ∧
    BulkNearSupportQuickCheck (211 : Fin 234) ∧
    BulkNearSupportQuickCheck (212 : Fin 234) ∧
    BulkNearSupportQuickCheck (213 : Fin 234) ∧
    BulkNearSupportQuickCheck (214 : Fin 234) ∧
    BulkNearSupportQuickCheck (215 : Fin 234) ∧
    BulkNearSupportQuickCheck (216 : Fin 234) ∧
    BulkNearSupportQuickCheck (217 : Fin 234) ∧
    BulkNearSupportQuickCheck (218 : Fin 234) ∧
    BulkNearSupportQuickCheck (219 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_4_207, bulkNearSupportLiteral_4_208, bulkNearSupportLiteral_4_209, bulkNearSupportLiteral_4_210, bulkNearSupportLiteral_4_211, bulkNearSupportLiteral_4_212, bulkNearSupportLiteral_4_213, bulkNearSupportLiteral_4_214, bulkNearSupportLiteral_4_215, bulkNearSupportLiteral_4_216, bulkNearSupportLiteral_4_217, bulkNearSupportLiteral_4_218, bulkNearSupportLiteral_4_219⟩

end ProteinFolding.Tetrahedral

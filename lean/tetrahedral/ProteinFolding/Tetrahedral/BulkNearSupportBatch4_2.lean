import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_4_193 :
    BulkNearSupportQuickCheck (193 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_194 :
    BulkNearSupportQuickCheck (194 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_195 :
    BulkNearSupportQuickCheck (195 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_196 :
    BulkNearSupportQuickCheck (196 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_197 :
    BulkNearSupportQuickCheck (197 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_198 :
    BulkNearSupportQuickCheck (198 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_199 :
    BulkNearSupportQuickCheck (199 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_200 :
    BulkNearSupportQuickCheck (200 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_201 :
    BulkNearSupportQuickCheck (201 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_202 :
    BulkNearSupportQuickCheck (202 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_203 :
    BulkNearSupportQuickCheck (203 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_204 :
    BulkNearSupportQuickCheck (204 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_205 :
    BulkNearSupportQuickCheck (205 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_4_206 :
    BulkNearSupportQuickCheck (206 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_4_2 :
    BulkNearSupportQuickCheck (193 : Fin 234) ∧
    BulkNearSupportQuickCheck (194 : Fin 234) ∧
    BulkNearSupportQuickCheck (195 : Fin 234) ∧
    BulkNearSupportQuickCheck (196 : Fin 234) ∧
    BulkNearSupportQuickCheck (197 : Fin 234) ∧
    BulkNearSupportQuickCheck (198 : Fin 234) ∧
    BulkNearSupportQuickCheck (199 : Fin 234) ∧
    BulkNearSupportQuickCheck (200 : Fin 234) ∧
    BulkNearSupportQuickCheck (201 : Fin 234) ∧
    BulkNearSupportQuickCheck (202 : Fin 234) ∧
    BulkNearSupportQuickCheck (203 : Fin 234) ∧
    BulkNearSupportQuickCheck (204 : Fin 234) ∧
    BulkNearSupportQuickCheck (205 : Fin 234) ∧
    BulkNearSupportQuickCheck (206 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_4_193, bulkNearSupportLiteral_4_194, bulkNearSupportLiteral_4_195, bulkNearSupportLiteral_4_196, bulkNearSupportLiteral_4_197, bulkNearSupportLiteral_4_198, bulkNearSupportLiteral_4_199, bulkNearSupportLiteral_4_200, bulkNearSupportLiteral_4_201, bulkNearSupportLiteral_4_202, bulkNearSupportLiteral_4_203, bulkNearSupportLiteral_4_204, bulkNearSupportLiteral_4_205, bulkNearSupportLiteral_4_206⟩

end ProteinFolding.Tetrahedral

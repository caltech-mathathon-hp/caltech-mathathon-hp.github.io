import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_3_149 :
    BulkNearSupportQuickCheck (149 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_150 :
    BulkNearSupportQuickCheck (150 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_151 :
    BulkNearSupportQuickCheck (151 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_152 :
    BulkNearSupportQuickCheck (152 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_153 :
    BulkNearSupportQuickCheck (153 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_154 :
    BulkNearSupportQuickCheck (154 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_155 :
    BulkNearSupportQuickCheck (155 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_156 :
    BulkNearSupportQuickCheck (156 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_157 :
    BulkNearSupportQuickCheck (157 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_158 :
    BulkNearSupportQuickCheck (158 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_159 :
    BulkNearSupportQuickCheck (159 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_160 :
    BulkNearSupportQuickCheck (160 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_161 :
    BulkNearSupportQuickCheck (161 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_162 :
    BulkNearSupportQuickCheck (162 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_163 :
    BulkNearSupportQuickCheck (163 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_3_164 :
    BulkNearSupportQuickCheck (164 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_3_2 :
    BulkNearSupportQuickCheck (149 : Fin 234) ∧
    BulkNearSupportQuickCheck (150 : Fin 234) ∧
    BulkNearSupportQuickCheck (151 : Fin 234) ∧
    BulkNearSupportQuickCheck (152 : Fin 234) ∧
    BulkNearSupportQuickCheck (153 : Fin 234) ∧
    BulkNearSupportQuickCheck (154 : Fin 234) ∧
    BulkNearSupportQuickCheck (155 : Fin 234) ∧
    BulkNearSupportQuickCheck (156 : Fin 234) ∧
    BulkNearSupportQuickCheck (157 : Fin 234) ∧
    BulkNearSupportQuickCheck (158 : Fin 234) ∧
    BulkNearSupportQuickCheck (159 : Fin 234) ∧
    BulkNearSupportQuickCheck (160 : Fin 234) ∧
    BulkNearSupportQuickCheck (161 : Fin 234) ∧
    BulkNearSupportQuickCheck (162 : Fin 234) ∧
    BulkNearSupportQuickCheck (163 : Fin 234) ∧
    BulkNearSupportQuickCheck (164 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_3_149, bulkNearSupportLiteral_3_150, bulkNearSupportLiteral_3_151, bulkNearSupportLiteral_3_152, bulkNearSupportLiteral_3_153, bulkNearSupportLiteral_3_154, bulkNearSupportLiteral_3_155, bulkNearSupportLiteral_3_156, bulkNearSupportLiteral_3_157, bulkNearSupportLiteral_3_158, bulkNearSupportLiteral_3_159, bulkNearSupportLiteral_3_160, bulkNearSupportLiteral_3_161, bulkNearSupportLiteral_3_162, bulkNearSupportLiteral_3_163, bulkNearSupportLiteral_3_164⟩

end ProteinFolding.Tetrahedral

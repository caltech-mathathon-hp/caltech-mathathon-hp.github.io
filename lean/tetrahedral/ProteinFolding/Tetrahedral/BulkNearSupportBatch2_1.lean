import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_2_85 :
    BulkNearSupportQuickCheck (85 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_86 :
    BulkNearSupportQuickCheck (86 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_87 :
    BulkNearSupportQuickCheck (87 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_88 :
    BulkNearSupportQuickCheck (88 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_89 :
    BulkNearSupportQuickCheck (89 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_90 :
    BulkNearSupportQuickCheck (90 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_91 :
    BulkNearSupportQuickCheck (91 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_92 :
    BulkNearSupportQuickCheck (92 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_93 :
    BulkNearSupportQuickCheck (93 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_94 :
    BulkNearSupportQuickCheck (94 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_95 :
    BulkNearSupportQuickCheck (95 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_96 :
    BulkNearSupportQuickCheck (96 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_97 :
    BulkNearSupportQuickCheck (97 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_98 :
    BulkNearSupportQuickCheck (98 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_99 :
    BulkNearSupportQuickCheck (99 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_100 :
    BulkNearSupportQuickCheck (100 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_2_1 :
    BulkNearSupportQuickCheck (85 : Fin 234) ∧
    BulkNearSupportQuickCheck (86 : Fin 234) ∧
    BulkNearSupportQuickCheck (87 : Fin 234) ∧
    BulkNearSupportQuickCheck (88 : Fin 234) ∧
    BulkNearSupportQuickCheck (89 : Fin 234) ∧
    BulkNearSupportQuickCheck (90 : Fin 234) ∧
    BulkNearSupportQuickCheck (91 : Fin 234) ∧
    BulkNearSupportQuickCheck (92 : Fin 234) ∧
    BulkNearSupportQuickCheck (93 : Fin 234) ∧
    BulkNearSupportQuickCheck (94 : Fin 234) ∧
    BulkNearSupportQuickCheck (95 : Fin 234) ∧
    BulkNearSupportQuickCheck (96 : Fin 234) ∧
    BulkNearSupportQuickCheck (97 : Fin 234) ∧
    BulkNearSupportQuickCheck (98 : Fin 234) ∧
    BulkNearSupportQuickCheck (99 : Fin 234) ∧
    BulkNearSupportQuickCheck (100 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_2_85, bulkNearSupportLiteral_2_86, bulkNearSupportLiteral_2_87, bulkNearSupportLiteral_2_88, bulkNearSupportLiteral_2_89, bulkNearSupportLiteral_2_90, bulkNearSupportLiteral_2_91, bulkNearSupportLiteral_2_92, bulkNearSupportLiteral_2_93, bulkNearSupportLiteral_2_94, bulkNearSupportLiteral_2_95, bulkNearSupportLiteral_2_96, bulkNearSupportLiteral_2_97, bulkNearSupportLiteral_2_98, bulkNearSupportLiteral_2_99, bulkNearSupportLiteral_2_100⟩

end ProteinFolding.Tetrahedral

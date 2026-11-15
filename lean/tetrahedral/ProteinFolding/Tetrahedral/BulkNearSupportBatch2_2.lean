import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_2_101 :
    BulkNearSupportQuickCheck (101 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_102 :
    BulkNearSupportQuickCheck (102 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_103 :
    BulkNearSupportQuickCheck (103 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_104 :
    BulkNearSupportQuickCheck (104 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_105 :
    BulkNearSupportQuickCheck (105 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_106 :
    BulkNearSupportQuickCheck (106 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_107 :
    BulkNearSupportQuickCheck (107 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_108 :
    BulkNearSupportQuickCheck (108 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_109 :
    BulkNearSupportQuickCheck (109 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_110 :
    BulkNearSupportQuickCheck (110 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_111 :
    BulkNearSupportQuickCheck (111 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_112 :
    BulkNearSupportQuickCheck (112 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_113 :
    BulkNearSupportQuickCheck (113 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_114 :
    BulkNearSupportQuickCheck (114 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_115 :
    BulkNearSupportQuickCheck (115 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_116 :
    BulkNearSupportQuickCheck (116 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_2_2 :
    BulkNearSupportQuickCheck (101 : Fin 234) ∧
    BulkNearSupportQuickCheck (102 : Fin 234) ∧
    BulkNearSupportQuickCheck (103 : Fin 234) ∧
    BulkNearSupportQuickCheck (104 : Fin 234) ∧
    BulkNearSupportQuickCheck (105 : Fin 234) ∧
    BulkNearSupportQuickCheck (106 : Fin 234) ∧
    BulkNearSupportQuickCheck (107 : Fin 234) ∧
    BulkNearSupportQuickCheck (108 : Fin 234) ∧
    BulkNearSupportQuickCheck (109 : Fin 234) ∧
    BulkNearSupportQuickCheck (110 : Fin 234) ∧
    BulkNearSupportQuickCheck (111 : Fin 234) ∧
    BulkNearSupportQuickCheck (112 : Fin 234) ∧
    BulkNearSupportQuickCheck (113 : Fin 234) ∧
    BulkNearSupportQuickCheck (114 : Fin 234) ∧
    BulkNearSupportQuickCheck (115 : Fin 234) ∧
    BulkNearSupportQuickCheck (116 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_2_101, bulkNearSupportLiteral_2_102, bulkNearSupportLiteral_2_103, bulkNearSupportLiteral_2_104, bulkNearSupportLiteral_2_105, bulkNearSupportLiteral_2_106, bulkNearSupportLiteral_2_107, bulkNearSupportLiteral_2_108, bulkNearSupportLiteral_2_109, bulkNearSupportLiteral_2_110, bulkNearSupportLiteral_2_111, bulkNearSupportLiteral_2_112, bulkNearSupportLiteral_2_113, bulkNearSupportLiteral_2_114, bulkNearSupportLiteral_2_115, bulkNearSupportLiteral_2_116⟩

end ProteinFolding.Tetrahedral

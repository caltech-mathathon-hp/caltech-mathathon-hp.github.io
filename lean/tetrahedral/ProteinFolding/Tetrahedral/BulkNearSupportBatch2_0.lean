import ProteinFolding.Tetrahedral.BulkNearSupportCheckSpec

/-! Independent closed support and closure certificates. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private theorem bulkNearSupportLiteral_2_69 :
    BulkNearSupportQuickCheck (69 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_70 :
    BulkNearSupportQuickCheck (70 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_71 :
    BulkNearSupportQuickCheck (71 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_72 :
    BulkNearSupportQuickCheck (72 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_73 :
    BulkNearSupportQuickCheck (73 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_74 :
    BulkNearSupportQuickCheck (74 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_75 :
    BulkNearSupportQuickCheck (75 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_76 :
    BulkNearSupportQuickCheck (76 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_77 :
    BulkNearSupportQuickCheck (77 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_78 :
    BulkNearSupportQuickCheck (78 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_79 :
    BulkNearSupportQuickCheck (79 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_80 :
    BulkNearSupportQuickCheck (80 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_81 :
    BulkNearSupportQuickCheck (81 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_82 :
    BulkNearSupportQuickCheck (82 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_83 :
    BulkNearSupportQuickCheck (83 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

private theorem bulkNearSupportLiteral_2_84 :
    BulkNearSupportQuickCheck (84 : Fin 234) := by
  unfold BulkNearSupportQuickCheck BulkSegmentQuickCheck
  simp only [bulkNearSegmentSupport, List.mem_toFinset]
  decide +kernel

theorem bulkNearSupportBatch_2_0 :
    BulkNearSupportQuickCheck (69 : Fin 234) ∧
    BulkNearSupportQuickCheck (70 : Fin 234) ∧
    BulkNearSupportQuickCheck (71 : Fin 234) ∧
    BulkNearSupportQuickCheck (72 : Fin 234) ∧
    BulkNearSupportQuickCheck (73 : Fin 234) ∧
    BulkNearSupportQuickCheck (74 : Fin 234) ∧
    BulkNearSupportQuickCheck (75 : Fin 234) ∧
    BulkNearSupportQuickCheck (76 : Fin 234) ∧
    BulkNearSupportQuickCheck (77 : Fin 234) ∧
    BulkNearSupportQuickCheck (78 : Fin 234) ∧
    BulkNearSupportQuickCheck (79 : Fin 234) ∧
    BulkNearSupportQuickCheck (80 : Fin 234) ∧
    BulkNearSupportQuickCheck (81 : Fin 234) ∧
    BulkNearSupportQuickCheck (82 : Fin 234) ∧
    BulkNearSupportQuickCheck (83 : Fin 234) ∧
    BulkNearSupportQuickCheck (84 : Fin 234) := by
  exact ⟨bulkNearSupportLiteral_2_69, bulkNearSupportLiteral_2_70, bulkNearSupportLiteral_2_71, bulkNearSupportLiteral_2_72, bulkNearSupportLiteral_2_73, bulkNearSupportLiteral_2_74, bulkNearSupportLiteral_2_75, bulkNearSupportLiteral_2_76, bulkNearSupportLiteral_2_77, bulkNearSupportLiteral_2_78, bulkNearSupportLiteral_2_79, bulkNearSupportLiteral_2_80, bulkNearSupportLiteral_2_81, bulkNearSupportLiteral_2_82, bulkNearSupportLiteral_2_83, bulkNearSupportLiteral_2_84⟩

end ProteinFolding.Tetrahedral

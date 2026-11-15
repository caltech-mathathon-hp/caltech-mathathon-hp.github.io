import ProteinFolding.Tetrahedral.BulkNearSegmentsData

/-! The original support/closure predicate, with its component index explicit. -/

namespace ProteinFolding.Tetrahedral

def BulkNearSupportQuickCheck (i : Fin 234) : Prop :=
  BulkSegmentQuickCheck 50 (bulkNearSegmentSupport i) (bulkNearSegmentRoot i)
    (bulkNearSegmentRank i) (bulkNearSegmentPrev i)

end ProteinFolding.Tetrahedral

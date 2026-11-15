import ProteinFolding.Tetrahedral.BulkNearCoreData
import ProteinFolding.Tetrahedral.BulkPatchSupport

/-! Direct lookup certificates for every endpoint of every frozen local patch. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

def BulkNearPatchReferenceCheck (v : Fin 6) : Prop :=
  ∀ r (hr : r ∈ bulkPatchOffsets v),
    bulkPatchOffsetSite 50 v ⟨r, hr⟩ ∈
        bulkNearSegmentSupport (bulkNearPatchSegmentIndex v r) ∧
      bulkNearSegmentVertex (bulkNearPatchSegmentIndex v r) = v ∧
      bulkNearSegmentCore (bulkNearPatchSegmentIndex v r) = true

instance (v : Fin 6) : Decidable (BulkNearPatchReferenceCheck v) := by
  unfold BulkNearPatchReferenceCheck
  infer_instance

theorem bulkNearPatch_reference (v : Fin 6) : BulkNearPatchReferenceCheck v := by
  revert v
  decide

end ProteinFolding.Tetrahedral

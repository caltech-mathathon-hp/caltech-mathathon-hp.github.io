import ProteinFolding.Tetrahedral.BulkNearCoreData
import ProteinFolding.Tetrahedral.BulkNearEscapeData
import ProteinFolding.Tetrahedral.BulkSegments

/-! Decidable reference claims for the near-core escape witnesses. The
statistics are computed from the complete finite supports, rather than
being assumed to equal the noncomputable ambient component statistics. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem bulkNearSegment_points_nonempty (i : Fin 234) : bulkNearSegmentPoints i ≠ [] := by
  revert i
  decide

theorem bulkNearSegment_root_mem (i : Fin 234) : bulkNearSegmentRoot i ∈ bulkNearSegmentSupport i := by
  change (bulkNearSegmentPoints i).headD _ ∈ (bulkNearSegmentPoints i).toFinset
  apply List.mem_toFinset.mpr
  cases h : bulkNearSegmentPoints i with
  | nil => exact False.elim (bulkNearSegment_points_nonempty i h)
  | cons p ps => simp

def bulkNearSegmentX_nonempty (i : Fin 234) :
    ((bulkNearSegmentSupport i).image (fun p => p.val 0)).Nonempty :=
  ⟨(bulkNearSegmentRoot i).val 0, Finset.mem_image.mpr ⟨_, bulkNearSegment_root_mem i, rfl⟩⟩

def bulkNearReferenceXhat (i : Fin 234) : ℤ :=
  ((bulkNearSegmentSupport i).image (fun p => p.val 0)).min' (bulkNearSegmentX_nonempty i) +
    ((bulkNearSegmentSupport i).image (fun p => p.val 0)).max' (bulkNearSegmentX_nonempty i)

def BulkNearReferenceRow (i : Fin 234) : Prop :=
  ∃ p ∈ bulkNearSegmentSupport i, bulkFastDamaged 50 p ∧ bulkZ p = 0

instance (i : Fin 234) : Decidable (BulkNearReferenceRow i) := by
  unfold BulkNearReferenceRow
  infer_instance

def bulkNearReferencePotential (i : Fin 234) : BulkSegmentOrder :=
  if BulkNearReferenceRow i then toLex (2, toLex (|bulkNearReferenceXhat i|, 0))
  else if 0 < bulkAlpha 50 (bulkNearSegmentRoot i) then
    toLex (1, toLex (bulkAlpha 50 (bulkNearSegmentRoot i), bulkNearReferenceXhat i))
  else toLex (0, toLex (bulkNearReferenceXhat i, 0))

def BulkNearCoreEscapeCheck (i : Fin 234) : Prop :=
  bulkNearSegmentCore i = true →
    if (bulkNearCoreCase i).val = 0 then
      bulkNearCoreSource i ∈ bulkNearSegmentSupport i ∧
        (bulkFastCoverDirections 50 (bulkNearCoreSource i)).card ≤ 1
    else if (bulkNearCoreCase i).val = 1 then
      bulkNearCoreSource i ∈ bulkNearSegmentSupport i ∧
        bulkNearCoreTarget i ∈ bulkNearSegmentSupport (bulkNearCoreNext i) ∧
        bulkFastCoverBond 50 (bulkNearCoreSource i) (bulkNearCoreTarget i) ∧
        bulkNearSegmentVertex (bulkNearCoreNext i) = bulkNearSegmentVertex i ∧
        bulkNearReferencePotential i < bulkNearReferencePotential (bulkNearCoreNext i)
    else bulkNearEscapeStart (bulkNearCoreException i) ∈ bulkNearSegmentSupport i ∧
      bulkNearEscapeVertex (bulkNearCoreException i) = bulkNearSegmentVertex i

instance (i : Fin 234) : Decidable (BulkNearCoreEscapeCheck i) := by
  unfold BulkNearCoreEscapeCheck
  infer_instance

end ProteinFolding.Tetrahedral

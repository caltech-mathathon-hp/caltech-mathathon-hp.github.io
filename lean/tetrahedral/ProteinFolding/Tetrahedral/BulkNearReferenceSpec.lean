import ProteinFolding.Tetrahedral.BulkNearSegmentsData

/-! Small computable statements for the reference lookup and vertex boxes.
They use list membership, avoiding duplicate elimination during reduction. -/

namespace ProteinFolding.Tetrahedral

def bulkNearReferenceFrameFintype : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

def BulkNearCandidateReferenceCheck (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d : Fin 4) : Prop :=
  bulkFastDamaged 50 (bulkEdgeCandidate 50 F t.val odd d (by decide)) →
    bulkEdgeCandidate 50 F t.val odd d (by decide) ∈
        bulkNearSegmentPoints (bulkNearSegmentCandidateIndex F t odd d) ∧
      bulkNearSegmentVertex (bulkNearSegmentCandidateIndex F t odd d) = bulkEdgeStartIndex F ∧
      bulkNearSegmentCore (bulkNearSegmentCandidateIndex F t odd d) = true

instance (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d : Fin 4) :
    Decidable (BulkNearCandidateReferenceCheck F t odd d) := by
  unfold BulkNearCandidateReferenceCheck
  infer_instance

def BulkNearBoxReferenceCheck (i : Fin 234) : Prop :=
  ∀ p ∈ bulkNearSegmentPoints i, InBulkVertexBox 50 (bulkNearSegmentVertex i) 43 p

instance (i : Fin 234) : Decidable (BulkNearBoxReferenceCheck i) := by
  unfold BulkNearBoxReferenceCheck InBulkVertexBox
  infer_instance

end ProteinFolding.Tetrahedral

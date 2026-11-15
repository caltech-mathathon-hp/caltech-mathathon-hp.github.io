import ProteinFolding.Tetrahedral.BulkNearCandidateCheck0
import ProteinFolding.Tetrahedral.BulkNearCandidateCheck1
import ProteinFolding.Tetrahedral.BulkNearCandidateCheck2
import ProteinFolding.Tetrahedral.BulkNearCandidateCheck3
import ProteinFolding.Tetrahedral.BulkNearBoxCheck0
import ProteinFolding.Tetrahedral.BulkNearBoxCheck1
import ProteinFolding.Tetrahedral.BulkNearBoxCheck2
import ProteinFolding.Tetrahedral.BulkNearBoxCheck3
import ProteinFolding.Tetrahedral.BulkNearBoxCheck4
import ProteinFolding.Tetrahedral.BulkNearBoxCheck5

/-! Every near damaged-edge candidate has a named complete-segment witness.
The index is explicit, so the kernel checks a direct lookup rather than searching
through all the segment supports. -/

namespace ProteinFolding.Tetrahedral

theorem bulkNearSegment_candidate_reference (F : OctEdgeFrame) (t : Fin 10)
    (odd : Bool) (d : Fin 4)
    (hd : bulkFastDamaged 50 (bulkEdgeCandidate 50 F t.val odd d (by decide))) :
    bulkEdgeCandidate 50 F t.val odd d (by decide) ∈
        bulkNearSegmentSupport (bulkNearSegmentCandidateIndex F t odd d) ∧
      bulkNearSegmentVertex (bulkNearSegmentCandidateIndex F t odd d) = bulkEdgeStartIndex F ∧
      bulkNearSegmentCore (bulkNearSegmentCandidateIndex F t odd d) = true := by
  have hcheck : BulkNearCandidateReferenceCheck F t odd d := by
    have h : ∀ k : Fin 4, F.k = k → BulkNearCandidateReferenceCheck F t odd d := by
      intro k
      fin_cases k
      · intro hk; exact bulkNearCandidate_reference_0 F hk t odd d
      · intro hk; exact bulkNearCandidate_reference_1 F hk t odd d
      · intro hk; exact bulkNearCandidate_reference_2 F hk t odd d
      · intro hk; exact bulkNearCandidate_reference_3 F hk t odd d
    exact h _ rfl
  simpa only [bulkNearSegmentSupport, List.mem_toFinset] using hcheck hd

theorem bulkNearSegment_reference_box (i : Fin 234) :
    ∀ p ∈ bulkNearSegmentSupport i, InBulkVertexBox 50 (bulkNearSegmentVertex i) 43 p := by
  have hcheck : BulkNearBoxReferenceCheck i := by
    have h : ∀ v : Fin 6, bulkNearSegmentVertex i = v → BulkNearBoxReferenceCheck i := by
      intro v
      fin_cases v
      · exact bulkNearBox_reference_0 i
      · exact bulkNearBox_reference_1 i
      · exact bulkNearBox_reference_2 i
      · exact bulkNearBox_reference_3 i
      · exact bulkNearBox_reference_4 i
      · exact bulkNearBox_reference_5 i
    exact h _ rfl
  simpa only [BulkNearBoxReferenceCheck, bulkNearSegmentSupport, List.mem_toFinset] using hcheck

end ProteinFolding.Tetrahedral

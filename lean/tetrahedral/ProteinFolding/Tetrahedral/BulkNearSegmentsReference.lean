import ProteinFolding.Tetrahedral.BulkNearSegmentsCheck0
import ProteinFolding.Tetrahedral.BulkNearSegmentsCheck1
import ProteinFolding.Tetrahedral.BulkNearSegmentsCheck2
import ProteinFolding.Tetrahedral.BulkNearSegmentsCheck3
import ProteinFolding.Tetrahedral.BulkNearSegmentsCheck4
import ProteinFolding.Tetrahedral.BulkNearSegmentsCheck5
import ProteinFolding.Tetrahedral.BulkNearSegmentsCandidateReference
import ProteinFolding.Tetrahedral.BulkNearCoreCertificates
import ProteinFolding.Tetrahedral.BulkSegmentWitnessValues

/-! The reference table lists complete components of the actual rung subgraph.
Its finite statistics therefore agree with the ambient component potential. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkNearSegment_reference_quick (i : Fin 234) :
    BulkSegmentQuickCheck 50 (bulkNearSegmentSupport i) (bulkNearSegmentRoot i)
      (bulkNearSegmentRank i) (bulkNearSegmentPrev i) := by
  have h : ∀ v : Fin 6, bulkNearSegmentVertex i = v →
      BulkSegmentQuickCheck 50 (bulkNearSegmentSupport i) (bulkNearSegmentRoot i)
        (bulkNearSegmentRank i) (bulkNearSegmentPrev i) := by
    intro v
    fin_cases v
    · exact bulkNearSegment_reference_quick_0 i
    · exact bulkNearSegment_reference_quick_1 i
    · exact bulkNearSegment_reference_quick_2 i
    · exact bulkNearSegment_reference_quick_3 i
    · exact bulkNearSegment_reference_quick_4 i
    · exact bulkNearSegment_reference_quick_5 i
  exact h _ rfl

theorem bulkNearSegment_reference_certificate (i : Fin 234) :
    BulkSegmentFiniteCheck 50 (bulkNearSegmentSupport i) (bulkNearSegmentRoot i)
      (bulkNearSegmentRank i) :=
  bulkSegmentQuickCheck_sound 50 _ _ _ _ (bulkNearSegment_reference_quick i)

def bulkNearSegmentReferenceView (i : Fin 234) : BulkVertex 50 :=
  ⟨bulkNearSegmentRoot i, (bulkInterior_fast_iff 50 _).mpr
    ((bulkNearSegment_reference_certificate i).2.1 _
      (bulkNearSegment_reference_certificate i).1)⟩

theorem bulkNearSegment_reference_potential (i : Fin 234) :
    bulkSegmentPotential 50 (bulkNearSegmentReferenceView i) =
      bulkNearReferencePotential i := by
  classical
  have hx := bulkSegmentFiniteCheck_xhat 50 (bulkNearSegmentReferenceView i)
    (bulkNearSegmentSupport i) (bulkNearSegmentRank i)
    (bulkNearSegment_reference_certificate i) (bulkNearSegmentX_nonempty i)
  have hhat : bulkSegmentXhat 50 (bulkNearSegmentReferenceView i) =
      bulkNearReferenceXhat i := hx
  have hα : bulkAlpha 50 (bulkNearSegmentReferenceView i).val =
      bulkAlpha 50 (bulkNearSegmentRoot i) := rfl
  have hr : BulkRowSegment 50 (bulkNearSegmentReferenceView i) ↔
      BulkNearReferenceRow i := by
    rw [bulkSegmentFiniteCheck_row 50 (bulkNearSegmentReferenceView i)
      (bulkNearSegmentSupport i) (bulkNearSegmentRank i)
      (bulkNearSegment_reference_certificate i)]
    simp only [BulkNearReferenceRow, bulkDamaged_fast_iff]
  unfold bulkSegmentPotential bulkNearReferencePotential
  by_cases hrow : BulkNearReferenceRow i
  · simp only [if_pos (hr.mpr hrow), if_pos hrow, hhat]
  · have hnrow : ¬BulkRowSegment 50 (bulkNearSegmentReferenceView i) :=
      fun h => hrow (hr.mp h)
    simp only [if_neg hnrow, if_neg hrow, hα]
    by_cases ha : 0 < bulkAlpha 50 (bulkNearSegmentRoot i)
    · simp only [if_pos ha, hhat]
    · simp only [if_neg ha, hhat]

theorem bulkSegment_reachable_iff_site (m : ℕ) (p q : BulkVertex m) :
    (bulkSegmentGraph m).Reachable p q ↔
      (bulkSiteSegmentGraph m).Reachable p.val q.val := by
  rw [← bulkSegmentSites_image_component]
  constructor
  · intro h
    exact Finset.mem_image.mpr ⟨q, (mem_bulkSegmentSites m p q).mpr h, rfl⟩
  · intro h
    obtain ⟨r, hr, hval⟩ := Finset.mem_image.mp h
    have heq : r = q := Subtype.ext hval
    subst r
    exact (mem_bulkSegmentSites m p q).mp hr

theorem bulkSegment_reachable_cover (m : ℕ) {p q : BulkVertex m}
    (h : (bulkSegmentGraph m).Reachable p q) :
    (bulkFiniteGraph m).Reachable p q := by
  obtain ⟨w⟩ := h
  let f : bulkSegmentGraph m →g bulkFiniteGraph m :=
    ⟨id, by intro a b hadj; exact hadj.1⟩
  exact ⟨w.map f⟩

end ProteinFolding.Tetrahedral

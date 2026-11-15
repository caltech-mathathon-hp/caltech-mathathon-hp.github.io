import ProteinFolding.Tetrahedral.BulkNearReferenceSpec
import ProteinFolding.Tetrahedral.BulkNearCandidatePositions

/-! Optional direct-position lookup checks. Soundness derives the original
public reference statement; no position is accepted without kernel checking. -/

namespace ProteinFolding.Tetrahedral

def bulkSiteCoordinatesMatch (p q : Site) : Bool :=
  decide (p.val 0 = q.val 0 ∧ p.val 1 = q.val 1 ∧ p.val 2 = q.val 2)

def bulkSiteListPositionMatch (ps : List Site) (i : ℕ) (p : Site) : Bool :=
  match ps[i]? with
  | none => false
  | some q => bulkSiteCoordinatesMatch q p

theorem bulkSiteListPositionMatch_mem (ps : List Site) (i : ℕ) (p : Site)
    (h : bulkSiteListPositionMatch ps i p = true) : p ∈ ps := by
  cases hget : ps[i]? with
  | none => simp only [bulkSiteListPositionMatch, hget, Bool.false_eq_true] at h
  | some q =>
    have hc : q.val 0 = p.val 0 ∧ q.val 1 = p.val 1 ∧ q.val 2 = p.val 2 := by
      apply of_decide_eq_true
      simpa only [bulkSiteListPositionMatch, hget, bulkSiteCoordinatesMatch] using h
    have hqp : q = p := by
      apply Subtype.ext
      funext k
      fin_cases k
      · exact hc.1
      · exact hc.2.1
      · exact hc.2.2
    have hm := List.mem_of_getElem? hget
    simpa only [hqp] using hm

def BulkNearCandidatePositionCheck (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d : Fin 4) : Prop :=
  bulkFastDamaged 50 (bulkEdgeCandidate 50 F t.val odd d (by decide)) →
    bulkSiteListPositionMatch (bulkNearSegmentPoints (bulkNearSegmentCandidateIndex F t odd d))
        (bulkNearCandidatePosition F t odd d) (bulkEdgeCandidate 50 F t.val odd d (by decide)) = true ∧
      bulkNearSegmentVertex (bulkNearSegmentCandidateIndex F t odd d) = bulkEdgeStartIndex F ∧
      bulkNearSegmentCore (bulkNearSegmentCandidateIndex F t odd d) = true

instance (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d : Fin 4) :
    Decidable (BulkNearCandidatePositionCheck F t odd d) := by
  unfold BulkNearCandidatePositionCheck
  infer_instance

theorem bulkNearCandidatePositionCheck_sound (F : OctEdgeFrame) (t : Fin 10) (odd : Bool) (d : Fin 4)
    (h : BulkNearCandidatePositionCheck F t odd d) : BulkNearCandidateReferenceCheck F t odd d := by
  intro hd
  obtain ⟨hget, hv, hc⟩ := h hd
  exact ⟨bulkSiteListPositionMatch_mem _ _ _ hget, hv, hc⟩

end ProteinFolding.Tetrahedral

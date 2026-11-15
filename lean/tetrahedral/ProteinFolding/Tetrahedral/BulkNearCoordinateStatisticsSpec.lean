import ProteinFolding.Tetrahedral.BulkNearCoordinateStatisticsData
import ProteinFolding.Tetrahedral.BulkNearCoreCertificates

/-! Bounds and attained extrema certify the same finite-support statistic used
by the original near-core statement. No computation of Site equality is needed. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def bulkSiteListPositionXMatch (ps : List Site) (i : ℕ) (x : ℤ) : Bool :=
  match ps[i]? with
  | none => false
  | some p => decide (p.val 0 = x)

theorem bulkSiteListPositionXMatch_mem (ps : List Site) (i : ℕ) (x : ℤ)
    (h : bulkSiteListPositionXMatch ps i x = true) :
    x ∈ ps.toFinset.image (fun p => p.val 0) := by
  cases hget : ps[i]? with
  | none => simp only [bulkSiteListPositionXMatch, hget, Bool.false_eq_true] at h
  | some p =>
    have hx : p.val 0 = x := by
      apply of_decide_eq_true
      simpa only [bulkSiteListPositionXMatch, hget] using h
    exact Finset.mem_image.mpr ⟨p, List.mem_toFinset.mpr (List.mem_of_getElem? hget), hx⟩

def BulkNearCoordinateStatisticsCheck (i : Fin 234) : Prop :=
  (∀ p ∈ bulkNearSegmentPoints i,
    bulkNearCoordinateMin i ≤ p.val 0 ∧ p.val 0 ≤ bulkNearCoordinateMax i) ∧
  bulkSiteListPositionXMatch (bulkNearSegmentPoints i)
    (bulkNearCoordinateMinPosition i) (bulkNearCoordinateMin i) = true ∧
  bulkSiteListPositionXMatch (bulkNearSegmentPoints i)
    (bulkNearCoordinateMaxPosition i) (bulkNearCoordinateMax i) = true

instance (i : Fin 234) : Decidable (BulkNearCoordinateStatisticsCheck i) := by
  unfold BulkNearCoordinateStatisticsCheck
  infer_instance

theorem bulkNearCoordinateStatisticsCheck_sound (i : Fin 234)
    (h : BulkNearCoordinateStatisticsCheck i) :
    bulkNearReferenceXhat i = bulkNearCoordinateMin i + bulkNearCoordinateMax i := by
  obtain ⟨hbound, hlo, hhi⟩ := h
  have hloMem : bulkNearCoordinateMin i ∈
      (bulkNearSegmentSupport i).image (fun p => p.val 0) :=
    bulkSiteListPositionXMatch_mem _ _ _ hlo
  have hhiMem : bulkNearCoordinateMax i ∈
      (bulkNearSegmentSupport i).image (fun p => p.val 0) :=
    bulkSiteListPositionXMatch_mem _ _ _ hhi
  have hb : ∀ x ∈ (bulkNearSegmentSupport i).image (fun p => p.val 0),
      bulkNearCoordinateMin i ≤ x ∧ x ≤ bulkNearCoordinateMax i := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact hbound p (List.mem_toFinset.mp hp)
  have hmin : ((bulkNearSegmentSupport i).image (fun p => p.val 0)).min'
      (bulkNearSegmentX_nonempty i) = bulkNearCoordinateMin i := by
    apply le_antisymm
    · exact Finset.min'_le _ _ hloMem
    · exact Finset.le_min' _ _ _ (fun x hx => (hb x hx).1)
  have hmax : ((bulkNearSegmentSupport i).image (fun p => p.val 0)).max'
      (bulkNearSegmentX_nonempty i) = bulkNearCoordinateMax i := by
    apply le_antisymm
    · exact Finset.max'_le _ _ _ (fun x hx => (hb x hx).2)
    · exact Finset.le_max' _ _ hhiMem
  exact congrArg₂ (· + ·) hmin hmax

end ProteinFolding.Tetrahedral

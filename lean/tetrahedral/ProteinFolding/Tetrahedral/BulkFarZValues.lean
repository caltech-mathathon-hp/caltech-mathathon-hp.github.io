import ProteinFolding.Tetrahedral.BulkFarZData
import ProteinFolding.Tetrahedral.BulkSegmentEdgeValues

/-! The six complete row supports retain their exact statistics at every
far edge location. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def BulkFarZFamily (F : OctEdgeFrame) (i : Fin 6) : Prop :=
  (bulkFarZPositiveFrame F ∧ i.val < 3) ∨ (bulkFarZNegativeFrame F ∧ 3 ≤ i.val)

theorem bulkFarZ_root_mem (i : Fin 6) : bulkFarZRoot i ∈ bulkFarZSupport i := by
  simp only [bulkFarZSupport, Finset.mem_insert, Finset.mem_singleton, true_or]

def bulkFarZReferenceView (i : Fin 6) : BulkVertex 27 :=
  ⟨bulkFarZRoot i, (bulkInterior_fast_iff 27 _).mpr
    ((bulkFarZ_reference_quick i).2.1 _ (bulkFarZ_root_mem i))⟩

def bulkFarZXhat (i : Fin 6) : ℤ :=
  match i.val with
  | 0 => 49
  | 1 => 53
  | 2 => 57
  | 3 => -49
  | 4 => -53
  | _ => -57

theorem bulkFarZ_reference_xhat (i : Fin 6) :
    bulkSegmentXhat 27 (bulkFarZReferenceView i) = bulkFarZXhat i := by
  have hne : ((bulkFarZSupport i).image (fun q => q.val 0)).Nonempty :=
    ⟨(bulkFarZRoot i).val 0, Finset.mem_image.mpr ⟨_, bulkFarZ_root_mem i, rfl⟩⟩
  rw [bulkSegmentFiniteCheck_xhat 27 (bulkFarZReferenceView i) (bulkFarZSupport i)
    (bulkFarZRank i) (bulkFarZ_reference_finite i) hne]
  simp only [bulkFarZSupport, Finset.image_insert, Finset.image_singleton,
    Finset.min'_pair, Finset.max'_pair]
  fin_cases i <;> decide

theorem bulkFarZ_reference_row_actual (i : Fin 6) : BulkRowSegment 27 (bulkFarZReferenceView i) := by
  apply (bulkSegmentFiniteCheck_row 27 (bulkFarZReferenceView i) (bulkFarZSupport i)
    (bulkFarZRank i) (bulkFarZ_reference_finite i)).mpr
  obtain ⟨p, hp, hd, hz⟩ := bulkFarZ_reference_row i
  exact ⟨p, hp, (bulkDamaged_fast_iff 27 p).mpr hd, hz⟩

def bulkFarZView (m t : ℕ) (F : OctEdgeFrame) (i : Fin 6)
    (ht : 13 ≤ t) (htm : t + 14 ≤ m) (hf : BulkFarZFamily F i) : BulkVertex m :=
  ⟨bulkEdgeReanchor 27 m 13 t F (bulkFarZRoot i),
    (bulkEdgeReanchor_interior_iff 27 m 13 t F 5 _ (by decide) (by decide)
      (by omega) (by omega) (bulkFarZ_reference_boxes F i hf _ (bulkFarZ_root_mem i))).mpr
      (bulkFarZReferenceView i).property⟩

theorem bulkFarZ_view_xhat (m t : ℕ) (F : OctEdgeFrame) (i : Fin 6)
    (ht : 13 ≤ t) (htm : t + 14 ≤ m) (hf : BulkFarZFamily F i) :
    bulkSegmentXhat m (bulkFarZView m t F i ht htm hf) = bulkFarZXhat i +
      2 * ((bulkEdgeAnchor m F t).val 0 - (bulkEdgeAnchor 27 F 13).val 0) := by
  have h := bulkSegment_edge_xhat_shift 27 m 13 t F 5 (bulkFarZSupport i)
    (bulkFarZReferenceView i) (bulkFarZView m t F i ht htm hf) (bulkFarZRank i)
    (by decide) (by decide) ht htm (bulkFarZ_reference_boxes F i hf)
    (bulkFarZ_reference_finite i) rfl
  rwa [bulkFarZ_reference_xhat i] at h

theorem bulkFarZ_view_row (m t : ℕ) (F : OctEdgeFrame) (i : Fin 6)
    (ht : 13 ≤ t) (htm : t + 14 ≤ m) (hf : BulkFarZFamily F i) :
    BulkRowSegment m (bulkFarZView m t F i ht htm hf) :=
  (bulkSegment_edge_row 27 m 13 t F 5 (bulkFarZSupport i)
    (bulkFarZReferenceView i) (bulkFarZView m t F i ht htm hf) (bulkFarZRank i)
    (by decide) (by decide) ht htm (bulkFarZ_reference_boxes F i hf)
    (bulkFarZ_reference_finite i) rfl).mpr (bulkFarZ_reference_row_actual i)

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkFarZNearData

/-! Exact transition-row potentials at size50, before vertex transport. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkFarZNear_root_mem (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6) :
    bulkFarZNearRoot F j i ∈ bulkFarZNearSupport F j i := by
  simp only [bulkFarZNearSupport, Finset.mem_insert, Finset.mem_singleton, true_or]

theorem bulkFarZNear_reference_finite (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6)
    (hf : BulkFarZFamily F i) : BulkSegmentFiniteCheck 50 (bulkFarZNearSupport F j i)
      (bulkFarZNearRoot F j i) (bulkFarZNearRank F j i) :=
  bulkSegmentQuickCheck_sound 50 _ _ _ _ (bulkFarZNear_reference_quick F j i hf)

def bulkFarZNearReferenceView (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6)
    (hf : BulkFarZFamily F i) : BulkVertex 50 :=
  ⟨bulkFarZNearRoot F j i, (bulkInterior_fast_iff 50 _).mpr
    ((bulkFarZNear_reference_quick F j i hf).2.1 _ (bulkFarZNear_root_mem F j i))⟩

def bulkFarZNearXhat (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6) : ℤ :=
  (bulkFarZNearRoot F j i).val 0 + (bulkFarZNearOther F j i).val 0

theorem bulkFarZNear_reference_xhat (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6)
    (hf : BulkFarZFamily F i) :
    bulkSegmentXhat 50 (bulkFarZNearReferenceView F j i hf) = bulkFarZNearXhat F j i := by
  have hne : ((bulkFarZNearSupport F j i).image (fun q => q.val 0)).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨_, bulkFarZNear_root_mem F j i, rfl⟩⟩
  rw [bulkSegmentFiniteCheck_xhat 50 (bulkFarZNearReferenceView F j i hf) (bulkFarZNearSupport F j i)
    (bulkFarZNearRank F j i) (bulkFarZNear_reference_finite F j i hf) hne]
  simp only [bulkFarZNearSupport, Finset.image_insert, Finset.image_singleton, Finset.min'_pair,
    Finset.max'_pair]
  unfold bulkFarZNearXhat
  rcases le_total ((bulkFarZNearRoot F j i).val 0) ((bulkFarZNearOther F j i).val 0) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    omega

theorem bulkFarZNear_reference_row_actual (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6)
    (hf : BulkFarZFamily F i) : BulkRowSegment 50 (bulkFarZNearReferenceView F j i hf) := by
  apply (bulkSegmentFiniteCheck_row 50 (bulkFarZNearReferenceView F j i hf) (bulkFarZNearSupport F j i)
    (bulkFarZNearRank F j i) (bulkFarZNear_reference_finite F j i hf)).mpr
  obtain ⟨p, hp, hd, hz⟩ := bulkFarZNear_reference_row F j i hf
  exact ⟨p, hp, (bulkDamaged_fast_iff 50 p).mpr hd, hz⟩

local instance bulkFarZNearValuesFrameFintype : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bulkFarZNear_reference_abs_up (F : OctEdgeFrame) (j : Fin 3) (i : Fin 4) :
    BulkFarZAscendingFrame F i →
      |bulkFarZNearXhat F j (bulkFarZFrom i)| < |bulkFarZNearXhat F j (bulkFarZTo i)| := by
  unfold BulkFarZAscendingFrame
  revert F j i
  decide

theorem bulkFarZNear_reference_potential_up (F : OctEdgeFrame) (j : Fin 3) (i : Fin 4)
    (hf : BulkFarZAscendingFrame F i) :
    bulkSegmentPotential 50 (bulkFarZNearReferenceView F j (bulkFarZFrom i) (bulkFarZ_from_family F i hf)) <
      bulkSegmentPotential 50 (bulkFarZNearReferenceView F j (bulkFarZTo i) (bulkFarZ_to_family F i hf)) := by
  apply bulkSegmentPotential_lt_of_row_abs_up
  · exact bulkFarZNear_reference_row_actual F j _ (bulkFarZ_from_family F i hf)
  · exact bulkFarZNear_reference_row_actual F j _ (bulkFarZ_to_family F i hf)
  rw [bulkFarZNear_reference_xhat, bulkFarZNear_reference_xhat]
  exact bulkFarZNear_reference_abs_up F j i hf

end ProteinFolding.Tetrahedral

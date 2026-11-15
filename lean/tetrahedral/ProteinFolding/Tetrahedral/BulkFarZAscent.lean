import ProteinFolding.Tetrahedral.BulkFarZValues
import ProteinFolding.Tetrahedral.BulkPotentialComparisons
import ProteinFolding.Tetrahedral.BulkGraphReachability

/-! Uniform strict row ascents at far class-Z edges. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def BulkFarZAscendingFrame (F : OctEdgeFrame) (i : Fin 4) : Prop :=
  (bulkFarZPositiveFrame F ∧ i.val < 2) ∨ (bulkFarZNegativeFrame F ∧ 2 ≤ i.val)

theorem bulkFarZ_from_family (F : OctEdgeFrame) (i : Fin 4) (h : BulkFarZAscendingFrame F i) :
    BulkFarZFamily F (bulkFarZFrom i) := by
  fin_cases i <;> simp_all [BulkFarZAscendingFrame, BulkFarZFamily, bulkFarZFrom]

theorem bulkFarZ_to_family (F : OctEdgeFrame) (i : Fin 4) (h : BulkFarZAscendingFrame F i) :
    BulkFarZFamily F (bulkFarZTo i) := by
  fin_cases i <;> simp_all [BulkFarZAscendingFrame, BulkFarZFamily, bulkFarZFrom, bulkFarZTo]

theorem bulkFarZ_anchor_positive_shift (m t : ℕ) (F : OctEdgeFrame)
    (ht : 13 ≤ t) (htm : t + 14 ≤ m) (hF : bulkFarZPositiveFrame F) :
    0 ≤ (bulkEdgeAnchor m F t).val 0 - (bulkEdgeAnchor 27 F 13).val 0 := by
  have hm : 1 ≤ m := by omega
  rw [bulkEdgeAnchor_closedCoordinates hm F t, bulkEdgeAnchor_closedCoordinates (by decide : 1 ≤ 27) F 13]
  rcases F with ⟨k, j, a, b, hkj, hka, hkb, hja, hjb, hab⟩
  fin_cases k <;> fin_cases j <;> fin_cases a <;> fin_cases b
  all_goals simp_all [bulkFarZPositiveFrame, bulkEdgeClosedCoordinates, bulkEdgeFaceValue, octRadius]
  all_goals omega

theorem bulkFarZ_anchor_negative_shift (m t : ℕ) (F : OctEdgeFrame)
    (ht : 13 ≤ t) (htm : t + 14 ≤ m) (hF : bulkFarZNegativeFrame F) :
    (bulkEdgeAnchor m F t).val 0 - (bulkEdgeAnchor 27 F 13).val 0 ≤ 0 := by
  have hm : 1 ≤ m := by omega
  rw [bulkEdgeAnchor_closedCoordinates hm F t, bulkEdgeAnchor_closedCoordinates (by decide : 1 ≤ 27) F 13]
  rcases F with ⟨k, j, a, b, hkj, hka, hkb, hja, hjb, hab⟩
  fin_cases k <;> fin_cases j <;> fin_cases a <;> fin_cases b
  all_goals simp_all [bulkFarZNegativeFrame, bulkEdgeClosedCoordinates, bulkEdgeFaceValue, octRadius]
  all_goals omega

theorem bulkFarZ_ascent_potential (m t : ℕ) (F : OctEdgeFrame) (i : Fin 4)
    (ht : 13 ≤ t) (htm : t + 14 ≤ m) (hf : BulkFarZAscendingFrame F i) :
    bulkSegmentPotential m (bulkFarZView m t F (bulkFarZFrom i) ht htm (bulkFarZ_from_family F i hf)) <
      bulkSegmentPotential m (bulkFarZView m t F (bulkFarZTo i) ht htm (bulkFarZ_to_family F i hf)) := by
  apply bulkSegmentPotential_lt_of_row_abs_up
  · exact bulkFarZ_view_row m t F _ ht htm (bulkFarZ_from_family F i hf)
  · exact bulkFarZ_view_row m t F _ ht htm (bulkFarZ_to_family F i hf)
  rw [bulkFarZ_view_xhat, bulkFarZ_view_xhat]
  fin_cases i
  · change |(49 : ℤ) + 2 * ((bulkEdgeAnchor m F t).val 0 - (bulkEdgeAnchor 27 F 13).val 0)| <
      |53 + 2 * ((bulkEdgeAnchor m F t).val 0 - (bulkEdgeAnchor 27 F 13).val 0)|
    have hF : bulkFarZPositiveFrame F := by simpa [BulkFarZAscendingFrame] using hf
    have hs := bulkFarZ_anchor_positive_shift m t F ht htm hF
    rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
    omega
  · change |(53 : ℤ) + 2 * ((bulkEdgeAnchor m F t).val 0 - (bulkEdgeAnchor 27 F 13).val 0)| <
      |57 + 2 * ((bulkEdgeAnchor m F t).val 0 - (bulkEdgeAnchor 27 F 13).val 0)|
    have hF : bulkFarZPositiveFrame F := by simpa [BulkFarZAscendingFrame] using hf
    have hs := bulkFarZ_anchor_positive_shift m t F ht htm hF
    rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
    omega
  · change |(-49 : ℤ) + 2 * ((bulkEdgeAnchor m F t).val 0 - (bulkEdgeAnchor 27 F 13).val 0)| <
      |-53 + 2 * ((bulkEdgeAnchor m F t).val 0 - (bulkEdgeAnchor 27 F 13).val 0)|
    have hF : bulkFarZNegativeFrame F := by simpa [BulkFarZAscendingFrame] using hf
    have hs := bulkFarZ_anchor_negative_shift m t F ht htm hF
    rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
    omega
  · change |(-53 : ℤ) + 2 * ((bulkEdgeAnchor m F t).val 0 - (bulkEdgeAnchor 27 F 13).val 0)| <
      |-57 + 2 * ((bulkEdgeAnchor m F t).val 0 - (bulkEdgeAnchor 27 F 13).val 0)|
    have hF : bulkFarZNegativeFrame F := by simpa [BulkFarZAscendingFrame] using hf
    have hs := bulkFarZ_anchor_negative_shift m t F ht htm hF
    rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
    omega

theorem bulkFarZ_ascent_reachable (m t : ℕ) (F : OctEdgeFrame) (i : Fin 4)
    (ht : 13 ≤ t) (htm : t + 14 ≤ m) (hf : BulkFarZAscendingFrame F i) :
    (bulkFiniteGraph m).Reachable
      (bulkFarZView m t F (bulkFarZFrom i) ht htm (bulkFarZ_from_family F i hf))
      (bulkFarZView m t F (bulkFarZTo i) ht htm (bulkFarZ_to_family F i hf)) := by
  obtain ⟨hsource, htarget, hbond⟩ := bulkFarZ_reference_joint i
  have hfamily := bulkFarZ_from_family F i hf
  have hbox := bulkFarZ_reference_boxes F (bulkFarZFrom i) hfamily
  have hsegment : (bulkSiteSegmentGraph m).Reachable
      (bulkEdgeReanchor 27 m 13 t F (bulkFarZRoot (bulkFarZFrom i)))
      (bulkEdgeReanchor 27 m 13 t F (bulkFarZJointSource i)) :=
    (bulkSegmentFiniteCheck_edge_component 27 m 13 t F 5 (bulkFarZSupport (bulkFarZFrom i))
      (bulkFarZRoot (bulkFarZFrom i)) (bulkFarZRank (bulkFarZFrom i)) (by decide) (by decide)
      ht htm hbox (bulkFarZ_reference_finite (bulkFarZFrom i)) _).mp
        (Finset.mem_image.mpr ⟨_, hsource, rfl⟩)
  have hcoverReach : (bulkCoverGraph m).Reachable
      (bulkEdgeReanchor 27 m 13 t F (bulkFarZRoot (bulkFarZFrom i)))
      (bulkEdgeReanchor 27 m 13 t F (bulkFarZJointSource i)) := by
    obtain ⟨w⟩ := hsegment
    let f : bulkSiteSegmentGraph m →g bulkCoverGraph m := ⟨id, by intro a b h; exact h.1⟩
    exact ⟨w.map f⟩
  have hcover : (bulkCoverGraph m).Adj (bulkEdgeReanchor 27 m 13 t F (bulkFarZJointSource i))
      (bulkEdgeReanchor 27 m 13 t F (bulkFarZJointTarget i)) := by
    apply (mem_bulkCoverNeighbours m _ _).mp
    rw [← bulkEdgeReanchor_coverNeighbours_image 27 m 13 t F 5 _ (by decide) (by decide)
      ht htm (hbox _ hsource)]
    exact Finset.mem_image.mpr ⟨_, (mem_bulkCoverNeighbours 27 _ _).mpr
      ((bulkCoverBond_fast_iff 27 _ _).mpr hbond), rfl⟩
  apply (bulkFinite_reachable_iff m _ _).mpr
  exact hcoverReach.trans hcover.reachable

end ProteinFolding.Tetrahedral

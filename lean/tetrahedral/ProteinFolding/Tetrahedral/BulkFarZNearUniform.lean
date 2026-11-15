import ProteinFolding.Tetrahedral.BulkFarZNearValues
import ProteinFolding.Tetrahedral.BulkFarZNearRecognition
import ProteinFolding.Tetrahedral.BulkSegmentOrderTransfer

/-! The Z-edge transition rows escape uniformly by vertex transport. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def bulkFarZNearView (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6)
    (hf : BulkFarZFamily F i) : BulkVertex m :=
  ⟨bulkReanchorSite 50 m (bulkEdgeStartIndex F) (bulkFarZNearRoot F j i),
    (bulkReanchor_interior_iff 50 m (bulkEdgeStartIndex F) 31 _ (by decide) (by omega)
      (bulkFarZNear_reference_boxes F j i hf _ (bulkFarZNear_root_mem F j i))).mpr
      (bulkFarZNearReferenceView F j i hf).property⟩

theorem bulkFarZNear_ascent_potential (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (j : Fin 3)
    (i : Fin 4) (hf : BulkFarZAscendingFrame F i) :
    bulkSegmentPotential m (bulkFarZNearView m hm F j (bulkFarZFrom i) (bulkFarZ_from_family F i hf)) <
      bulkSegmentPotential m (bulkFarZNearView m hm F j (bulkFarZTo i) (bulkFarZ_to_family F i hf)) := by
  apply (bulkSegment_vertex_potential_lt_iff 50 m (bulkEdgeStartIndex F) 31
    (bulkFarZNearSupport F j (bulkFarZFrom i)) (bulkFarZNearSupport F j (bulkFarZTo i))
    (bulkFarZNearReferenceView F j (bulkFarZFrom i) (bulkFarZ_from_family F i hf))
    (bulkFarZNearReferenceView F j (bulkFarZTo i) (bulkFarZ_to_family F i hf))
    (bulkFarZNearView m hm F j (bulkFarZFrom i) (bulkFarZ_from_family F i hf))
    (bulkFarZNearView m hm F j (bulkFarZTo i) (bulkFarZ_to_family F i hf))
    (bulkFarZNearRank F j (bulkFarZFrom i)) (bulkFarZNearRank F j (bulkFarZTo i))
    (by decide) (by omega)
    (bulkFarZNear_reference_boxes F j _ (bulkFarZ_from_family F i hf))
    (bulkFarZNear_reference_boxes F j _ (bulkFarZ_to_family F i hf))
    (bulkFarZNear_reference_finite F j _ (bulkFarZ_from_family F i hf))
    (bulkFarZNear_reference_finite F j _ (bulkFarZ_to_family F i hf)) rfl rfl).mpr
  exact bulkFarZNear_reference_potential_up F j i hf

theorem bulkFarZNear_ascent_reachable (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (j : Fin 3)
    (i : Fin 4) (hf : BulkFarZAscendingFrame F i) :
    (bulkFiniteGraph m).Reachable
      (bulkFarZNearView m hm F j (bulkFarZFrom i) (bulkFarZ_from_family F i hf))
      (bulkFarZNearView m hm F j (bulkFarZTo i) (bulkFarZ_to_family F i hf)) := by
  obtain ⟨hsource, htarget, hbond⟩ := bulkFarZNear_reference_joint F j i hf
  have hfamily := bulkFarZ_from_family F i hf
  have hbox := bulkFarZNear_reference_boxes F j (bulkFarZFrom i) hfamily
  have hsegment : (bulkSiteSegmentGraph m).Reachable
      (bulkReanchorSite 50 m (bulkEdgeStartIndex F) (bulkFarZNearRoot F j (bulkFarZFrom i)))
      (bulkReanchorSite 50 m (bulkEdgeStartIndex F) (bulkFarZNearMap F j (bulkFarZJointSource i))) :=
    (bulkSegmentFiniteCheck_vertex_component 50 m (bulkEdgeStartIndex F) 31
      (bulkFarZNearSupport F j (bulkFarZFrom i)) (bulkFarZNearRoot F j (bulkFarZFrom i))
      (bulkFarZNearRank F j (bulkFarZFrom i)) (by decide) (by omega) hbox
      (bulkFarZNear_reference_finite F j _ hfamily) _).mp (Finset.mem_image.mpr ⟨_, hsource, rfl⟩)
  have hcoverReach : (bulkCoverGraph m).Reachable
      (bulkReanchorSite 50 m (bulkEdgeStartIndex F) (bulkFarZNearRoot F j (bulkFarZFrom i)))
      (bulkReanchorSite 50 m (bulkEdgeStartIndex F) (bulkFarZNearMap F j (bulkFarZJointSource i))) := by
    obtain ⟨w⟩ := hsegment
    let f : bulkSiteSegmentGraph m →g bulkCoverGraph m := ⟨id, by intro a b h; exact h.1⟩
    exact ⟨w.map f⟩
  have hcover : (bulkCoverGraph m).Adj
      (bulkReanchorSite 50 m (bulkEdgeStartIndex F) (bulkFarZNearMap F j (bulkFarZJointSource i)))
      (bulkReanchorSite 50 m (bulkEdgeStartIndex F) (bulkFarZNearMap F j (bulkFarZJointTarget i))) := by
    apply (mem_bulkCoverNeighbours m _ _).mp
    rw [← bulkReanchor_coverNeighbours_image 50 m (bulkEdgeStartIndex F) 31 _
      (by decide) (by omega) (hbox _ hsource)]
    exact Finset.mem_image.mpr ⟨_, (mem_bulkCoverNeighbours 50 _ _).mpr
      ((bulkCoverBond_fast_iff 50 _ _).mpr hbond), rfl⟩
  apply (bulkFinite_reachable_iff m _ _).mpr
  exact hcoverReach.trans hcover.reachable

theorem bulkFarZNear_candidate_box (m : ℕ) (F : OctEdgeFrame) (j : Fin 3) (odd : Bool)
    (d : Fin 4) (hm : 1 ≤ m) : InBulkVertexBox m (bulkEdgeStartIndex F) 26
      (bulkEdgeCandidate m F (bulkFarZNearT j) odd d hm) := by
  have hb := bulkEdgeZigzag_in_start_box m F (2 * bulkFarZNearT j)
  have hj : bulkFarZNearT j ≤ 12 := by unfold bulkFarZNearT; omega
  cases odd
  · simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor]
    exact bulkVertexBox_mono m (bulkEdgeStartIndex F) (by omega)
      (bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) _ hb (step_adj _ d))
  · simp only [bulkEdgeCandidate, bulkClosedEdgeAnchor_eq, bulkEdgeAnchor]
    exact bulkVertexBox_mono m (bulkEdgeStartIndex F) (by omega)
      (bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) _
        (bulk_adjacent_in_vertex_box m (bulkEdgeStartIndex F) _ hb (step_adj _ F.a)) (step_adj _ d))

end ProteinFolding.Tetrahedral

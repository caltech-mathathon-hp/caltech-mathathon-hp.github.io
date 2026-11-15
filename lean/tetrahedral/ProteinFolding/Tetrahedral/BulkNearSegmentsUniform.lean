import ProteinFolding.Tetrahedral.BulkNearSegmentsReference
import ProteinFolding.Tetrahedral.BulkSegmentOrderTransfer

/-! Uniform transport of the complete near-vertex segment supports. Membership
in the finite translated support is equivalent to ambient segment reachability. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def bulkNearSegmentPointView (m : ℕ) (hm : 50 ≤ m) (i : Fin 234)
    (p : Site) (hp : p ∈ bulkNearSegmentSupport i) : BulkVertex m :=
  ⟨bulkReanchorSite 50 m (bulkNearSegmentVertex i) p,
    (bulkReanchor_interior_iff 50 m (bulkNearSegmentVertex i) 43 p (by decide) (by omega)
      (bulkNearSegment_reference_box i p hp)).mpr
        ((bulkInterior_fast_iff 50 p).mpr
          ((bulkNearSegment_reference_certificate i).2.1 p hp))⟩

def bulkNearSegmentRootView (m : ℕ) (hm : 50 ≤ m) (i : Fin 234) : BulkVertex m :=
  bulkNearSegmentPointView m hm i (bulkNearSegmentRoot i)
    (bulkNearSegment_reference_certificate i).1

theorem bulkNearSegment_uniform_component (m : ℕ) (hm : 50 ≤ m)
    (i : Fin 234) (p : Site) :
    p ∈ (bulkNearSegmentSupport i).image (bulkReanchorSite 50 m (bulkNearSegmentVertex i)) ↔
      (bulkSiteSegmentGraph m).Reachable (bulkNearSegmentRootView m hm i).val p :=
  bulkSegmentFiniteCheck_vertex_component 50 m (bulkNearSegmentVertex i) 43
    (bulkNearSegmentSupport i) (bulkNearSegmentRoot i) (bulkNearSegmentRank i)
    (by decide) hm (bulkNearSegment_reference_box i)
    (bulkNearSegment_reference_certificate i) p

theorem bulkNearSegment_point_reachable (m : ℕ) (hm : 50 ≤ m) (i : Fin 234)
    (p : Site) (hp : p ∈ bulkNearSegmentSupport i) :
    (bulkSegmentGraph m).Reachable (bulkNearSegmentRootView m hm i)
      (bulkNearSegmentPointView m hm i p hp) := by
  apply (bulkSegment_reachable_iff_site m _ _).mpr
  exact (bulkNearSegment_uniform_component m hm i _).mp
    (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

theorem bulkNearSegment_point_potential (m : ℕ) (hm : 50 ≤ m) (i : Fin 234)
    (p : Site) (hp : p ∈ bulkNearSegmentSupport i) :
    bulkSegmentPotential m (bulkNearSegmentRootView m hm i) =
      bulkSegmentPotential m (bulkNearSegmentPointView m hm i p hp) :=
  bulkSegmentPotential_eq m (bulkNearSegment_point_reachable m hm i p hp)

theorem bulkNearSegment_points_cover_reachable (m : ℕ) (hm : 50 ≤ m) (i : Fin 234)
    (p q : Site) (hp : p ∈ bulkNearSegmentSupport i) (hq : q ∈ bulkNearSegmentSupport i) :
    (bulkFiniteGraph m).Reachable (bulkNearSegmentPointView m hm i p hp)
      (bulkNearSegmentPointView m hm i q hq) :=
  bulkSegment_reachable_cover m
    ((bulkNearSegment_point_reachable m hm i p hp).symm.trans
      (bulkNearSegment_point_reachable m hm i q hq))

theorem bulkNearSegment_uniform_potential_lt (m : ℕ) (hm : 50 ≤ m) (i j : Fin 234)
    (hv : bulkNearSegmentVertex j = bulkNearSegmentVertex i)
    (hlt : bulkNearReferencePotential i < bulkNearReferencePotential j) :
    bulkSegmentPotential m (bulkNearSegmentRootView m hm i) <
      bulkSegmentPotential m (bulkNearSegmentRootView m hm j) := by
  apply (bulkSegment_vertex_potential_lt_iff 50 m (bulkNearSegmentVertex i) 43
    (bulkNearSegmentSupport i) (bulkNearSegmentSupport j)
    (bulkNearSegmentReferenceView i) (bulkNearSegmentReferenceView j)
    (bulkNearSegmentRootView m hm i) (bulkNearSegmentRootView m hm j)
    (bulkNearSegmentRank i) (bulkNearSegmentRank j) (by decide) hm
    (bulkNearSegment_reference_box i) (by simpa only [hv] using bulkNearSegment_reference_box j)
    (bulkNearSegment_reference_certificate i) (bulkNearSegment_reference_certificate j)
    rfl (by
      change bulkReanchorSite 50 m (bulkNearSegmentVertex j) _ = _
      rw [hv]
      rfl)).mpr
  simpa only [bulkNearSegment_reference_potential] using hlt

end ProteinFolding.Tetrahedral

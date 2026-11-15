import ProteinFolding.Tetrahedral.BulkJointSlabs

/-! A class-Z joint in the class-X slab is near a y-vertex; a
negative-alpha class-Z joint is near an x-vertex. These alternatives
exclude mixed and negative class-Z far segments geometrically. -/

namespace ProteinFolding.Tetrahedral

theorem bulkEdgeCandidate_joint_in_anchor_box {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (t : ℕ) (odd : Bool) (d : Fin 4) (p : Site)
    (hp : p = bulkEdgeCandidate m F t odd d hm ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p) :
    InBulkEdgeBox m F t 3 p := by
  have hb := bulkEdgeCandidate_in_box m F t odd d hm
  rcases hp with rfl | hp
  · intro k
    have h := hb k
    omega
  · intro k
    have h := abs_le.mp (hb k)
    have hs := adj_coordinate hp k
    rw [abs_le]
    constructor <;> omega

set_option maxHeartbeats 1200000 in
theorem bulkZEdge_box_small_x_near_vertex {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (t D B : ℕ) (p : Site) (hF : BulkZEdgeFrame F) (hp : InBulkEdgeBox m F t D p)
    (hx : |p.val 0| ≤ (B : ℤ)) : ∃ v : Fin 6, InBulkVertexBox m v (B + 2 * D) p := by
  have hx' := abs_le.mp hx
  have h0 := abs_le.mp (hp 0)
  have h1 := abs_le.mp (hp 1)
  have h2 := abs_le.mp (hp 2)
  have hz := bulkEdgeAnchor_z_of_Z hm F t hF
  have hk := (bulkEdgeAnchor_faces hm F t).1
  rcases hF with ⟨h0F, h1F⟩ | ⟨h0F, h1F⟩ | ⟨h0F, h1F⟩ | ⟨h0F, h1F⟩
  · refine ⟨4, ?_⟩
    rw [h0F] at hk
    intro k
    fin_cases k <;> dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre,
      tetraCoordinate] at hk ⊢ <;> rw [abs_le] <;> constructor <;> omega
  · refine ⟨1, ?_⟩
    rw [h0F] at hk
    intro k
    fin_cases k <;> dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre,
      tetraCoordinate] at hk ⊢ <;> rw [abs_le] <;> constructor <;> omega
  · refine ⟨1, ?_⟩
    rw [h0F] at hk
    intro k
    fin_cases k <;> dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre,
      tetraCoordinate] at hk ⊢ <;> rw [abs_le] <;> constructor <;> omega
  · refine ⟨4, ?_⟩
    rw [h0F] at hk
    intro k
    fin_cases k <;> dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre,
      tetraCoordinate] at hk ⊢ <;> rw [abs_le] <;> constructor <;> omega

set_option maxHeartbeats 1200000 in
theorem bulkZEdge_box_small_Y_near_vertex {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (t D B : ℕ) (p : Site) (hF : BulkZEdgeFrame F) (hp : InBulkEdgeBox m F t D p)
    (hy : |bulkY m p| ≤ (B : ℤ)) : ∃ v : Fin 6, InBulkVertexBox m v (B + 2 * D) p := by
  have hy' := abs_le.mp hy
  have h0 := abs_le.mp (hp 0)
  have h1 := abs_le.mp (hp 1)
  have h2 := abs_le.mp (hp 2)
  have hz := bulkEdgeAnchor_z_of_Z hm F t hF
  have hk := (bulkEdgeAnchor_faces hm F t).1
  dsimp only [bulkY] at hy'
  rcases hF with ⟨h0F, h1F⟩ | ⟨h0F, h1F⟩ | ⟨h0F, h1F⟩ | ⟨h0F, h1F⟩
  · refine ⟨5, ?_⟩
    rw [h0F] at hk
    intro k
    fin_cases k <;> dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre,
      tetraCoordinate] at hk ⊢ <;> rw [abs_le] <;> constructor <;> omega
  · refine ⟨0, ?_⟩
    rw [h0F] at hk
    intro k
    fin_cases k <;> dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre,
      tetraCoordinate] at hk ⊢ <;> rw [abs_le] <;> constructor <;> omega
  · refine ⟨5, ?_⟩
    rw [h0F] at hk
    intro k
    fin_cases k <;> dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre,
      tetraCoordinate] at hk ⊢ <;> rw [abs_le] <;> constructor <;> omega
  · refine ⟨0, ?_⟩
    rw [h0F] at hk
    intro k
    fin_cases k <;> dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre,
      tetraCoordinate] at hk ⊢ <;> rw [abs_le] <;> constructor <;> omega

theorem bulkZJoint_in_x_slab_near_vertex {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (t : ℕ) (odd : Bool) (d : Fin 4) (p : Site) (hF : BulkZEdgeFrame F)
    (hp : p = bulkEdgeCandidate m F t odd d hm ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p)
    (hx : |p.val 0| ≤ 5) : ∃ v : Fin 6, InBulkVertexBox m v 11 p :=
  bulkZEdge_box_small_x_near_vertex hm F t 3 5 p hF
    (bulkEdgeCandidate_joint_in_anchor_box hm F t odd d p hp) hx

theorem bulkZJoint_negative_near_vertex {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (t : ℕ) (odd : Bool) (d : Fin 4) (p : Site) (hF : BulkZEdgeFrame F)
    (hp : p = bulkEdgeCandidate m F t odd d hm ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p)
    (hα : bulkAlpha m p < 0) : ∃ v : Fin 6, InBulkVertexBox m v 9 p := by
  have hz := bulkEdgeCandidate_joint_z_bound hm F t odd d hF p hp
  have hy : |bulkY m p| ≤ 3 := by unfold bulkAlpha at hα; omega
  exact bulkZEdge_box_small_Y_near_vertex hm F t 3 3 p hF
    (bulkEdgeCandidate_joint_in_anchor_box hm F t odd d p hp) hy

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.BulkFarJointGeometry

/-! A moderately negative-alpha joint in the narrow X slab must belong
to an X-plane edge. This also excludes all small vertex patches there. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def BulkYEdgeFrame (F : OctEdgeFrame) : Prop :=
  (F.k = 0 ∧ F.j = 2) ∨ (F.k = 2 ∧ F.j = 0) ∨
    (F.k = 1 ∧ F.j = 3) ∨ (F.k = 3 ∧ F.j = 1)

theorem bulkEdgeFrame_plane_cases (F : OctEdgeFrame) :
    BulkXEdgeFrame F ∨ BulkYEdgeFrame F ∨ BulkZEdgeFrame F := by
  have hne := F.kj
  rcases F with ⟨k, j, a, b, hkj, hka, hkb, hja, hjb, hab⟩
  fin_cases k <;> fin_cases j <;> simp_all [BulkXEdgeFrame, BulkYEdgeFrame, BulkZEdgeFrame]

theorem bulkEdgeAnchor_Y_of_Y {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (hF : BulkYEdgeFrame F) : bulkY m (bulkEdgeAnchor m F t) = 0 := by
  have hk := (bulkEdgeAnchor_faces hm F t).1
  have hj := (bulkEdgeAnchor_faces hm F t).2.1
  rcases hF with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  all_goals rw [h0] at hk; rw [h1] at hj
  all_goals dsimp [tetraCoordinate, bulkY] at hk hj ⊢; omega

theorem bulkNegative_moderate_not_vertex_box (m : ℕ) (hm : 50 ≤ m) (p : Site)
    (hx : |p.val 0| ≤ 6) (hα : bulkAlpha m p < 0) (hbound : |bulkAlpha m p| ≤ octRadius m - 35)
    (v : Fin 6) : ¬InBulkVertexBox m v 9 p := by
  intro hbox
  have h0 := abs_le.mp (hbox 0)
  have h1 := abs_le.mp (hbox 1)
  have h2 := abs_le.mp (hbox 2)
  have hx' := abs_le.mp hx
  have hbound' := abs_le.mp hbound
  unfold bulkAlpha at hα hbound'
  rcases le_total 0 (bulkY m p) with hy | hy <;> rcases le_total 0 (bulkZ p) with hz | hz
  all_goals first | rw [abs_of_nonneg hy] at hα hbound' | rw [abs_of_nonpos hy] at hα hbound'
  all_goals first | rw [abs_of_nonneg hz] at hα hbound' | rw [abs_of_nonpos hz] at hα hbound'
  all_goals fin_cases v
  all_goals dsimp [bulkPatchVertex, octVertexSite, octVertexCoordinates, octCentre, bulkY, bulkZ, octRadius] at *
  all_goals omega

theorem bulkNegative_moderate_joint_frame_X (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (p : Site)
    (hp : p = bulkEdgeCandidate m F t odd d hOne ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hOne) p)
    (hx : |p.val 0| ≤ 6) (hα : bulkAlpha m p < 0) (hbound : |bulkAlpha m p| ≤ octRadius m - 35) :
    BulkXEdgeFrame F := by
  rcases bulkEdgeFrame_plane_cases F with hX | hY | hZ
  · exact hX
  · have hbox := bulkEdgeCandidate_joint_in_anchor_box hOne F t odd d p hp
    have hAnchorY := bulkEdgeAnchor_Y_of_Y hOne F t hY
    have h0 := abs_le.mp (hbox 0)
    have h1 := abs_le.mp (hbox 1)
    have h2 := abs_le.mp (hbox 2)
    have hx' := abs_le.mp hx
    have hYA : |bulkY m p| ≤ 3 := by
      rw [abs_le]
      dsimp only [bulkY] at hAnchorY ⊢
      constructor <;> omega
    rw [abs_of_neg hα] at hbound
    unfold bulkAlpha at hbound
    have hZA : |bulkZ p| ≤ octRadius m - 32 := by omega
    have hZA' := abs_le.mp hZA
    have hk := (bulkEdgeAnchor_faces hOne F t).1
    dsimp only [bulkY] at hAnchorY
    dsimp only [bulkZ] at hZA'
    rcases hY with ⟨h0F, _⟩ | ⟨h0F, _⟩ | ⟨h0F, _⟩ | ⟨h0F, _⟩
    all_goals rw [h0F] at hk
    all_goals dsimp [tetraCoordinate] at hk
    all_goals omega
  · obtain ⟨v, hv⟩ := bulkZJoint_negative_near_vertex hOne F t odd d p hZ hp hα
    exact (bulkNegative_moderate_not_vertex_box m hm p hx hα hbound v hv).elim

end ProteinFolding.Tetrahedral

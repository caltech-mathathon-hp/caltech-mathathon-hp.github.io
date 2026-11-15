import ProteinFolding.Tetrahedral.BulkFarJointGeometry
import ProteinFolding.Tetrahedral.BulkFoliationParity

/-! Far two-joint segments are uniformly of class X, or of class Z
with positive alpha. The assertions concern actual candidate endpoints. -/

namespace ProteinFolding.Tetrahedral

def BulkXJointEndpoint (m : ℕ) (hm : 1 ≤ m) (p : Site) : Prop :=
  ∃ (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4), BulkXEdgeFrame F ∧
    bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m ∧
    (p = bulkEdgeCandidate m F t odd d hm ∨ tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p)

def BulkZJointEndpoint (m : ℕ) (hm : 1 ≤ m) (p : Site) : Prop :=
  ∃ (F : OctEdgeFrame) (t : ℕ) (odd : Bool) (d : Fin 4), BulkZEdgeFrame F ∧
    bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m ∧
    (p = bulkEdgeCandidate m F t odd d hm ∨ tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p)

def BulkFarFromVertices (m : ℕ) (p : Site) : Prop := ∀ v : Fin 6, ¬InBulkVertexBox m v 12 p

theorem bulkFarCandidate_joint_class {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (p : Site) (ht : 10 ≤ t) (htm : t + 11 ≤ m)
    (hd : bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m)
    (hp : p = bulkEdgeCandidate m F t odd d hm ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p) :
    BulkXJointEndpoint m hm p ∨ BulkZJointEndpoint m hm p := by
  rcases bulkFarEdge_damaged_plane m F t odd d hm ht htm hd with hX | hZ
  · exact Or.inl ⟨F, t, odd, d, hX, hd, hp⟩
  · exact Or.inr ⟨F, t, odd, d, hZ, hd, hp⟩

theorem bulkFarZJoint_alpha_positive {m : ℕ} (hm : 1 ≤ m) (p : Site)
    (hp : BulkZJointEndpoint m hm p) (hfar : BulkFarFromVertices m p) : 0 < bulkAlpha m p := by
  rcases bulkAlpha_signed m p with hneg | hpos
  · obtain ⟨F, t, odd, d, hZ, _, hendpoint⟩ := hp
    obtain ⟨v, hv⟩ := bulkZJoint_negative_near_vertex hm F t odd d p hZ hendpoint hneg
    exact (hfar v (bulkVertexBox_mono m v (by decide : 9 ≤ 12) hv)).elim
  · exact hpos

theorem bulkFar_joint_classes_agree {m : ℕ} (hm : 1 ≤ m) (p q : BulkVertex m)
    (hline : (bulkSegmentGraph m).Reachable p q)
    (hp : BulkXJointEndpoint m hm p.val ∨ BulkZJointEndpoint m hm p.val)
    (hq : BulkXJointEndpoint m hm q.val ∨ BulkZJointEndpoint m hm q.val)
    (hfarP : BulkFarFromVertices m p.val) (hfarQ : BulkFarFromVertices m q.val) :
    (BulkXJointEndpoint m hm p.val ∧ BulkXJointEndpoint m hm q.val) ∨
      (BulkZJointEndpoint m hm p.val ∧ BulkZJointEndpoint m hm q.val ∧ 0 < bulkAlpha m p.val) := by
  rcases hp with hpX | hpZ <;> rcases hq with hqX | hqZ
  · exact Or.inl ⟨hpX, hqX⟩
  · obtain ⟨F, t, odd, d, hX, _, hendpoint⟩ := hpX
    have hslab := bulkSegment_joint_x_slab hm F t odd d hX p q hendpoint hline
    obtain ⟨G, u, oddQ, e, hZ, _, hendpointQ⟩ := hqZ
    obtain ⟨v, hv⟩ := bulkZJoint_in_x_slab_near_vertex hm G u oddQ e q.val hZ hendpointQ hslab
    exact (hfarQ v (bulkVertexBox_mono m v (by decide : 11 ≤ 12) hv)).elim
  · obtain ⟨F, t, odd, d, hX, _, hendpoint⟩ := hqX
    have hslab := bulkSegment_joint_x_slab hm F t odd d hX q p hendpoint hline.symm
    obtain ⟨G, u, oddP, e, hZ, _, hendpointP⟩ := hpZ
    obtain ⟨v, hv⟩ := bulkZJoint_in_x_slab_near_vertex hm G u oddP e p.val hZ hendpointP hslab
    exact (hfarP v (bulkVertexBox_mono m v (by decide : 11 ≤ 12) hv)).elim
  · exact Or.inr ⟨hpZ, hqZ, bulkFarZJoint_alpha_positive hm p.val hpZ hfarP⟩

end ProteinFolding.Tetrahedral

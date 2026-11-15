import ProteinFolding.Tetrahedral.BulkJointPlanes
import ProteinFolding.Tetrahedral.BulkSegmentLocalBounds

/-! The endpoints of a class-X merge lie in the slab |X| <= 3;
their entire rung segment lies in |X| <= 5. Class-Z endpoints satisfy
|Z| <= 4. These are uniform bounds for actual candidate coordinates. -/

namespace ProteinFolding.Tetrahedral

theorem bulkEdgeCandidate_joint_x_bound {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (t : ℕ) (odd : Bool) (d : Fin 4) (hF : BulkXEdgeFrame F) (p : Site)
    (hp : p = bulkEdgeCandidate m F t odd d hm ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p) : |p.val 0| ≤ 3 := by
  have hb := abs_le.mp (bulkEdgeCandidate_x_bound hm F t odd d hF)
  rcases hp with rfl | hp
  · rw [abs_le]
    constructor <;> omega
  · have hstep := adj_coordinate hp 0
    rw [abs_le]
    constructor <;> omega

theorem bulkEdgeCandidate_joint_z_bound {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (t : ℕ) (odd : Bool) (d : Fin 4) (hF : BulkZEdgeFrame F) (p : Site)
    (hp : p = bulkEdgeCandidate m F t odd d hm ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p) : |bulkZ p| ≤ 4 := by
  have hb := abs_le.mp (bulkEdgeCandidate_z_bound hm F t odd d hF)
  rcases hp with rfl | hp
  · rw [abs_le]
    constructor <;> omega
  · have hstep := adj_coordinate hp 2
    rw [abs_le]
    dsimp only [bulkZ] at hb ⊢
    constructor <;> omega

theorem bulkSegment_joint_x_slab {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (t : ℕ) (odd : Bool) (d : Fin 4) (hF : BulkXEdgeFrame F) (p q : BulkVertex m)
    (hp : p.val = bulkEdgeCandidate m F t odd d hm ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p.val)
    (h : (bulkSegmentGraph m).Reachable p q) : |q.val.val 0| ≤ 5 := by
  exact bulkSegment_x_bound_of_site m 3 h
    (bulkEdgeCandidate_joint_x_bound hm F t odd d hF p.val hp)

end ProteinFolding.Tetrahedral

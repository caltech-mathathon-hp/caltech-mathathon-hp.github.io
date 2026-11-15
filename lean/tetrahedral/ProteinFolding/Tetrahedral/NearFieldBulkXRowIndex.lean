import ProteinFolding.Tetrahedral.NearFieldBulkXRows

/-! An occupied second-row site has an anchor within the finite edge range. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem xRowSite_index_bound (m : ℕ) (hm : 1 ≤ m) (k : Fin 4)
    (reverse small : Bool) (t : ℕ) (hp : InOctahedron m (xRowSite m hm k reverse small t)) :
    t + 1 ≤ m := by
  let F := xRowFrame k reverse
  have hu := (hp F.a).2
  have hA := bulkEdgeAnchor_inA m F t
  have ha := (bulkEdgeAnchor_faces hm F t).2.2.1
  simp only [xRowSite, bulkClosedEdgeAnchor_eq] at hu
  cases small
  · change tetraCoordinate m (step (step (bulkEdgeAnchor m F t) F.j) F.b).val F.a ≤ octRadius m at hu
    rw [tetraCoordinate_step_B m (step_in_B hA F.j), tetraCoordinate_step_A m hA] at hu
    simp only [if_neg F.ab, if_neg (Ne.symm F.ja)] at hu
    rw [ha] at hu
    dsimp [octRadius] at hu
    omega
  · change tetraCoordinate m (step (step (step (bulkEdgeAnchor m F t) F.a) F.k) F.a).val F.a ≤ octRadius m at hu
    rw [tetraCoordinate_step_A m (step_in_A (step_in_B hA F.a) F.k),
      tetraCoordinate_step_B m (step_in_B hA F.a), tetraCoordinate_step_A m hA] at hu
    simp only [ite_true, if_neg (Ne.symm F.ka)] at hu
    rw [ha] at hu
    dsimp [octRadius] at hu
    omega

end ProteinFolding.Tetrahedral.NearField

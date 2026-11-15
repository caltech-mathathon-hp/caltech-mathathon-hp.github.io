import ProteinFolding.Cubic.Proofs.PackingGeometryWalls

/-! Backbone length bounds for the short links between J's E_2 blocks.
A link shorter than the separation of two nonincident rails cannot switch rails. -/

namespace ProteinFolding.CubicPackingGeometry

theorem latticeDistance_triangle (p q r : Site) :
    latticeDistance p r ≤ latticeDistance p q + latticeDistance q r := by
  unfold latticeDistance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  have h := Int.natAbs_add_le (p k - q k) (q k - r k)
  rw [show (p k - q k) + (q k - r k) = p k - r k by omega] at h
  exact h

theorem walk_distance_le (p : ℕ → Site) (N : ℕ)
    (hstep : ∀ j, j < N → cubicLattice.Adj (p j) (p (j + 1))) :
    latticeDistance (p 0) (p N) ≤ N := by
  induction N with
  | zero => simp [latticeDistance]
  | succ N ih =>
    have hp := ih (by intro j hj; exact hstep j (by omega))
    have ht := latticeDistance_triangle (p 0) (p N) (p (N + 1))
    have hu : latticeDistance (p N) (p (N + 1)) = 1 := hstep N (by omega)
    omega

theorem fold_segment_distance_le {N : ℕ} (f : Fold cubicLattice N) (i j : Fin N)
    (hij : i.val ≤ j.val) : latticeDistance (f.pos i) (f.pos j) ≤ j.val - i.val := by
  let p : ℕ → Site := fun k => if h : i.val + k < N then f.pos ⟨i.val + k, h⟩ else f.pos i
  have hs : ∀ k, k < j.val - i.val → cubicLattice.Adj (p k) (p (k + 1)) := by
    intro k hk
    have h0 : i.val + k < N := by have := j.isLt; omega
    have h1 : i.val + (k + 1) < N := by have := j.isLt; omega
    simp only [p, dif_pos h0, dif_pos h1]
    apply f.consecutive
    dsimp
    omega
  have h := walk_distance_le p (j.val - i.val) hs
  have he : i.val + (j.val - i.val) = j.val := by omega
  simpa only [p, Nat.add_zero, dif_pos i.isLt, he, dif_pos j.isLt] using h

/-- Every sufficiently short backbone link between vertices on a matching
family of rails keeps the same rail. Used with 4Q+7 < d+1 for the J word. -/
theorem short_fold_link_same_rail (a : Site) (d : ℕ) (rails : Finset CubeEdge)
    (hmatching : ∀ bits, (incidentEdges bits ∩ rails).card ≤ 1)
    (e g : CubeEdge) (he : e ∈ rails) (hg : g ∈ rails) (r s : Fin d)
    {N : ℕ} (f : Fold cubicLattice N) (i j : Fin N) (hij : i.val ≤ j.val)
    (hpi : f.pos i = openEdgePoint a d e r) (hpj : f.pos j = openEdgePoint a d g s)
    (hshort : j.val - i.val < d + 1) : e = g := by
  by_contra hne
  have hnc := noCommonCorner_of_matching rails hmatching e g he hg hne
  have hlower := nonincident_edges_distance a d e g r s hnc
  have hupper := fold_segment_distance_le f i j hij
  rw [hpi, hpj] at hupper
  omega

end ProteinFolding.CubicPackingGeometry

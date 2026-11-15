import ProteinFolding.Cubic.Proofs.PackingGeometryWalls

/-! A wall crossing has exactly d+1 compressed H steps between its two rail
anchors. Nonincident rails are already d+1 apart, so the entire crossing is
straight. This does not assume an orientation of the successful fold. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicCertificates

def negateSite (p : Site) : Site := fun k => -p k

theorem distance_negateSite (p q : Site) : latticeDistance (negateSite p) (negateSite q) =
    latticeDistance p q := by
  apply Finset.sum_congr rfl
  intro k _
  change (-p k - -q k).natAbs = (p k - q k).natAbs
  rw [show -p k - -q k = -(p k - q k) by omega, Int.natAbs_neg]

theorem negateSite_adj {p q : Site} (h : cubicLattice.Adj p q) :
    cubicLattice.Adj (negateSite p) (negateSite q) := by
  change latticeDistance (negateSite p) (negateSite q) = 1
  rw [distance_negateSite]
  exact h

theorem walk_min_axis_straight (p : ℕ → Site) (N : ℕ) (axis : Fin 3)
    (hstep : ∀ j, j < N → cubicLattice.Adj (p j) (p (j + 1)))
    (hend : p N axis = p 0 axis - (N : ℤ)) :
    ∀ i, i ≤ N → p i = Function.update (p 0) axis (p 0 axis - (i : ℤ)) := by
  have hsteps : ∀ j, j < N → cubicLattice.Adj (negateSite (p j)) (negateSite (p (j + 1))) := by
    intro j hj
    exact negateSite_adj (hstep j hj)
  have he : negateSite (p N) axis = negateSite (p 0) axis + (N : ℤ) := by
    dsimp only [negateSite]
    omega
  have h := walk_max_axis_straight (fun i => negateSite (p i)) N axis hsteps he
  intro i hi
  funext k
  have hk := congrFun (h i hi) k
  by_cases hka : k = axis
  · subst k
    simp only [negateSite, Function.update_self] at hk ⊢
    omega
  · simp only [negateSite, Function.update_of_ne hka] at hk ⊢
    omega

theorem endValue_opposite_difference (base : ℤ) (d : ℕ) (b c : Fin 2) (hbc : b ≠ c) :
    endValue base d c = endValue base d b + ((d + 1 : ℕ) : ℤ) ∨
      endValue base d c = endValue base d b - ((d + 1 : ℕ) : ℤ) := by
  fin_cases b <;> fin_cases c <;>
    simp only [endValue, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul] at hbc ⊢ <;>
    first | exact False.elim (hbc rfl) | omega

/-- No turn or detour is possible in a d+1-step crossing between nonincident
open edges: every intermediate site lies on one straight lattice row. -/
theorem nonincident_crossing_straight (a : Site) (d : ℕ) (e f : CubeEdge)
    (r s : Fin d) (hnc : NoCommonCorner e f) (p : ℕ → Site)
    (hstart : p 0 = openEdgePoint a d e r) (hend : p (d + 1) = openEdgePoint a d f s)
    (hstep : ∀ j, j < d + 1 → cubicLattice.Adj (p j) (p (j + 1))) :
    ∃ axis : Fin 3, axis ≠ e.axis ∧ axis ≠ f.axis ∧
      ((∀ i, i ≤ d + 1 → p i = Function.update (p 0) axis (p 0 axis + (i : ℤ))) ∨
       (∀ i, i ≤ d + 1 → p i = Function.update (p 0) axis (p 0 axis - (i : ℤ)))) := by
  obtain ⟨axis, hke, hkf, hside⟩ := nonincident_separating_coordinate e f hnc
  have hcoord : p (d + 1) axis = p 0 axis + ((d + 1 : ℕ) : ℤ) ∨
      p (d + 1) axis = p 0 axis - ((d + 1 : ℕ) : ℤ) := by
    rw [hstart, hend, openEdgePoint_fixed a d e r axis hke, openEdgePoint_fixed a d f s axis hkf]
    exact endValue_opposite_difference (a axis) d _ _ hside
  refine ⟨axis, hke, hkf, ?_⟩
  rcases hcoord with hcoord | hcoord
  · exact Or.inl (walk_max_axis_straight p (d + 1) axis hstep hcoord)
  · exact Or.inr (walk_min_axis_straight p (d + 1) axis hstep hcoord)

/-- Confinement of the surface path identifies a common face; nonincident
anchors on that face must be its parallel opposite edges. -/
theorem crossing_rails_parallel (a : Site) (d : ℕ) (e f : CubeEdge) (r s : Fin d)
    (hnc : NoCommonCorner e f) (normal : Fin 3) (upper : Bool) (first last : Site)
    (hfirst : FaceInterior a (d + 2) normal upper first)
    (hlast : FaceInterior a (d + 2) normal upper last)
    (ha : cubicLattice.Adj first (openEdgePoint a d e r))
    (hb : cubicLattice.Adj last (openEdgePoint a d f s)) : e.axis = f.axis :=
  nonincident_coplanar_parallel e f normal (faceSide upper) hnc
    (face_neighbour_edge_on_face hfirst e r ha) (face_neighbour_edge_on_face hlast f s hb)

end ProteinFolding.CubicPackingGeometry

import ProteinFolding.Cubic.Proofs.PackingGeometryMatching

/-! Local geometry of the two packing rails. Nonincident cube edges are at
least d+1 apart; when they bound one face they are parallel opposite sides. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicCertificates

def fixedSide (e : CubeEdge) (k : Fin 3) : Fin 2 :=
  if k = 0 then e.first else if k = 1 then
    if e.axis = 0 then e.first else e.second
  else e.second

def NoCommonCorner (e f : CubeEdge) : Prop :=
  ∀ bits : Fin 3 → Fin 2, e ∈ incidentEdges bits → f ∉ incidentEdges bits

instance (e f : CubeEdge) : Decidable (NoCommonCorner e f) :=
  inferInstanceAs (Decidable (∀ bits : Fin 3 → Fin 2, e ∈ incidentEdges bits → f ∉ incidentEdges bits))

def EdgeOnFace (e : CubeEdge) (normal : Fin 3) (side : Fin 2) : Prop :=
  normal ≠ e.axis ∧ fixedSide e normal = side

instance (e : CubeEdge) (normal : Fin 3) (side : Fin 2) : Decidable (EdgeOnFace e normal side) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- This is a finite statement about the twelve edges of the abstract cube. -/
theorem nonincident_separating_coordinate : ∀ e f : CubeEdge,
    NoCommonCorner e f → ∃ k : Fin 3,
      k ≠ e.axis ∧ k ≠ f.axis ∧ fixedSide e k ≠ fixedSide f k := by
  decide

/-- Two nonincident geometric edges on one cube face are its opposite sides. -/
theorem nonincident_coplanar_parallel : ∀ e f : CubeEdge, ∀ normal : Fin 3, ∀ side : Fin 2,
    NoCommonCorner e f → EdgeOnFace e normal side → EdgeOnFace f normal side →
      e.axis = f.axis := by
  decide

theorem noCommonCorner_of_matching (edges : Finset CubeEdge)
    (hmatching : ∀ bits, (incidentEdges bits ∩ edges).card ≤ 1)
    (e f : CubeEdge) (he : e ∈ edges) (hf : f ∈ edges) (hef : e ≠ f) : NoCommonCorner e f := by
  intro bits hei hfi
  have heq := (Finset.card_le_one.mp (hmatching bits)) e (Finset.mem_inter.mpr ⟨hei, he⟩)
    f (Finset.mem_inter.mpr ⟨hfi, hf⟩)
  exact hef heq

theorem openEdgePoint_fixed (a : Site) (d : ℕ) (e : CubeEdge) (r : Fin d)
    (k : Fin 3) (hk : k ≠ e.axis) :
    openEdgePoint a d e r k = endValue (a k) d (fixedSide e k) := by
  obtain ⟨axis, b, c⟩ := e
  fin_cases axis <;> fin_cases k
  all_goals simp only [Fin.reduceFinMk] at hk ⊢
  all_goals first | exact False.elim (hk rfl) | simp [openEdgePoint, fixedSide]

theorem endValue_distance_of_ne (base : ℤ) (d : ℕ) (b c : Fin 2) (hbc : b ≠ c) :
    (endValue base d b - endValue base d c).natAbs = d + 1 := by
  fin_cases b <;> fin_cases c <;>
    simp only [endValue, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul] at hbc ⊢ <;>
    first | exact False.elim (hbc rfl) | omega

theorem coordinate_distance_le (p q : Site) (k : Fin 3) :
    (p k - q k).natAbs ≤ latticeDistance p q := by
  rw [distance_eq]
  fin_cases k <;> simp only [Fin.reduceFinMk] <;> omega

theorem nonincident_edges_distance (a : Site) (d : ℕ) (e f : CubeEdge)
    (r s : Fin d) (hnc : NoCommonCorner e f) :
    d + 1 ≤ latticeDistance (openEdgePoint a d e r) (openEdgePoint a d f s) := by
  obtain ⟨k, hke, hkf, hside⟩ := nonincident_separating_coordinate e f hnc
  have h := coordinate_distance_le (openEdgePoint a d e r) (openEdgePoint a d f s) k
  rw [openEdgePoint_fixed a d e r k hke, openEdgePoint_fixed a d f s k hkf,
    endValue_distance_of_ne (a k) d _ _ hside] at h
  exact h

def faceSide (upper : Bool) : Fin 2 := if upper then 1 else 0

theorem faceInterior_normal_value {a p : Site} {d : ℕ} {normal : Fin 3} {upper : Bool}
    (hp : FaceInterior a (d + 2) normal upper p) :
    p normal = endValue (a normal) d (faceSide upper) := by
  have h := hp.2.1
  cases upper <;> simp only [faceSide, Bool.false_eq_true, ↓reduceIte, endValue] at h ⊢ <;> omega

/-- A step from a face interior to a skeleton vertex stays in that face's
supporting plane. Moving normally would leave both tangential axes interior. -/
theorem face_to_skeleton_normal_eq {a p q : Site} {n : ℕ} {normal : Fin 3} {upper : Bool}
    (hp : FaceInterior a n normal upper p) (hq : EdgeSkeleton a n q)
    (hadj : cubicLattice.Adj p q) : q normal = p normal := by
  obtain ⟨dir, hdir⟩ := adj_step hadj
  by_cases hn : normal = directionAxis dir
  · obtain ⟨_, i, j, hij, hi, hj⟩ := hq
    have hoff : i ≠ normal ∨ j ≠ normal := by by_contra h; push_neg at h; exact hij (h.1.trans h.2.symm)
    rcases hoff with hoff | hoff
    · have hk : i ≠ directionAxis dir := by simpa only [← hn] using hoff
      have he := congrFun hdir i
      rw [step_unchanged_off_axis p dir i hk] at he
      unfold BoundaryCoordinate at hi
      rw [← he] at hi
      exact False.elim (boundary_not_strict hi (hp.2.2 i hoff))
    · have hk : j ≠ directionAxis dir := by simpa only [← hn] using hoff
      have he := congrFun hdir j
      rw [step_unchanged_off_axis p dir j hk] at he
      unfold BoundaryCoordinate at hj
      rw [← he] at hj
      exact False.elim (boundary_not_strict hj (hp.2.2 j hoff))
  · have he := congrFun hdir normal
    rw [step_unchanged_off_axis p dir normal hn] at he
    exact he.symm

theorem face_neighbour_edge_on_face {a p : Site} {d : ℕ} {normal : Fin 3} {upper : Bool}
    (hp : FaceInterior a (d + 2) normal upper p) (e : CubeEdge) (r : Fin d)
    (hadj : cubicLattice.Adj p (openEdgePoint a d e r)) :
    EdgeOnFace e normal (faceSide upper) := by
  have he := face_to_skeleton_normal_eq hp (openEdgePoint_skeleton a d e r) hadj
  have hn : normal ≠ e.axis := by
    intro hn
    have hb := faceInterior_boundary hp
    unfold BoundaryCoordinate at hb
    rw [← he, hn] at hb
    exact boundary_not_strict hb (openEdgePoint_axis_strict a d e r)
  refine ⟨hn, ?_⟩
  apply endValue_injective (a normal) d
  rw [← openEdgePoint_fixed a d e r normal hn, he, faceInterior_normal_value hp]

end ProteinFolding.CubicPackingGeometry

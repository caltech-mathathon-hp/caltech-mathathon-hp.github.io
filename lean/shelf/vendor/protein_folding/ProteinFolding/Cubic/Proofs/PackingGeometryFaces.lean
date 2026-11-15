import ProteinFolding.Cubic.Proofs.PackingGeometryLocal

/-! Connected surface paths avoiding occupied cube edges stay in a single
face interior. This is the geometric confinement used for the wall and item
words after saturation of the skeleton. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicCertificates

def FaceInterior (a : Site) (n : ℕ) (axis : Fin 3) (upper : Bool) (p : Site) : Prop :=
  p ∈ cube a n ∧
    (if upper then p axis + 1 = a axis + (n : ℤ) else p axis = a axis) ∧
      ∀ j : Fin 3, j ≠ axis → a j < p j ∧ p j + 1 < a j + (n : ℤ)

theorem faceInterior_boundary {a p : Site} {n : ℕ} {axis : Fin 3} {upper : Bool}
    (h : FaceInterior a n axis upper p) : BoundaryCoordinate a p n axis := by
  cases upper
  · exact Or.inl h.2.1
  · exact Or.inr h.2.1

theorem faceInterior_exists_of_surface_not_edge {a p : Site} {n : ℕ}
    (hs : Surface a n p) (he : ¬ EdgeSkeleton a n p) :
    ∃ axis upper, FaceInterior a n axis upper p := by
  obtain ⟨hp, axis, hb⟩ := hs
  have hinterior : ∀ j : Fin 3, j ≠ axis → a j < p j ∧ p j + 1 < a j + (n : ℤ) := by
    intro j hj
    have hnot : ¬ BoundaryCoordinate a p n j := by
      intro hb'
      exact he ⟨hp, j, axis, hj, hb', hb⟩
    have h := hp j
    simp only [BoundaryCoordinate, not_or] at hnot
    omega
  rcases hb with hb | hb
  · exact ⟨axis, false, hp, hb, hinterior⟩
  · exact ⟨axis, true, hp, hb, hinterior⟩

def directionAxis : Fin 6 → Fin 3
  | 0 | 1 => 0
  | 2 | 3 => 1
  | 4 | 5 => 2

theorem step_unchanged_off_axis (p : Site) (d : Fin 6) (k : Fin 3)
    (hk : k ≠ directionAxis d) : step p d k = p k := by
  fin_cases d <;> fin_cases k <;> simp_all [directionAxis, step]

theorem boundary_not_strict {a p : Site} {n : ℕ} {k : Fin 3}
    (hb : BoundaryCoordinate a p n k)
    (hstrict : a k < p k ∧ p k + 1 < a k + (n : ℤ)) : False := by
  rcases hb with hb | hb <;> omega

theorem adjacent_faceInterior_axis_eq {a p q : Site} {n : ℕ}
    {i j : Fin 3} {upper lower : Bool}
    (hp : FaceInterior a n i upper p) (hq : FaceInterior a n j lower q)
    (hadj : cubicLattice.Adj p q) : i = j := by
  obtain ⟨d, rfl⟩ := adj_step hadj
  by_contra hij
  by_cases haxis : i = directionAxis d
  · have hjaxis : j ≠ directionAxis d := by intro h; exact hij (haxis.trans h.symm)
    have heq := step_unchanged_off_axis p d j hjaxis
    have hb := faceInterior_boundary hq
    rw [BoundaryCoordinate, heq] at hb
    exact boundary_not_strict hb (hp.2.2 j (Ne.symm hij))
  · have heq := step_unchanged_off_axis p d i haxis
    have hs := hq.2.2 i hij
    rw [heq] at hs
    exact boundary_not_strict (faceInterior_boundary hp) hs

theorem faceInterior_side_ge_three {a p : Site} {n : ℕ} {i : Fin 3} {upper : Bool}
    (hp : FaceInterior a n i upper p) : 3 ≤ n := by
  have hj : ∃ j : Fin 3, j ≠ i := by
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  obtain ⟨j, hj⟩ := hj
  have hs := hp.2.2 j hj
  omega

theorem adjacent_faceInterior_side_eq {a p q : Site} {n : ℕ}
    {i : Fin 3} {upper lower : Bool}
    (hp : FaceInterior a n i upper p) (hq : FaceInterior a n i lower q)
    (hadj : cubicLattice.Adj p q) : upper = lower := by
  obtain ⟨d, rfl⟩ := adj_step hadj
  have hbounds := step_coordinate_bounds p d i
  have hn := faceInterior_side_ge_three hp
  have hb := hp.2.1
  have hc := hq.2.1
  cases upper <;> cases lower <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb hc ⊢ <;> omega

/-- Once the edge skeleton is unavailable, a unit step along the surface
cannot change either the face's axis or its lower/upper side. -/
theorem faceInterior_step_closed {a p q : Site} {n : ℕ} {i : Fin 3} {upper : Bool}
    (hp : FaceInterior a n i upper p) (hq : Surface a n q)
    (hqe : ¬ EdgeSkeleton a n q) (hadj : cubicLattice.Adj p q) :
    FaceInterior a n i upper q := by
  obtain ⟨j, lower, hf⟩ := faceInterior_exists_of_surface_not_edge hq hqe
  have he := adjacent_faceInterior_axis_eq hp hf hadj
  subst j
  have he' := adjacent_faceInterior_side_eq hp hf hadj
  subst lower
  exact hf

/-- An entire nonempty path on the surface, with every cube-edge site
unavailable, is contained in its first face interior. -/
theorem faceInterior_path_closed {a : Site} {n N : ℕ} {axis : Fin 3} {upper : Bool}
    (p : Fin N → Site) (hN : 0 < N)
    (hfirst : FaceInterior a n axis upper (p ⟨0, hN⟩))
    (hsurface : ∀ i, Surface a n (p i))
    (hedge : ∀ i, ¬ EdgeSkeleton a n (p i))
    (hstep : ∀ i j : Fin N, i.val + 1 = j.val → cubicLattice.Adj (p i) (p j)) :
    ∀ i, FaceInterior a n axis upper (p i) := by
  have h : ∀ k (hk : k < N), FaceInterior a n axis upper (p ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk; exact hfirst
    | succ k ih =>
      intro hk
      have hk' : k < N := by omega
      exact faceInterior_step_closed (ih hk') (hsurface ⟨k + 1, hk⟩)
        (hedge ⟨k + 1, hk⟩) (hstep ⟨k, hk'⟩ ⟨k + 1, hk⟩ rfl)
  intro i
  exact h i.val i.isLt

theorem surface_path_in_one_face {a : Site} {n N : ℕ}
    (p : Fin N → Site) (hN : 0 < N)
    (hsurface : ∀ i, Surface a n (p i))
    (hedge : ∀ i, ¬ EdgeSkeleton a n (p i))
    (hstep : ∀ i j : Fin N, i.val + 1 = j.val → cubicLattice.Adj (p i) (p j)) :
    ∃ axis upper, ∀ i, FaceInterior a n axis upper (p i) := by
  obtain ⟨axis, upper, hfirst⟩ :=
    faceInterior_exists_of_surface_not_edge (hsurface ⟨0, hN⟩) (hedge ⟨0, hN⟩)
  exact ⟨axis, upper, faceInterior_path_closed p hN hfirst hsurface hedge hstep⟩

end ProteinFolding.CubicPackingGeometry

import ProteinFolding.Cubic.Proofs.PackingGeometryFaces

/-! Equality in the axial displacement bound forces a cubic-lattice walk
to be straight. This is the no-spare-steps principle for the frame's walls. -/

namespace ProteinFolding.CubicPackingGeometry

open CubicCertificates

theorem adjacent_coordinate_bounds {p q : Site} (h : cubicLattice.Adj p q) (k : Fin 3) :
    p k - 1 ≤ q k ∧ q k ≤ p k + 1 := by
  obtain ⟨d, rfl⟩ := adj_step h
  exact step_coordinate_bounds p d k

theorem walk_coordinate_upper (p : ℕ → Site) (start m : ℕ)
    (hstep : ∀ j, j < m → cubicLattice.Adj (p (start + j)) (p (start + j + 1)))
    (k : Fin 3) : p (start + m) k ≤ p start k + (m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hprefix : ∀ j, j < m → cubicLattice.Adj (p (start + j)) (p (start + j + 1)) := by
      intro j hj
      exact hstep j (by omega)
    have hi := ih hprefix
    have hs := adjacent_coordinate_bounds (hstep m (by omega)) k
    simpa only [Nat.add_succ, Nat.cast_add, Nat.cast_one] using (by omega :
      p (start + m + 1) k ≤ p start k + ((m : ℤ) + 1))

theorem walk_max_axis_prefix (p : ℕ → Site) (N : ℕ) (axis : Fin 3)
    (hstep : ∀ j, j < N → cubicLattice.Adj (p j) (p (j + 1)))
    (hend : p N axis = p 0 axis + (N : ℤ)) :
    ∀ i, i ≤ N → p i axis = p 0 axis + (i : ℤ) := by
  intro i hi
  have hp := walk_coordinate_upper p 0 i (by
    intro j hj
    simpa only [Nat.zero_add] using hstep j (by omega)) axis
  have hs := walk_coordinate_upper p i (N - i) (by
    intro j hj
    exact hstep (i + j) (by omega)) axis
  have hsum : i + (N - i) = N := by omega
  rw [hsum] at hs
  simp only [Nat.zero_add] at hp
  omega

theorem adjacent_max_axis_other_eq {p q : Site} (axis k : Fin 3)
    (h : cubicLattice.Adj p q) (haxis : q axis = p axis + 1) (hk : k ≠ axis) :
    q k = p k := by
  obtain ⟨d, rfl⟩ := adj_step h
  have hd : axis = directionAxis d := by
    by_contra hn
    have he := step_unchanged_off_axis p d axis hn
    omega
  exact step_unchanged_off_axis p d k (by simpa only [← hd] using hk)

/-- The equality case of the endpoint distance bound: no turn or backwards
step is possible when every available step is needed in a single axis. -/
theorem walk_max_axis_straight (p : ℕ → Site) (N : ℕ) (axis : Fin 3)
    (hstep : ∀ j, j < N → cubicLattice.Adj (p j) (p (j + 1)))
    (hend : p N axis = p 0 axis + (N : ℤ)) :
    ∀ i, i ≤ N → p i = Function.update (p 0) axis (p 0 axis + (i : ℤ)) := by
  have haxis := walk_max_axis_prefix p N axis hstep hend
  have hother : ∀ i, i ≤ N → ∀ k, k ≠ axis → p i k = p 0 k := by
    intro i
    induction i with
    | zero => intros; rfl
    | succ i ih =>
      intro hi k hk
      have hi' : i < N := by omega
      have he := adjacent_max_axis_other_eq axis k (hstep i hi')
        (by rw [haxis (i + 1) hi, haxis i (by omega)]; simp; omega) hk
      exact he.trans (ih (by omega) k hk)
  intro i hi
  funext k
  by_cases hk : k = axis
  · subst k
    simpa only [Function.update_self] using haxis i hi
  · simpa only [Function.update_of_ne hk] using hother i hi k hk

end ProteinFolding.CubicPackingGeometry

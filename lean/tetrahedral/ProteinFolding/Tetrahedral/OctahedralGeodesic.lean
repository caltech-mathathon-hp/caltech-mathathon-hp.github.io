import ProteinFolding.Tetrahedral.OctahedralEdgeFacts

/-!
# Unique straight zigzags

The four-times-height is 4-Lipschitz on lattice bonds. A path attaining
the resulting length bound must take the uniquely determined forward
step at every site. This proves uniqueness in the entire lattice, without
assuming that intermediate sites lie on the surface.
-/

namespace ProteinFolding.Tetrahedral

def edgeForwardStep (a b : Fin 4) (p : Site) : Site :=
  if InASublattice p.val then step p a else step p b

theorem edgeForwardStep_adj (a b : Fin 4) (p : Site) :
    tetrahedralLattice.Adj p (edgeForwardStep a b p) := by
  unfold edgeForwardStep
  split_ifs <;> exact step_adj _ _

theorem edgeForwardStep_height (m : ℕ) {a b : Fin 4} (hab : a ≠ b) (p : Site) :
    octEdgeHeight4 m a b (edgeForwardStep a b p) = octEdgeHeight4 m a b p + 4 := by
  rcases p.property with hpA | hpB
  · rw [edgeForwardStep, if_pos hpA, octEdgeHeight4_step_A m a b a hpA,
      if_pos rfl, if_neg (Ne.symm hab)]
    omega
  · rw [edgeForwardStep, if_neg ((inB_iff_not_inA p).mp hpB),
      octEdgeHeight4_step_B m a b b hpB, if_neg hab, if_pos rfl]
    omega

/-- A bond attaining the upper height increment has only one possible end. -/
theorem height_up_step_unique (m : ℕ) (a b : Fin 4) {p q : Site}
    (hadj : tetrahedralLattice.Adj p q)
    (hheight : octEdgeHeight4 m a b q = octEdgeHeight4 m a b p + 4) :
    q = edgeForwardStep a b p := by
  obtain ⟨d, rfl⟩ := (adj_iff_exists_step p q).mp hadj
  rcases p.property with hpA | hpB
  · rw [octEdgeHeight4_step_A m a b d hpA] at hheight
    rw [edgeForwardStep, if_pos hpA]
    by_cases hda : d = a
    · rw [hda]
    · rw [if_neg (Ne.symm hda)] at hheight
      split_ifs at hheight <;> omega
  · rw [octEdgeHeight4_step_B m a b d hpB] at hheight
    rw [edgeForwardStep, if_neg ((inB_iff_not_inA p).mp hpB)]
    by_cases hdb : d = b
    · rw [hdb]
    · rw [if_neg (Ne.symm hdb)] at hheight
      split_ifs at hheight <;> omega

theorem path_height_upper_bound (m : ℕ) (a b : Fin 4) (f : ℕ → Site) (n : ℕ)
    (hstep : ∀ i < n, tetrahedralLattice.Adj (f i) (f (i + 1))) :
    octEdgeHeight4 m a b (f n) ≤ octEdgeHeight4 m a b (f 0) + 4 * (n : ℤ) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hp := ih (fun i hi => hstep i (by omega))
    have hs := (octEdgeHeight4_adj_bounds m a b (hstep n (by omega))).2
    push_cast
    omega

/-- Equality in the path bound forces every individual step. -/
theorem saturated_path_forward (m : ℕ) (a b : Fin 4) (f : ℕ → Site) (n : ℕ)
    (hstep : ∀ i < n, tetrahedralLattice.Adj (f i) (f (i + 1)))
    (hend : octEdgeHeight4 m a b (f n) = octEdgeHeight4 m a b (f 0) + 4 * (n : ℤ)) :
    ∀ i < n, f (i + 1) = edgeForwardStep a b (f i) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have hpsteps : ∀ i < n, tetrahedralLattice.Adj (f i) (f (i + 1)) := by
      intro i hi
      exact hstep i (by omega)
    have hp := path_height_upper_bound m a b f n hpsteps
    have hs := (octEdgeHeight4_adj_bounds m a b (hstep n (by omega))).2
    have hpheight : octEdgeHeight4 m a b (f n) =
        octEdgeHeight4 m a b (f 0) + 4 * (n : ℤ) := by
      push_cast at hend
      omega
    have hlast : octEdgeHeight4 m a b (f (n + 1)) =
        octEdgeHeight4 m a b (f n) + 4 := by
      push_cast at hend
      omega
    intro i hi
    by_cases hin : i < n
    · exact ih hpsteps hpheight i hin
    · have hieq : i = n := by omega
      subst i
      exact height_up_step_unique m a b (hstep n (by omega)) hlast

/-- Two paths of the extremal length and height difference coincide. -/
theorem saturated_path_unique (m : ℕ) (a b : Fin 4) (f g : ℕ → Site) (n : ℕ)
    (hf : ∀ i < n, tetrahedralLattice.Adj (f i) (f (i + 1)))
    (hg : ∀ i < n, tetrahedralLattice.Adj (g i) (g (i + 1)))
    (hfheight : octEdgeHeight4 m a b (f n) = octEdgeHeight4 m a b (f 0) + 4 * (n : ℤ))
    (hgheight : octEdgeHeight4 m a b (g n) = octEdgeHeight4 m a b (g 0) + 4 * (n : ℤ))
    (hstart : f 0 = g 0) : ∀ i ≤ n, f i = g i := by
  have hff := saturated_path_forward m a b f n hf hfheight
  have hgf := saturated_path_forward m a b g n hg hgheight
  intro i
  induction i with
  | zero => intro _; exact hstart
  | succ i ih =>
    intro hi
    rw [hff i (by omega), hgf i (by omega), ih (by omega)]

/-- Any path joining opposite height edges needs at least 2m−2 bonds. -/
theorem opposite_edges_path_length {m : ℕ} (hm : 1 ≤ m) (a b : Fin 4)
    (f : ℕ → Site) (n : ℕ)
    (hstep : ∀ i < n, tetrahedralLattice.Adj (f i) (f (i + 1)))
    (hstart : OctEdgeSite m b a (f 0)) (hend : OctEdgeSite m a b (f n)) :
    2 * m - 2 ≤ n := by
  have hs : f 0 ∈ octahedron m := (octEdgeSite_surface m hstart).1
  have he : f n ∈ octahedron m := (octEdgeSite_surface m hend).1
  have hmin := (octEdgeHeight4_min_iff m a b hs).mpr hstart
  have hmax := (octEdgeHeight4_max_iff m a b he).mpr hend
  have hbound := path_height_upper_bound m a b f n hstep
  dsimp [octRadius] at hmin hmax
  omega

/-- At the minimum length, endpoints on the extremal edges force the zigzag. -/
theorem opposite_edges_minimal_path_forward {m : ℕ} (hm : 1 ≤ m) (a b : Fin 4)
    (f : ℕ → Site) (hstep : ∀ i < 2 * m - 2,
      tetrahedralLattice.Adj (f i) (f (i + 1)))
    (hstart : OctEdgeSite m b a (f 0)) (hend : OctEdgeSite m a b (f (2 * m - 2))) :
    ∀ i < 2 * m - 2, f (i + 1) = edgeForwardStep a b (f i) := by
  have hs : f 0 ∈ octahedron m := (octEdgeSite_surface m hstart).1
  have he : f (2 * m - 2) ∈ octahedron m := (octEdgeSite_surface m hend).1
  have hmin := (octEdgeHeight4_min_iff m a b hs).mpr hstart
  have hmax := (octEdgeHeight4_max_iff m a b he).mpr hend
  apply saturated_path_forward m a b f (2 * m - 2) hstep
  dsimp [octRadius] at hmin hmax
  omega

end ProteinFolding.Tetrahedral

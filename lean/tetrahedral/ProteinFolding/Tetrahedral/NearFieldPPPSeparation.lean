import ProteinFolding.Tetrahedral.NearFieldPPPEdges

/-! Same-edge PPP links separate by height or by their two opposite face normals. -/

namespace ProteinFolding.Tetrahedral

theorem edgePPPFold_height {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) (s : Fin 3) :
    octEdgeHeight4 m F.a F.b ((edgePPPFold m F r).pos s) =
      -2 * octRadius m + 4 * ((r : ℤ) + s.val) := by
  have hz := octEdgeZigzag_height hm F r
  change octEdgeHeight4 m F.a F.b (facePPPSite (octEdgeZigzag m F r)
    (edgePPPNormal F (octEdgeZigzag m F r)) (edgePPPBack F (octEdgeZigzag m F r))
    (edgePPPForward F (octEdgeZigzag m F r)) s) = _
  by_cases hpA : InASublattice (octEdgeZigzag m F r).val
  · have h0 := octEdgeHeight4_step_A m F.a F.b F.k hpA
    have h1 := octEdgeHeight4_step_B m F.a F.b F.b (step_in_B hpA F.k)
    have h2 := octEdgeHeight4_step_A m F.a F.b F.a (step_in_A (step_in_B hpA F.k) F.b)
    simp only [if_neg F.ka.symm, if_neg F.kb.symm, if_neg F.ab, if_neg F.ab.symm, ite_true] at h0 h1 h2
    simp only [edgePPPNormal, edgePPPBack, edgePPPForward, if_pos hpA]
    fin_cases s <;> dsimp [facePPPSite] <;> omega
  · have hpB := (inB_iff_not_inA _).mpr hpA
    have h0 := octEdgeHeight4_step_B m F.a F.b F.j hpB
    have h1 := octEdgeHeight4_step_A m F.a F.b F.a (step_in_A hpB F.j)
    have h2 := octEdgeHeight4_step_B m F.a F.b F.b (step_in_B (step_in_A hpB F.j) F.a)
    simp only [if_neg F.ja.symm, if_neg F.jb.symm, if_neg F.ab, if_neg F.ab.symm, ite_true] at h0 h1 h2
    simp only [edgePPPNormal, edgePPPBack, edgePPPForward, if_neg hpA]
    fin_cases s <;> dsimp [facePPPSite] <;> omega

theorem edgePPPFolds_disjoint_of_index_gap {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r r' : ℕ)
    (hgap : r + 3 ≤ r' ∨ r' + 3 ≤ r) (s t : Fin 3) :
    (edgePPPFold m F r).pos s ≠ (edgePPPFold m F r').pos t := by
  intro heq
  have hs := edgePPPFold_height hm F r s
  have ht := edgePPPFold_height hm F r' t
  rw [heq] at hs
  have hsl := s.isLt
  have htl := t.isLt
  omega

theorem edgePPPFold_big_normal_lower {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r < 2 * m - 1) (hpA : InASublattice (octEdgeZigzag m F r).val) (s : Fin 3) :
    octRadius m + 3 ≤ tetraCoordinate m ((edgePPPFold m F r).pos s).val F.k := by
  have hE := octEdgeZigzag_mem hm F hr
  have hf : tetraCoordinate m (octEdgeZigzag m F r).val F.k = octRadius m := by
    rcases hE with hA | hB
    · exact hA.1.2.2
    · exact (sublattices_disjoint _ hpA hB.1.2.1).elim
  have h0 := tetraCoordinate_step_A m hpA F.k F.k
  have h1 := tetraCoordinate_step_B m (step_in_B hpA F.k) F.b F.k
  have h2 := tetraCoordinate_step_A m (step_in_A (step_in_B hpA F.k) F.b) F.a F.k
  simp only [ite_true, if_neg F.kb, if_neg F.ka] at h0 h1 h2
  change octRadius m + 3 ≤ tetraCoordinate m (facePPPSite (octEdgeZigzag m F r)
    (edgePPPNormal F (octEdgeZigzag m F r)) (edgePPPBack F (octEdgeZigzag m F r))
    (edgePPPForward F (octEdgeZigzag m F r)) s).val F.k
  simp only [edgePPPNormal, edgePPPBack, edgePPPForward, if_pos hpA]
  fin_cases s <;> dsimp [facePPPSite] <;> omega

theorem edgePPPFold_big_normal_upper_B {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r < 2 * m - 1) (hpB : InBSublattice (octEdgeZigzag m F r).val) (s : Fin 3) :
    tetraCoordinate m ((edgePPPFold m F r).pos s).val F.k ≤ octRadius m := by
  have hE := octEdgeZigzag_mem hm F hr
  have hf : tetraCoordinate m (octEdgeZigzag m F r).val F.k = octRadius m - 1 := by
    rcases hE with hA | hB
    · exact (sublattices_disjoint _ hA.1.2.1 hpB).elim
    · have h := hB.2
      dsimp [octRadius] at *
      omega
  have h0 := tetraCoordinate_step_B m hpB F.j F.k
  have h1 := tetraCoordinate_step_A m (step_in_A hpB F.j) F.a F.k
  have h2 := tetraCoordinate_step_B m (step_in_B (step_in_A hpB F.j) F.a) F.b F.k
  simp only [if_neg F.kj, if_neg F.ka, if_neg F.kb] at h0 h1 h2
  change tetraCoordinate m (facePPPSite (octEdgeZigzag m F r)
    (edgePPPNormal F (octEdgeZigzag m F r)) (edgePPPBack F (octEdgeZigzag m F r))
    (edgePPPForward F (octEdgeZigzag m F r)) s).val F.k ≤ octRadius m
  simp only [edgePPPNormal, edgePPPBack, edgePPPForward, if_neg ((inB_iff_not_inA _).mp hpB)]
  fin_cases s <;> dsimp [facePPPSite] <;> omega

theorem edgePPPFolds_disjoint_of_opposite_colours {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r r' : ℕ)
    (hr : r < 2 * m - 1) (hr' : r' < 2 * m - 1)
    (hA : InASublattice (octEdgeZigzag m F r).val) (hB : InBSublattice (octEdgeZigzag m F r').val)
    (s t : Fin 3) : (edgePPPFold m F r).pos s ≠ (edgePPPFold m F r').pos t := by
  intro heq
  have hs := edgePPPFold_big_normal_lower hm F r hr hA s
  have ht := edgePPPFold_big_normal_upper_B hm F r' hr' hB t
  rw [heq] at hs
  omega

theorem octEdgeZigzag_inA_of_even {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) (hr : r % 2 = 0) :
    InASublattice (octEdgeZigzag m F r).val := by
  have he : r = 2 * (r / 2) := by omega
  rw [he]
  exact (octEdgeZigzag_even hm F (r / 2)).1

theorem octEdgeZigzag_inB_of_odd {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ) (hr : r % 2 = 1) :
    InBSublattice (octEdgeZigzag m F r).val := by
  have he : r = 2 * (r / 2) + 1 := by omega
  rw [he]
  exact (octEdgeZigzag_odd hm F (r / 2)).1

theorem edgePPPFolds_disjoint_of_parity_or_gap {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r r' : ℕ)
    (hr : r < 2 * m - 1) (hr' : r' < 2 * m - 1)
    (hsep : r % 2 ≠ r' % 2 ∨ r + 3 ≤ r' ∨ r' + 3 ≤ r) (s t : Fin 3) :
    (edgePPPFold m F r).pos s ≠ (edgePPPFold m F r').pos t := by
  rcases hsep with hpar | hgap
  · by_cases heven : r % 2 = 0
    · apply edgePPPFolds_disjoint_of_opposite_colours hm F r r' hr hr'
        (octEdgeZigzag_inA_of_even hm F r heven) (octEdgeZigzag_inB_of_odd hm F r' (by omega)) s t
    · exact (edgePPPFolds_disjoint_of_opposite_colours hm F r' r hr' hr
        (octEdgeZigzag_inA_of_even hm F r' (by omega)) (octEdgeZigzag_inB_of_odd hm F r (by omega)) t s).symm
  · exact edgePPPFolds_disjoint_of_index_gap hm F r r' hgap s t

end ProteinFolding.Tetrahedral

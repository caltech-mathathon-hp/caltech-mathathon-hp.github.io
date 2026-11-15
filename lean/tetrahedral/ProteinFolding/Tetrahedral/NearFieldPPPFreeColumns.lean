import ProteinFolding.Tetrahedral.NearFieldPPPEdgeColumns

/-! An endpoint-free PPP determines the normal pair of any column it meets.
This applies to the actual A[2] edge column as well as bulk columns. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgePPP_endpointFree_column_pair (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m)
    (hpne : C.owner ≠ octEdgeZigzag m F r) (hqne : C.owner ≠ octEdgeZigzag m F (r + 2))
    (n : ℕ) (s : Fin 3) (heq : C.point n = (edgePPPFold m F r).pos s) :
    (InASublattice C.owner.val ∧ C.dir = F.k ∧ columnOpposite F.k = F.j) ∨
      (InBSublattice C.owner.val ∧ C.dir = F.j ∧ columnOpposite F.j = F.k) := by
  have hq : faceFourStep (octEdgeZigzag m F r) (edgePPPNormal F (octEdgeZigzag m F r))
      (edgePPPBack F (octEdgeZigzag m F r)) (edgePPPForward F (octEdgeZigzag m F r)) ∈ octahedron m := by
    rw [edgePPP_endpoint]
    rcases octEdgeZigzag_mem hm F hr with h | h <;> exact h.1.1
  have hdir : C.dir = edgePPPNormal F (octEdgeZigzag m F r) := by
    rcases facePPPFold_column_owner m _ _ _ _ (edgePPPLateral_ne F _) (edgePPP_back_ne_normal F _)
      (edgePPP_forward_ne_normal F _) (edgePPP_normal_face hm F r (by omega)) hq C n s heq with h | h | h
    · exact (hpne h).elim
    · exact (hqne (by simpa only [edgePPP_endpoint] using h)).elim
    · exact h.1
  rcases edgePPPFold_column_owner hm F r hr C n s heq with h | h | h | h
  · exact (hpne h).elim
  · exact (hqne h).elim
  · have hA : InASublattice C.owner.val := by
      rw [h.2.2]
      exact step_in_A (step_in_B h.2.1 F.j) F.b
    exact Or.inl ⟨hA, by simpa only [edgePPPNormal, if_pos h.2.1] using hdir, h.1⟩
  · have hB : InBSublattice C.owner.val := by
      rw [h.2.2]
      exact step_in_B (step_in_A h.2.1 F.k) F.a
    exact Or.inr ⟨hB, by simpa only [edgePPPNormal, if_neg ((inB_iff_not_inA _).mp h.2.1)] using hdir, h.1⟩

theorem edgePPPFold_ne_A_column_of_owner_pair_ne (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m)
    (hpne : C.owner ≠ octEdgeZigzag m F r) (hqne : C.owner ≠ octEdgeZigzag m F (r + 2))
    (hA : InASublattice C.owner.val) (d : Fin 4) (hd : C.dir = d)
    (hpair : F.k ≠ d ∨ F.j ≠ columnOpposite d) (s : Fin 3) (n : ℕ) :
    (edgePPPFold m F r).pos s ≠ C.point n := by
  intro heq
  rcases edgePPP_endpointFree_column_pair m hm F r hr C hpne hqne n s heq.symm with h | h
  · have hk : F.k = d := h.2.1.symm.trans hd
    have hj : F.j = columnOpposite d := by rw [← hk]; exact h.2.2.symm
    rcases hpair with hpair | hpair
    · exact hpair hk
    · exact hpair hj
  · exact sublattices_disjoint _ hA h.1

end ProteinFolding.Tetrahedral.NearField

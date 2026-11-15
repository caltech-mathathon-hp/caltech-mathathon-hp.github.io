import ProteinFolding.Tetrahedral.NearFieldPPPEdgeColumns
import ProteinFolding.Tetrahedral.NearFieldBorrowedBulkClearance

/-! If an edge PPP meets a column owned by a surviving bulk site, its
normal pair is exactly that column's X-plane pair. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgePPPFold_bulkOwner_pair (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m) (hC : C.owner ∈ bulkInterior m)
    (n : ℕ) (s : Fin 3) (heq : C.point n = (edgePPPFold m F r).pos s) :
    (InASublattice C.owner.val ∧ C.dir = F.k ∧ columnOpposite F.k = F.j) ∨
      (InBSublattice C.owner.val ∧ C.dir = F.j ∧ columnOpposite F.j = F.k) := by
  have hpne : C.owner ≠ octEdgeZigzag m F r := by
    intro h
    have hd := edgeZigzag_mem_deleted hm F r (by omega)
    rw [← h] at hd
    exact (Finset.mem_sdiff.mp hC).2 hd
  have hqne : C.owner ≠ octEdgeZigzag m F (r + 2) := by
    intro h
    have hd := edgeZigzag_mem_deleted hm F (r + 2) hr
    rw [← h] at hd
    exact (Finset.mem_sdiff.mp hC).2 hd
  have hq : faceFourStep (octEdgeZigzag m F r) (edgePPPNormal F (octEdgeZigzag m F r))
      (edgePPPBack F (octEdgeZigzag m F r)) (edgePPPForward F (octEdgeZigzag m F r)) ∈ octahedron m := by
    rw [edgePPP_endpoint]
    rcases octEdgeZigzag_mem hm F hr with h | h
    · exact h.1.1
    · exact h.1.1
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

theorem edgePPPFold_ne_A_column_of_pair_ne (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m) (hC : C.owner ∈ bulkInterior m)
    (hA : InASublattice C.owner.val) (d : Fin 4) (hd : C.dir = d)
    (hpair : F.k ≠ d ∨ F.j ≠ columnOpposite d) (s : Fin 3) (n : ℕ) :
    (edgePPPFold m F r).pos s ≠ C.point n := by
  intro heq
  rcases edgePPPFold_bulkOwner_pair m hm F r hr C hC n s heq.symm with h | h
  · have hk : F.k = d := h.2.1.symm.trans hd
    have hj : F.j = columnOpposite d := by rw [← hk]; exact h.2.2.symm
    rcases hpair with hpair | hpair
    · exact hpair hk
    · exact hpair hj
  · exact sublattices_disjoint _ hA h.1

theorem edgePPPFold_ne_B_column_of_pair_ne (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m) (hC : C.owner ∈ bulkInterior m)
    (hB : InBSublattice C.owner.val) (d : Fin 4) (hd : C.dir = d)
    (hpair : F.j ≠ d ∨ F.k ≠ columnOpposite d) (s : Fin 3) (n : ℕ) :
    (edgePPPFold m F r).pos s ≠ C.point n := by
  intro heq
  rcases edgePPPFold_bulkOwner_pair m hm F r hr C hC n s heq.symm with h | h
  · exact sublattices_disjoint _ h.1 hB
  · have hj : F.j = d := h.2.1.symm.trans hd
    have hk : F.k = columnOpposite d := by rw [← hj]; exact h.2.2.symm
    rcases hpair with hpair | hpair
    · exact hpair hj
    · exact hpair hk

end ProteinFolding.Tetrahedral.NearField

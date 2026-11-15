import ProteinFolding.Tetrahedral.NearFieldPPPColumnMargins

/-! Canonical columns on inner edge sites or corners avoid all PPPs whose
H endpoints are different from their owners. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgePPPFold_ne_column_of_face_margins (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m)
    (hpne : C.owner ≠ octEdgeZigzag m F r) (hqne : C.owner ≠ octEdgeZigzag m F (r + 2))
    (hA : InASublattice C.owner.val → ∀ d, tetraCoordinate m C.owner.val d ≠ -octRadius m + 4)
    (hB : InBSublattice C.owner.val → ∀ d, tetraCoordinate m C.owner.val d ≠ octRadius m - 5)
    (s : Fin 3) (n : ℕ) : (edgePPPFold m F r).pos s ≠ C.point n := by
  intro heq
  rcases edgePPPFold_column_owner hm F r hr C n s heq.symm with h | h | h | h
  · exact hpne h
  · exact hqne h
  · have hCA : InASublattice C.owner.val := by
      rw [h.2.2]
      exact step_in_A (step_in_B h.2.1 F.j) F.b
    have hf := edgeASecondRow_near_lower m hm F r (by omega) h.2.1
    rw [← h.2.2] at hf
    exact hA hCA F.j hf
  · have hCB : InBSublattice C.owner.val := by
      rw [h.2.2]
      exact step_in_B (step_in_A h.2.1 F.k) F.a
    have hf := edgeBSecondRow_near_upper m hm F r (by omega) h.2.1
    rw [← h.2.2] at hf
    exact hB hCB F.k hf

theorem edgePPPFold_ne_inner_edge_column (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame) (r i : ℕ)
    (hr : r + 2 < 2 * m - 1) (hilo : 4 ≤ i) (hihi : i + 4 ≤ 2 * m - 2)
    (C : DanglingColumn m) (howner : C.owner = octEdgeZigzag m G i)
    (hpne : C.owner ≠ octEdgeZigzag m F r) (hqne : C.owner ≠ octEdgeZigzag m F (r + 2))
    (s : Fin 3) (n : ℕ) : (edgePPPFold m F r).pos s ≠ C.point n := by
  apply edgePPPFold_ne_column_of_face_margins m (by omega) F r hr C hpne hqne _ _ s n
  · intro hA d
    rw [howner] at hA ⊢
    exact inner_edge_A_no_near_lower m hm G i hilo hihi hA d
  · intro hB d
    rw [howner] at hB ⊢
    exact inner_edge_B_no_near_upper m hm G i hilo hihi hB d

theorem edgePPPFold_ne_vertex_column (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m) (a : Fin 3) (positive : Bool)
    (howner : C.owner = octVertexSite m a positive)
    (hpne : C.owner ≠ octEdgeZigzag m F r) (hqne : C.owner ≠ octEdgeZigzag m F (r + 2))
    (s : Fin 3) (n : ℕ) : (edgePPPFold m F r).pos s ≠ C.point n := by
  apply edgePPPFold_ne_column_of_face_margins m (by omega) F r hr C hpne hqne _ _ s n
  · intro _ d
    rw [howner]
    exact vertex_no_near_lower m hm a positive d
  · intro hB _
    have hA : InASublattice C.owner.val := by rw [howner]; exact octVertexCoordinates_inA m a positive
    exact (sublattices_disjoint _ hA hB).elim

theorem edgePPPFold_ne_Bcorner_column (m : ℕ) (hm : 4 ≤ m) (F G : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m) (howner : C.owner = octEdgeZigzag m G 1)
    (hpne : C.owner ≠ octEdgeZigzag m F r) (hqne : C.owner ≠ octEdgeZigzag m F (r + 2))
    (s : Fin 3) (n : ℕ) : (edgePPPFold m F r).pos s ≠ C.point n := by
  apply edgePPPFold_ne_column_of_face_margins m (by omega) F r hr C hpne hqne _ _ s n
  · intro hA _
    have hB : InBSublattice C.owner.val := by
      rw [howner]
      simpa only [Nat.mul_zero, Nat.zero_add] using (octEdgeZigzag_odd (by omega : 1 ≤ m) G 0).1
    exact (sublattices_disjoint _ hA hB).elim
  · intro _ d
    rw [howner]
    exact Bcorner_no_near_upper m hm G d

end ProteinFolding.Tetrahedral.NearField

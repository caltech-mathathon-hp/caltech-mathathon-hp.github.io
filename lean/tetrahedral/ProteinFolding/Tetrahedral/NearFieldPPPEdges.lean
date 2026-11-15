import ProteinFolding.Tetrahedral.NearFieldPPPPaths

/-! Every same-edge dimer PPP is an explicit three-site skin-one fold. -/

namespace ProteinFolding.Tetrahedral

theorem edgePPP_normal_face {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r < 2 * m - 1) :
    OctBigFace m (edgePPPNormal F (octEdgeZigzag m F r)) (octEdgeZigzag m F r) ∨
    OctSmallFace m (edgePPPNormal F (octEdgeZigzag m F r)) (octEdgeZigzag m F r) := by
  rcases octEdgeZigzag_mem hm F hr with hA | hB
  · rw [edgePPPNormal, if_pos hA.1.2.1]
    exact Or.inl hA.1
  · rw [edgePPPNormal, if_neg ((inB_iff_not_inA _).mp hB.1.2.1)]
    exact Or.inr hB.1

theorem edgePPP_back_ne_normal (F : OctEdgeFrame) (p : Site) : edgePPPBack F p ≠ edgePPPNormal F p := by
  unfold edgePPPBack edgePPPNormal
  split_ifs
  · exact F.kb.symm
  · exact F.ja.symm

theorem edgePPP_forward_ne_normal (F : OctEdgeFrame) (p : Site) : edgePPPForward F p ≠ edgePPPNormal F p := by
  unfold edgePPPForward edgePPPNormal
  split_ifs
  · exact F.ka.symm
  · exact F.jb.symm

theorem edgePPPFold_outside {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r < 2 * m - 1) (i : Fin 3) : (edgePPPFold m F r).pos i ∉ octahedron m :=
  facePPPFold_outside m _ _ _ _ (edgePPPLateral_ne F _) (edgePPP_back_ne_normal F _)
    (edgePPP_forward_ne_normal F _) (edgePPP_normal_face hm F r hr) i

theorem edgePPPFold_mem_skin_one {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (i : Fin 3) : (edgePPPFold m F r).pos i ∈ skin m 1 := by
  apply facePPPFold_mem_skin_one m _ _ _ _ (edgePPPLateral_ne F _) (edgePPP_back_ne_normal F _)
    (edgePPP_forward_ne_normal F _) (edgePPP_normal_face hm F r (by omega)) _ i
  rw [edgePPP_endpoint]
  rcases octEdgeZigzag_mem hm F hr with h | h
  · exact h.1.1
  · exact h.1.1

theorem edgePPPFold_first_seam (m : ℕ) (F : OctEdgeFrame) (r : ℕ) :
    tetrahedralLattice.Adj (octEdgeZigzag m F r) ((edgePPPFold m F r).pos 0) :=
  facePPPFold_first_seam _ _ _ _ _

theorem edgePPPFold_last_seam (m : ℕ) (F : OctEdgeFrame) (r : ℕ) :
    tetrahedralLattice.Adj ((edgePPPFold m F r).pos 2) (octEdgeZigzag m F (r + 2)) := by
  rw [← edgePPP_endpoint]
  exact facePPPFold_last_seam _ _ _ _ _

end ProteinFolding.Tetrahedral

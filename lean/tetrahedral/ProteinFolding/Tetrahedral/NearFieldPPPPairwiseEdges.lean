import ProteinFolding.Tetrahedral.NearFieldPPPPairwise
import ProteinFolding.Tetrahedral.NearFieldPPPEdges

/-! The pairwise theorem applies uniformly to all dimer and ring-corner PPPs. -/

namespace ProteinFolding.Tetrahedral

theorem edgePPPFolds_disjoint_of_endpoints_ne {m : ℕ} (hm : 1 ≤ m)
    (F G : OctEdgeFrame) (r r' : ℕ) (hr : r + 2 < 2 * m - 1) (hr' : r' + 2 < 2 * m - 1)
    (hpp : octEdgeZigzag m F r ≠ octEdgeZigzag m G r')
    (hpq : octEdgeZigzag m F r ≠ octEdgeZigzag m G (r' + 2))
    (hqp : octEdgeZigzag m F (r + 2) ≠ octEdgeZigzag m G r')
    (hqq : octEdgeZigzag m F (r + 2) ≠ octEdgeZigzag m G (r' + 2)) (s t : Fin 3) :
    (edgePPPFold m F r).pos s ≠ (edgePPPFold m G r').pos t := by
  have hq : faceFourStep (octEdgeZigzag m F r) (edgePPPNormal F (octEdgeZigzag m F r))
      (edgePPPBack F (octEdgeZigzag m F r)) (edgePPPForward F (octEdgeZigzag m F r)) ∈ octahedron m := by
    rw [edgePPP_endpoint]
    rcases octEdgeZigzag_mem hm F hr with h | h
    · exact h.1.1
    · exact h.1.1
  have hq' : faceFourStep (octEdgeZigzag m G r') (edgePPPNormal G (octEdgeZigzag m G r'))
      (edgePPPBack G (octEdgeZigzag m G r')) (edgePPPForward G (octEdgeZigzag m G r')) ∈ octahedron m := by
    rw [edgePPP_endpoint]
    rcases octEdgeZigzag_mem hm G hr' with h | h
    · exact h.1.1
    · exact h.1.1
  exact facePPPFolds_disjoint_of_endpoints_disjoint m _ _ _ _ _ _ _ _
    (edgePPPLateral_ne F _) (edgePPP_back_ne_normal F _) (edgePPP_forward_ne_normal F _)
    (edgePPPLateral_ne G _) (edgePPP_back_ne_normal G _) (edgePPP_forward_ne_normal G _)
    (edgePPP_normal_face hm F r (by omega)) (edgePPP_normal_face hm G r' (by omega)) hq hq' hpp
    (by simpa only [edgePPP_endpoint] using hpq) (by simpa only [edgePPP_endpoint] using hqp)
    (by simpa only [edgePPP_endpoint] using hqq) s t

theorem facePPPFold_ne_cap_of_owner_ne (m : ℕ) (p : Site) (k i l : Fin 4)
    (hil : i ≠ l) (hik : i ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p) (hq : faceFourStep p k i l ∈ octahedron m)
    (C : DanglingColumn m) (hpne : C.owner ≠ p) (hqne : C.owner ≠ faceFourStep p k i l) (s : Fin 3) :
    (facePPPFold p k i l hil).pos s ≠ C.seed := by
  have hp := hface.elim (fun h => h.1) (fun h => h.1)
  fin_cases s
  · exact (dangling_caps_ne_of_owner_ne m C.owner p C.dir k C.owner_mem hp C.seed_outside hpne).symm
  · intro heq
    change step (step p k) i = C.seed at heq
    apply facePPP_middle_not_dangling m k i hik hface
    rw [heq]
    exact C.seed_dangling
  · change step (step (step p k) i) l ≠ C.seed
    rw [facePPP_last_eq_endpoint_cap]
    exact (dangling_caps_ne_of_owner_ne m C.owner _ C.dir k C.owner_mem hq C.seed_outside hqne).symm

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.NearFieldPPPFrameShortData
import ProteinFolding.Tetrahedral.NearFieldPPPPairwise
import ProteinFolding.Tetrahedral.NearFieldPPPEdges

/-! All valid edge/dimer/ring PPPs avoid every Appendix C frame P-link
whenever their H endpoints are disjoint. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem facePPPFold_ne_shortFramePFold (m q : ℕ) (p : Site) (k i l : Fin 4)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p) (hqp : faceFourStep p k i l ∈ octahedron m)
    (kind : Fin 6) (hq : q % 2 = 1) (hkind : kind = 2 ∨ kind = 3 ∨ kind = 5)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (hpstart : p ≠ frameStartH m q kind) (hpend : p ≠ frameEndH m q kind)
    (hqstart : faceFourStep p k i l ≠ frameStartH m q kind)
    (hqend : faceFourStep p k i l ≠ frameEndH m q kind)
    (s : Fin 3) (r : Fin (nearFrameLength kind - 2)) :
    (facePPPFold p k i l hil).pos s ≠ (framePFold m q kind hq).pos r := by
  have hr : r.val < 3 := by have h := r.isLt; have hn := shortFrame_length kind hkind; omega
  have hf := shortFrame_face m q kind hq hkind hqlo hqhi
  have hend := shortFrame_endpoint m q kind hq hkind hqlo hqhi
  have hqf : faceFourStep (frameStartH m q kind) (shortFrameNormal kind)
      (shortFrameBack kind) (shortFrameForward kind) ∈ octahedron m := by
    rw [hend]
    exact (frameHs_mem_oct m q kind hq hqlo hqhi).2
  change (facePPPFold p k i l hil).pos s ≠ nearFramePoint m q kind hq _
  rw [shortFrame_Ppoint m q kind hq hkind hqlo hqhi ⟨r.val, hr⟩]
  exact facePPPFolds_disjoint_of_endpoints_disjoint m p (frameStartH m q kind)
    k i l (shortFrameNormal kind) (shortFrameBack kind) (shortFrameForward kind)
    hil hik hlk (shortFrame_distinct kind).1 (shortFrame_distinct kind).2.1
    (shortFrame_distinct kind).2.2 hface hf hqp hqf hpstart
    (by simpa only [hend] using hpend) hqstart (by simpa only [hend] using hqend) s ⟨r.val, hr⟩

theorem frameKind_long_or_short (kind : Fin 6) :
    (kind = 0 ∨ kind = 1 ∨ kind = 4) ∨ (kind = 2 ∨ kind = 3 ∨ kind = 5) := by
  revert kind
  decide

theorem facePPPFold_ne_framePFold (m q : ℕ) (p : Site) (k i l : Fin 4)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p) (hqp : faceFourStep p k i l ∈ octahedron m)
    (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (hpstart : p ≠ frameStartH m q kind) (hpend : p ≠ frameEndH m q kind)
    (hqstart : faceFourStep p k i l ≠ frameStartH m q kind)
    (hqend : faceFourStep p k i l ≠ frameEndH m q kind)
    (s : Fin 3) (r : Fin (nearFrameLength kind - 2)) :
    (facePPPFold p k i l hil).pos s ≠ (framePFold m q kind hq).pos r := by
  rcases frameKind_long_or_short kind with hlong | hshort
  · exact facePPPFold_ne_longFramePFold m q p k i l hil hik hlk hface hqp kind hq hlong
      hqlo hqhi hpstart hpend hqstart hqend s r
  · exact facePPPFold_ne_shortFramePFold m q p k i l hil hik hlk hface hqp kind hq hshort
      hqlo hqhi hpstart hpend hqstart hqend s r

theorem edgePPPFold_ne_framePFold (m q : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * m - 1) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (hpstart : octEdgeZigzag m F r ≠ frameStartH m q kind)
    (hpend : octEdgeZigzag m F r ≠ frameEndH m q kind)
    (hqstart : octEdgeZigzag m F (r + 2) ≠ frameStartH m q kind)
    (hqend : octEdgeZigzag m F (r + 2) ≠ frameEndH m q kind)
    (s : Fin 3) (t : Fin (nearFrameLength kind - 2)) :
    (edgePPPFold m F r).pos s ≠ (framePFold m q kind hq).pos t := by
  have hqp : faceFourStep (octEdgeZigzag m F r) (edgePPPNormal F (octEdgeZigzag m F r))
      (edgePPPBack F (octEdgeZigzag m F r)) (edgePPPForward F (octEdgeZigzag m F r)) ∈ octahedron m := by
    rw [edgePPP_endpoint]
    rcases octEdgeZigzag_mem hm F hr with h | h
    · exact h.1.1
    · exact h.1.1
  exact facePPPFold_ne_framePFold m q _ _ _ _ (edgePPPLateral_ne F _)
    (edgePPP_back_ne_normal F _) (edgePPP_forward_ne_normal F _)
    (edgePPP_normal_face hm F r (by omega)) hqp kind hq hqlo hqhi hpstart hpend
    (by simpa only [edgePPP_endpoint] using hqstart) (by simpa only [edgePPP_endpoint] using hqend) s t

end ProteinFolding.Tetrahedral.NearField

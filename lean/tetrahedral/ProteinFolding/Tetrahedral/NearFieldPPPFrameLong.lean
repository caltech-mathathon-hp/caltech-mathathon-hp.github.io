import ProteinFolding.Tetrahedral.NearFieldPPPFramePorts

/-! A valid PPP with different H endpoints avoids every long frame link.
Dangling collisions force a common H owner, while a PPP middle needs two
dangling neighbours and each long-frame site has only one such port. -/

namespace ProteinFolding.Tetrahedral.NearField

def frameStartH (m q : ℕ) (kind : Fin 6) : Site :=
  octEdgeZigzag m (nearFrameRouteFrame kind) (nearFrameStartIndex m q kind)

def frameEndH (m q : ℕ) (kind : Fin 6) : Site :=
  octEdgeZigzag m (nearFrameRouteFrame kind) (nearFrameEndIndex m q kind)

theorem frameHs_mem_oct (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) :
    frameStartH m q kind ∈ octahedron m ∧ frameEndH m q kind ∈ octahedron m := by
  have h := nearFrame_endpoints_mem_oct m q kind hq hqlo hqhi
  simpa only [frameStartH, frameEndH, nearFrame_start_eq m q kind hq hqlo hqhi,
    nearFrame_end_eq m q kind hq hqlo hqhi] using h

theorem danglingCap_ne_framePFold (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (p : Site) (d : Fin 4) (hp : p ∈ octahedron m) (hout : step p d ∉ octahedron m)
    (hstart : p ≠ frameStartH m q kind) (hend : p ≠ frameEndH m q kind)
    (r : Fin (nearFrameLength kind - 2)) : step p d ≠ (framePFold m q kind hq).pos r := by
  intro heq
  have hdang : IsDangling m ((framePFold m q kind hq).pos r) := by
    rw [← heq]
    exact ⟨hout, p, hp, step_adj _ _⟩
  have hidx := nearFramePoint_dangling_index m q kind hq
    ⟨r.val + 1, by have h := r.isLt; omega⟩
    (by change 0 < r.val + 1; omega)
    (by change r.val + 1 + 1 < nearFrameLength kind; have h := r.isLt; omega) hdang
  change r.val + 1 = 1 ∨ r.val + 1 + 2 = nearFrameLength kind at hidx
  have hmem := frameHs_mem_oct m q kind hq hqlo hqhi
  rcases hidx with hfirst | hlast
  · have hadj := framePFold_first_seam m q kind hq hqlo hqhi r (by omega)
    have howner : frameStartH m q kind = p := outside_step_unique_inside m hp d hout
      (by rw [heq]; exact hadj.symm) hmem.1
    exact hstart howner.symm
  · have hadj := framePFold_last_seam m q kind hq hqlo hqhi r (by omega)
    have howner : frameEndH m q kind = p := outside_step_unique_inside m hp d hout
      (by rw [heq]; exact hadj) hmem.2
    exact hend howner.symm

theorem facePPPFold_ne_longFramePFold (m q : ℕ) (p : Site) (k i l : Fin 4)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p) (hqp : faceFourStep p k i l ∈ octahedron m)
    (kind : Fin 6) (hq : q % 2 = 1) (hkind : kind = 0 ∨ kind = 1 ∨ kind = 4)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (hpstart : p ≠ frameStartH m q kind) (hpend : p ≠ frameEndH m q kind)
    (hqstart : faceFourStep p k i l ≠ frameStartH m q kind)
    (hqend : faceFourStep p k i l ≠ frameEndH m q kind)
    (s : Fin 3) (r : Fin (nearFrameLength kind - 2)) :
    (facePPPFold p k i l hil).pos s ≠ (framePFold m q kind hq).pos r := by
  have hp := hface.elim (fun h => h.1) (fun h => h.1)
  have hout := face_four_bond_internal_sites_outside m p k i l hik hlk hface
  fin_cases s
  · exact danglingCap_ne_framePFold m q kind hq hqlo hqhi p k hp hout.1 hpstart hpend r
  · exact facePPP_middle_ne_longFrameP m q p k i l hil hik hlk hface hqp kind hq hkind
      ⟨r.val + 1, by have h := r.isLt; omega⟩ (by change 0 < r.val + 1; omega)
      (by change r.val + 1 + 1 < nearFrameLength kind; have h := r.isLt; omega)
  · change step (step (step p k) i) l ≠ _
    rw [facePPP_last_eq_endpoint_cap]
    have hqout : step (faceFourStep p k i l) k ∉ octahedron m := by
      rw [← facePPP_last_eq_endpoint_cap]
      exact hout.2.2
    exact danglingCap_ne_framePFold m q kind hq hqlo hqhi _ k hqp hqout hqstart hqend r

end ProteinFolding.Tetrahedral.NearField

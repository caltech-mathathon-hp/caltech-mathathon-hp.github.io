import ProteinFolding.Tetrahedral.NearFieldPPPFrameCertificate
import ProteinFolding.Tetrahedral.NearFieldPPPPairwiseFacts
import ProteinFolding.Tetrahedral.NearFieldFrameFolds

/-! Long frame links have one dangling port at each site, so contain no PPP middle. -/

namespace ProteinFolding.Tetrahedral

theorem nearFramePoint_dangling_index (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (hdang : IsDangling m (nearFramePoint m q kind hq r)) :
    r.val = 1 ∨ r.val + 2 = nearFrameLength kind := by
  apply nearFrame_dangling_index_certificate m q kind r hr0 hrlast
  intro i
  exact dangling_tetraCoordinate_bounds m hdang i

theorem nearFramePoint_dangling_neighbour_direction (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hkind : kind = 0 ∨ kind = 1 ∨ kind = 4)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind)
    (d : Fin 4) (hdang : IsDangling m (step (nearFramePoint m q kind hq r) d)) :
    d = nearFrameSinglePort kind r.val := by
  have hb : ∀ i, -(2 * (m : ℤ) - 1) - 3 ≤ tetraCoordinate m (nearFrameStepCoordinates m q kind r.val d) i ∧
      tetraCoordinate m (nearFrameStepCoordinates m q kind r.val d) i ≤ octRadius m + 3 := by
    intro i
    have h := dangling_tetraCoordinate_bounds m hdang i
    rw [nearFramePoint_step_coordinates] at h
    exact h
  rcases hkind with rfl | rfl | rfl
  · exact nearFrame_single_port_kind0 m q r d hr0 hrlast hb
  · exact nearFrame_single_port_kind1 m q r d hr0 hrlast hb
  · exact nearFrame_single_port_kind4 m q r d hr0 hrlast hb

theorem facePPP_middle_ne_longFrameP (m q : ℕ) (p : Site) (k i l : Fin 4)
    (hil : i ≠ l) (hik : i ≠ k) (hlk : l ≠ k)
    (hface : OctBigFace m k p ∨ OctSmallFace m k p) (hqp : faceFourStep p k i l ∈ octahedron m)
    (kind : Fin 6) (hq : q % 2 = 1) (hkind : kind = 0 ∨ kind = 1 ∨ kind = 4)
    (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    step (step p k) i ≠ nearFramePoint m q kind hq r := by
  intro heq
  have hp := hface.elim (fun h => h.1) (fun h => h.1)
  have hout := face_four_bond_internal_sites_outside m p k i l hik hlk hface
  have ha : IsDangling m (step (nearFramePoint m q kind hq r) i) := by
    rw [← heq, step_step]
    exact ⟨hout.1, p, hp, step_adj _ _⟩
  have hc : IsDangling m (step (nearFramePoint m q kind hq r) l) := by
    rw [← heq]
    exact ⟨hout.2.2, faceFourStep p k i l, hqp, (step_adj _ _).symm⟩
  have hi := nearFramePoint_dangling_neighbour_direction m q kind hq hkind r hr0 hrlast i ha
  have hl := nearFramePoint_dangling_neighbour_direction m q kind hq hkind r hr0 hrlast l hc
  exact hil (hi.trans hl.symm)

end ProteinFolding.Tetrahedral

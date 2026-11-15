import ProteinFolding.Tetrahedral.NearFieldRingFrameColumns
import ProteinFolding.Tetrahedral.NearFieldPPPFrameSeparation

/-! Atomic separation of the complete capped ring from the reserved frame:
all frame P-links and every frame H site in the reserved face. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem nearFrameRouteFrame_small (kind : Fin 6) : (nearFrameRouteFrame kind).j = 3 := by
  fin_cases kind <;> rfl

theorem frameStartH_reserved_coordinate (m q : ℕ) (hm : 3 ≤ m) (kind : Fin 6) :
    tetraCoordinate m (frameStartH m q kind).val 3 ≤ -octRadius m := by
  have h := ringEdgePoint_small_coordinate m hm (nearFrameRouteFrame kind) (nearFrameStartIndex m q kind)
  rw [nearFrameRouteFrame_small] at h
  exact h

theorem frameEndH_reserved_coordinate (m q : ℕ) (hm : 3 ≤ m) (kind : Fin 6) :
    tetraCoordinate m (frameEndH m q kind).val 3 ≤ -octRadius m := by
  have h := ringEdgePoint_small_coordinate m hm (nearFrameRouteFrame kind) (nearFrameEndIndex m q kind)
  rw [nearFrameRouteFrame_small] at h
  exact h

theorem ringEdgePoint_ne_reserved_site (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (hj : F.j ≠ 3)
    (r : ℕ) (hlo : 1 ≤ r) (hhi : r + 3 ≤ 2 * m - 1) (x : Site)
    (hx : tetraCoordinate m x.val 3 ≤ -octRadius m) : octEdgeZigzag m F r ≠ x := by
  intro heq
  have h := ringEdgePoint_other_small_coordinate m hm F r hlo hhi 3 hj.symm
  rw [heq] at h
  omega

theorem ringEdgePPP_ne_framePFold (m q : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (hj : F.j ≠ 3)
    (r : ℕ) (hlo : 1 ≤ r) (hhi : r + 5 ≤ 2 * m - 1)
    (kind : Fin 6) (hq : q % 2 = 1) (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (s : Fin 3) (t : Fin (nearFrameLength kind - 2)) :
    (edgePPPFold m F r).pos s ≠ (framePFold m q kind hq).pos t :=
  edgePPPFold_ne_framePFold m q (by omega) F r (by omega) kind hq hqlo hqhi
    (ringEdgePoint_ne_reserved_site m hm F hj r hlo (by omega) _ (frameStartH_reserved_coordinate m q hm kind))
    (ringEdgePoint_ne_reserved_site m hm F hj r hlo (by omega) _ (frameEndH_reserved_coordinate m q hm kind))
    (ringEdgePoint_ne_reserved_site m hm F hj (r + 2) (by omega) (by omega) _
      (frameStartH_reserved_coordinate m q hm kind))
    (ringEdgePoint_ne_reserved_site m hm F hj (r + 2) (by omega) (by omega) _
      (frameEndH_reserved_coordinate m q hm kind)) s t

theorem ringFold_ne_framePFold (m q : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (hj : F.j ≠ 3)
    (kind : Fin 6) (hq : q % 2 = 1) (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (i : Fin (dimerChain (3 * (m - 2))).length) (t : Fin (nearFrameLength kind - 2)) :
    (ringFold m (by omega) heven F).pos i ≠ (framePFold m q kind hq).pos t := by
  apply ringFold_property m (by omega) heven F (fun x => x ≠ (framePFold m q kind hq).pos t) _ _ i
  · intro j r
    let r' : Fin (dimerChain (m - 3 + 1)).length :=
      ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
    change (edgeDimerFold (by omega : 1 ≤ m) (ringSideFrame F j) 1 (m - 3) false (by omega)).pos r' ≠ _
    rcases edgeDimerFold_pos_cases (by omega : 1 ≤ m) (ringSideFrame F j) 1 (m - 3) false
        (by omega) r' with ⟨k, hk, s, hs⟩ | ⟨k, hk, s, hs⟩
    · rw [hs]
      intro heq
      apply framePFold_outside m q kind hq t
      rw [← heq]
      exact edgeDimerHsites_subset_oct (by omega : 1 ≤ m) (ringSideFrame F j) 1 (m - 3) (by omega)
        (dimerHIndex_mem_Hsites m (ringSideFrame F j) 1 (m - 3) false k hk s)
    · rw [hs]
      have hb := dimerLinkIndex_bounds 1 false k
      exact ringEdgePPP_ne_framePFold m q (by omega) (ringSideFrame F j)
        (by rw [ringSideFrame_small]; exact hj) _ (by omega) (by omega) kind hq hqlo hqhi s t
  · intro c r
    exact ringEdgePPP_ne_framePFold m q (by omega) (bulkReverseEdgeFrame (ringSideFrame F c.castSucc))
      (by change (ringSideFrame F c.castSucc).j ≠ 3; rw [ringSideFrame_small]; exact hj)
      1 (by omega) (by omega) kind hq hqlo hqhi r.rev t

theorem cappedRingFold_ne_framePFold (m q : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (hj : F.j ≠ 3) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (kind : Fin 6) (hq : q % 2 = 1) (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) (t : Fin (nearFrameLength kind - 2)) :
    (cappedRingFold m hm heven F C D hC hD).pos i ≠ (framePFold m q kind hq).pos t := by
  intro heq
  have hmem := (mem_foldSites (cappedRingFold m hm heven F C D hC hD) _).mpr ⟨i, heq⟩
  rw [cappedRingFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact ringTerminalColumn_ne_framePFold m q (by omega) F hj 0 0 C hC kind hq hqlo hqhi 0 t h.symm
  · obtain ⟨j, hj'⟩ := (mem_foldSites _ _).mp h
    exact ringFold_ne_framePFold m q hm heven F hj kind hq hqlo hqhi j t hj'
  · exact ringTerminalColumn_ne_framePFold m q (by omega) F hj 2 1 D hD kind hq hqlo hqhi 0 t h.symm

theorem ringFold_ne_reserved_oct_site (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (hj : F.j ≠ 3) (x : Site) (hx : x ∈ octahedron m)
    (hface : tetraCoordinate m x.val 3 ≤ -octRadius m)
    (i : Fin (dimerChain (3 * (m - 2))).length) : (ringFold m hm heven F).pos i ≠ x := by
  apply ringFold_property m hm heven F (fun y => y ≠ x) _ _ i
  · intro j r
    let r' : Fin (dimerChain (m - 3 + 1)).length :=
      ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
    change (edgeDimerFold (by omega : 1 ≤ m) (ringSideFrame F j) 1 (m - 3) false (by omega)).pos r' ≠ x
    rcases edgeDimerFold_pos_cases (by omega : 1 ≤ m) (ringSideFrame F j) 1 (m - 3) false
        (by omega) r' with ⟨k, hk, s, hs⟩ | ⟨k, hk, s, hs⟩
    · rw [hs]
      have hb := dimerHIndex_bounds 1 false k s
      exact ringEdgePoint_ne_reserved_site m hm (ringSideFrame F j)
        (by rw [ringSideFrame_small]; exact hj) _ (by omega) (by omega) x hface
    · rw [hs]
      intro heq
      have hb := dimerLinkIndex_bounds 1 false k
      exact edgePPPFold_outside (by omega : 1 ≤ m) (ringSideFrame F j) _ (by omega) s (heq.symm ▸ hx)
  · intro c r heq
    exact ringCornerFold_outside m hm _ r (heq.symm ▸ hx)

theorem cappedRingFold_ne_reserved_oct_site (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (hj : F.j ≠ 3) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (x : Site) (hx : x ∈ octahedron m) (hface : tetraCoordinate m x.val 3 ≤ -octRadius m)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) :
    (cappedRingFold m hm heven F C D hC hD).pos i ≠ x := by
  intro heq
  have hmem := (mem_foldSites (cappedRingFold m hm heven F C D hC hD) _).mpr ⟨i, heq⟩
  rw [cappedRingFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · apply C.seed_outside
    change C.seed ∈ octahedron m
    rw [← h]
    exact hx
  · obtain ⟨j, hj'⟩ := (mem_foldSites _ _).mp h
    exact ringFold_ne_reserved_oct_site m (by omega) heven F hj x hx hface j hj'
  · apply D.seed_outside
    change D.seed ∈ octahedron m
    rw [← h]
    exact hx

end ProteinFolding.Tetrahedral.NearField

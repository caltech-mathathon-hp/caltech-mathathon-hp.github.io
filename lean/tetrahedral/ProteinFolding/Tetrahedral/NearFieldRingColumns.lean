import ProteinFolding.Tetrahedral.NearFieldRingLocations
import ProteinFolding.Tetrahedral.NearFieldRingB3Column
import ProteinFolding.Tetrahedral.NearFieldPPPCanonicalColumns

/-! Both external ring columns avoid the complete ring at every height.
For the final B3 endpoint the missing closing PPP is essential: its B1
corner is the first endpoint, excluded from all PPP owners used by the ring. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem ringTerminalSite_ne (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (i j : Fin 3) (e e' : Fin 2) (hne : (i, e) ≠ (j, e')) :
    ringTerminalSite m F i e ≠ ringTerminalSite m F j e' := by
  intro heq
  apply hne
  exact ringTerminalSite_injective m hm heven F (a₁ := (i, e)) (a₂ := (j, e')) heq

theorem ringFirst_ne_corner_start (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (c : Fin 2) :
    ringTerminalSite m F 0 0 ≠ octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 1 := by
  rw [ringCorner_start_owner m hm F c]
  exact ringTerminalSite_ne m hm heven F 0 c.succ 0 0 (by fin_cases c <;> decide)

theorem ringFirst_ne_corner_end (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (c : Fin 2) :
    ringTerminalSite m F 0 0 ≠ octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 3 := by
  rw [ringCorner_end_owner m hm F c]
  exact ringTerminalSite_ne m hm heven F 0 c.castSucc 0 1 (by fin_cases c <;> decide)

theorem ringLast_ne_corner_start (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (c : Fin 2) :
    ringTerminalSite m F 2 1 ≠ octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 1 := by
  rw [ringCorner_start_owner m hm F c]
  exact ringTerminalSite_ne m hm heven F 2 c.succ 1 0 (by fin_cases c <;> decide)

theorem ringLast_ne_corner_end (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (c : Fin 2) :
    ringTerminalSite m F 2 1 ≠ octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 3 := by
  rw [ringCorner_end_owner m hm F c]
  exact ringTerminalSite_ne m hm heven F 2 c.castSucc 1 1 (by fin_cases c <;> decide)

theorem ringLastReverse_start (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F 2)) 1 = ringTerminalSite m F 0 0 := by
  change octEdgeZigzag m (bulkReverseEdgeFrame (ringNextFrame (ringNextFrame F))) 1 =
    octEdgeZigzag m F 1
  rw [ringNext_start_corner m (by omega), ringNextFrame_three]

theorem edgeDimerFold_ne_column_of_PPP_ne {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (C : DanglingColumn m)
    (hppp : ∀ j, j < q → ∀ (s : Fin 3) n,
      (edgePPPFold m F (dimerLinkIndex base reverse j)).pos s ≠ C.point n)
    (i : Fin (dimerChain (q + 1)).length) (n : ℕ) :
    (edgeDimerFold hm F base q reverse hroom).pos i ≠ C.point n := by
  rcases edgeDimerFold_pos_cases hm F base q reverse hroom i with
    ⟨j, hj, s, hs⟩ | ⟨j, hj, s, hs⟩
  · rw [hs]
    intro heq
    apply C.point_outside n
    rw [← heq]
    exact edgeDimerHsites_subset_oct hm F base q hroom
      (dimerHIndex_mem_Hsites m F base q reverse j hj s)
  · rw [hs]
    exact hppp j hj s n

theorem ringFold_ne_first_column (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C : DanglingColumn m) (hC : C.owner = ringTerminalSite m F 0 0)
    (i : Fin (dimerChain (3 * (m - 2))).length) (n : ℕ) :
    (ringFold m (by omega) heven F).pos i ≠ C.point n := by
  apply ringFold_property m (by omega) heven F (fun x => x ≠ C.point n) _ _ i
  · intro j r
    let r' : Fin (dimerChain (m - 3 + 1)).length :=
      ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
    have hx := ringTerminal_linkOwnerExcluded m (by omega) heven F j 0 0
    rw [← hC] at hx
    exact edgeDimerFold_ne_column_of_PPP_ne (by omega : 1 ≤ m) (ringSideFrame F j)
      1 (m - 3) false (by omega) C (by
        intro k hk s v
        have hb := dimerLinkIndex_bounds 1 false k
        exact edgePPPFold_ne_Bcorner_column m (by omega) (ringSideFrame F j) (ringSideFrame F 0)
          _ (by omega) C hC (by simpa using hx k hk 0) (by simpa using hx k hk 1) s v) r' n
  · intro c r
    exact edgePPPFold_ne_Bcorner_column m (by omega)
      (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) (ringSideFrame F 0) 1 (by omega) C hC
      (by rw [hC]; exact ringFirst_ne_corner_start m (by omega) heven F c)
      (by rw [hC]; exact ringFirst_ne_corner_end m (by omega) heven F c) r.rev n

theorem ringFold_ne_last_column (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (D : DanglingColumn m) (hD : D.owner = ringTerminalSite m F 2 1)
    (i : Fin (dimerChain (3 * (m - 2))).length) (n : ℕ) :
    (ringFold m (by omega) heven F).pos i ≠ D.point n := by
  have hD' : D.owner = octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F 2)) 3 :=
    hD.trans (ringSide_last_eq_reverse_three m (by omega) (ringSideFrame F 2))
  apply ringFold_property m (by omega) heven F (fun x => x ≠ D.point n) _ _ i
  · intro j r
    let r' : Fin (dimerChain (m - 3 + 1)).length :=
      ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
    have hx := ringTerminal_linkOwnerExcluded m (by omega) heven F j 2 1
    rw [← hD] at hx
    have hc := ringTerminal_linkOwnerExcluded m (by omega) heven F j 0 0
    rw [← ringLastReverse_start m (by omega) F] at hc
    exact edgeDimerFold_ne_column_of_PPP_ne (by omega : 1 ≤ m) (ringSideFrame F j)
      1 (m - 3) false (by omega) D (by
        intro k hk s v
        have hb := dimerLinkIndex_bounds 1 false k
        exact edgePPPFold_ne_B3_column m hm (ringSideFrame F j)
          (bulkReverseEdgeFrame (ringSideFrame F 2)) _ (by omega) D hD'
          (by simpa using hx k hk 0) (by simpa using hx k hk 1)
          (by simpa using hc k hk 0) (by simpa using hc k hk 1) s v) r' n
  · intro c r
    exact edgePPPFold_ne_B3_column m hm (bulkReverseEdgeFrame (ringSideFrame F c.castSucc))
      (bulkReverseEdgeFrame (ringSideFrame F 2)) 1 (by omega) D hD'
      (by rw [hD]; exact ringLast_ne_corner_start m (by omega) heven F c)
      (by rw [hD]; exact ringLast_ne_corner_end m (by omega) heven F c)
      (by rw [ringLastReverse_start m (by omega) F]; exact ringFirst_ne_corner_start m (by omega) heven F c)
      (by rw [ringLastReverse_start m (by omega) F]; exact ringFirst_ne_corner_end m (by omega) heven F c)
      r.rev n

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.NearFieldRingTerminals

/-! Both selected corner PPPs avoid all three complete side folds and each
other. The third, closing corner PPP is deliberately absent from this unit. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem ringSide_ne_corner (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame)
    (i : Fin 3) (c : Fin 2) (r : Fin (dimerChain (m - 2)).length) (s : Fin 3) :
    (ringSideFold m hm (ringSideFrame F i)).pos r ≠
      (ringCornerFold m (ringSideFrame F c.castSucc)).pos s := by
  have hs := ringTerminal_linkOwnerExcluded m hm heven F i c.succ 0
  have ht := ringTerminal_linkOwnerExcluded m hm heven F i c.castSucc 1
  rw [← ringCorner_start_owner m hm F c] at hs
  rw [← ringCorner_end_owner m hm F c] at ht
  have hlen : (dimerChain (m - 3 + 1)).length = (dimerChain (m - 2)).length := by
    rw [show m - 3 + 1 = m - 2 by omega]
  let r' : Fin (dimerChain (m - 3 + 1)).length := ⟨r.val, by rw [hlen]; exact r.isLt⟩
  have h := edgeDimerFold_ne_edgePPPFold (by omega : 1 ≤ m)
    (ringSideFrame F i) (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 1 (m - 3) false
    (by omega) 1 (by omega) hs ht r' s.rev
  simpa only [edgeDimerFold_pos, ringSideFold_pos, ringCornerFold, Fold.reverse] using h

theorem ringCorners_disjoint (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame)
    (r s : Fin 3) :
    (ringCornerFold m (ringSideFrame F 0)).pos r ≠
      (ringCornerFold m (ringSideFrame F 1)).pos s := by
  have hterminal := ringTerminalSite_injective m hm heven F
  have hpp : ringTerminalSite m F 1 0 ≠ ringTerminalSite m F 2 0 := by
    intro heq
    have hbad := congrArg (fun ie : Fin 3 × Fin 2 => ie.1.val) (@hterminal (1, 0) (2, 0) heq)
    change (1 : ℕ) = 2 at hbad
    omega
  have hpq : ringTerminalSite m F 1 0 ≠ ringTerminalSite m F 1 1 := by
    intro heq
    have hbad := congrArg (fun ie : Fin 3 × Fin 2 => ie.2.val) (@hterminal (1, 0) (1, 1) heq)
    change (0 : ℕ) = 1 at hbad
    omega
  have hqp : ringTerminalSite m F 0 1 ≠ ringTerminalSite m F 2 0 := by
    intro heq
    have hbad := congrArg (fun ie : Fin 3 × Fin 2 => ie.1.val) (@hterminal (0, 1) (2, 0) heq)
    change (0 : ℕ) = 2 at hbad
    omega
  have hqq : ringTerminalSite m F 0 1 ≠ ringTerminalSite m F 1 1 := by
    intro heq
    have hbad := congrArg (fun ie : Fin 3 × Fin 2 => ie.1.val) (@hterminal (0, 1) (1, 1) heq)
    change (0 : ℕ) = 1 at hbad
    omega
  have hs0 : octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F 0)) 1 =
      ringTerminalSite m F 1 0 := ringCorner_start_owner m hm F 0
  have he0 : octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F 0)) 3 =
      ringTerminalSite m F 0 1 := ringCorner_end_owner m hm F 0
  have hs1 : octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F 1)) 1 =
      ringTerminalSite m F 2 0 := ringCorner_start_owner m hm F 1
  have he1 : octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F 1)) 3 =
      ringTerminalSite m F 1 1 := ringCorner_end_owner m hm F 1
  have h := edgePPPFolds_disjoint_of_endpoints_ne (by omega : 1 ≤ m)
    (bulkReverseEdgeFrame (ringSideFrame F 0)) (bulkReverseEdgeFrame (ringSideFrame F 1)) 1 1
    (by omega) (by omega)
    (by rw [hs0, hs1]; exact hpp)
    (by change _ ≠ octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F 1)) 3
        rw [hs0, he1]; exact hpq)
    (by change octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F 0)) 3 ≠ _
        rw [he0, hs1]; exact hqp)
    (by change octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F 0)) 3 ≠
          octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame F 1)) 3
        rw [he0, he1]; exact hqq)
    r.rev s.rev
  exact h

end ProteinFolding.Tetrahedral.NearField

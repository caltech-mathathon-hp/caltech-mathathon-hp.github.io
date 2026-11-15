import ProteinFolding.Tetrahedral.NearFieldRingColumns
import ProteinFolding.Tetrahedral.NearFieldRingSeparation

/-! A complete ring avoids both external columns of any ring on another
small face, at every height. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem edgePPP_ne_ring_terminal_column (m : ℕ) (hm : 30 ≤ m) (F G : OctEdgeFrame)
    (r : ℕ) (hr : r + 2 < 2 * m - 1) (C : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m G 0 0 ∨ C.owner = ringTerminalSite m G 2 1)
    (hfirstp : ringTerminalSite m G 0 0 ≠ octEdgeZigzag m F r)
    (hfirstq : ringTerminalSite m G 0 0 ≠ octEdgeZigzag m F (r + 2))
    (hlastp : ringTerminalSite m G 2 1 ≠ octEdgeZigzag m F r)
    (hlastq : ringTerminalSite m G 2 1 ≠ octEdgeZigzag m F (r + 2))
    (s : Fin 3) (n : ℕ) : (edgePPPFold m F r).pos s ≠ C.point n := by
  rcases hC with hC | hC
  · exact edgePPPFold_ne_Bcorner_column m (by omega) F (ringSideFrame G 0) r hr C hC
      (by rw [hC]; exact hfirstp) (by rw [hC]; exact hfirstq) s n
  · have hc : C.owner = octEdgeZigzag m (bulkReverseEdgeFrame (ringSideFrame G 2)) 3 :=
      hC.trans (ringSide_last_eq_reverse_three m (by omega) (ringSideFrame G 2))
    exact edgePPPFold_ne_B3_column m hm F (bulkReverseEdgeFrame (ringSideFrame G 2)) r hr C hc
      (by rw [hC]; exact hlastp) (by rw [hC]; exact hlastq)
      (by rw [ringLastReverse_start m (by omega) G]; exact hfirstp)
      (by rw [ringLastReverse_start m (by omega) G]; exact hfirstq) s n

theorem ringFold_ne_foreign_terminal_column (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j) (C : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m G 0 0 ∨ C.owner = ringTerminalSite m G 2 1)
    (i : Fin (dimerChain (3 * (m - 2))).length) (n : ℕ) :
    (ringFold m (by omega) heven F).pos i ≠ C.point n := by
  apply ringFold_property m (by omega) heven F (fun x => x ≠ C.point n) _ _ i
  · intro j r
    let r' : Fin (dimerChain (m - 3 + 1)).length :=
      ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
    have hf := ringForeignTerminal_linkOwnerExcluded m (by omega) F G hj j 0 0
    have hl := ringForeignTerminal_linkOwnerExcluded m (by omega) F G hj j 2 1
    exact edgeDimerFold_ne_column_of_PPP_ne (by omega : 1 ≤ m) (ringSideFrame F j)
      1 (m - 3) false (by omega) C (by
        intro k hk s v
        have hb := dimerLinkIndex_bounds 1 false k
        exact edgePPP_ne_ring_terminal_column m hm (ringSideFrame F j) G _ (by omega) C hC
          (by simpa using hf k hk 0) (by simpa using hf k hk 1)
          (by simpa using hl k hk 0) (by simpa using hl k hk 1) s v) r' n
  · intro c r
    exact edgePPP_ne_ring_terminal_column m hm (bulkReverseEdgeFrame (ringSideFrame F c.castSucc))
      G 1 (by omega) C hC
      (by rw [ringCorner_start_owner m (by omega) F c]
          exact ringTerminalSite_ne_small_faces m (by omega) G F hj.symm 0 c.succ 0 0)
      (by rw [ringCorner_end_owner m (by omega) F c]
          exact ringTerminalSite_ne_small_faces m (by omega) G F hj.symm 0 c.castSucc 0 1)
      (by rw [ringCorner_start_owner m (by omega) F c]
          exact ringTerminalSite_ne_small_faces m (by omega) G F hj.symm 2 c.succ 1 0)
      (by rw [ringCorner_end_owner m (by omega) F c]
          exact ringTerminalSite_ne_small_faces m (by omega) G F hj.symm 2 c.castSucc 1 1) r.rev n

theorem ringTerminalColumns_seeds_ne (m : ℕ) (hm : 30 ≤ m) (F G : OctEdgeFrame)
    (hj : F.j ≠ G.j) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0 ∨ C.owner = ringTerminalSite m F 2 1)
    (hD : D.owner = ringTerminalSite m G 0 0 ∨ D.owner = ringTerminalSite m G 2 1) : C.seed ≠ D.seed := by
  apply dangling_caps_ne_of_owner_ne m C.owner D.owner C.dir D.dir C.owner_mem D.owner_mem C.seed_outside
  rcases hC with hC | hC <;> rcases hD with hD | hD
  all_goals rw [hC, hD]
  all_goals exact ringTerminalSite_ne_small_faces m (by omega) F G hj _ _ _ _

end ProteinFolding.Tetrahedral.NearField

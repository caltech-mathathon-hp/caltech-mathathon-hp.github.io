import ProteinFolding.Tetrahedral.NearFieldRingWordPiece
import ProteinFolding.Tetrahedral.NearFieldRingFaceGeometry
import ProteinFolding.Tetrahedral.NearFieldPPPBorrowedFrameColumns
import ProteinFolding.Tetrahedral.NearFieldFrameCapColumns

/-! Rings off the reserved small face avoid every actual borrowed frame
column, including the left filler's special borrowed column at index two. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem ringFold_ne_frameBorrowPoint (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (hj : F.j ≠ 3)
    (a : ℕ) (ha : a % 2 = 0) (hlo : 2 ≤ a) (hhi : (a : ℤ) + 2 ≤ octRadius m) (mode : Bool)
    (hnear : mode = true ∨ 4 ≤ a) (hfar : mode = false ∨ (a : ℤ) + 4 ≤ octRadius m)
    (i : Fin (dimerChain (3 * (m - 2))).length) (n : ℕ) :
    (ringFold m (by omega) heven F).pos i ≠ frameBorrowPoint (by omega) a ha hlo hhi mode n := by
  apply ringFold_property m (by omega) heven F
    (fun x => x ≠ frameBorrowPoint (by omega) a ha hlo hhi mode n) _ _ i
  · intro j r
    let r' : Fin (dimerChain (m - 3 + 1)).length :=
      ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
    change (edgeDimerFold (by omega : 1 ≤ m) (ringSideFrame F j) 1 (m - 3) false (by omega)).pos r' ≠ _
    rcases edgeDimerFold_pos_cases (by omega : 1 ≤ m) (ringSideFrame F j) 1 (m - 3) false
        (by omega) r' with ⟨k, hk, s, hs⟩ | ⟨k, hk, s, hs⟩
    · rw [hs]
      intro heq
      apply frameBorrowPoint_outside (by omega : 1 ≤ m) a ha hlo hhi mode n
      rw [← heq]
      exact edgeDimerHsites_subset_oct (by omega : 1 ≤ m) (ringSideFrame F j) 1 (m - 3)
        (by omega) (dimerHIndex_mem_Hsites m (ringSideFrame F j) 1 (m - 3) false k hk s)
    · rw [hs]
      have hb := dimerLinkIndex_bounds 1 false k
      exact edgePPPFold_ne_frameBorrowPoint m (by omega) a ha hlo hhi mode hnear hfar
        (ringSideFrame F j) _ (by omega)
        (Or.inr (by rw [ringSideFrame_small]; exact hj)) s n
  · intro c r
    exact edgePPPFold_ne_frameBorrowPoint m (by omega) a ha hlo hhi mode hnear hfar
      (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 1 (by omega)
      (Or.inr (by change (ringSideFrame F c.castSucc).j ≠ 3; rw [ringSideFrame_small]; exact hj)) r.rev n

theorem Bcolumn_seed_ne_frameBorrowPoint (m : ℕ) (hm : 1 ≤ m) (C : DanglingColumn m)
    (hC : InBSublattice C.owner.val)
    (a : ℕ) (ha : a % 2 = 0) (hlo : 2 ≤ a) (hhi : (a : ℤ) + 2 ≤ octRadius m)
    (mode : Bool) (n : ℕ) : C.seed ≠ frameBorrowPoint hm a ha hlo hhi mode n := by
  cases n with
  | zero =>
    intro heq
    have hA := step_in_A hC C.dir
    have hB := step_in_B (frameEntryAnchor_inA hm a ha) 2
    change C.seed = frameLinkerCap m a at heq
    change InASublattice C.seed.val at hA
    rw [heq] at hA
    exact sublattices_disjoint _ hA hB
  | succ n =>
    exact (DanglingColumn.points_ne_of_owner_colours (frameBorrowColumn hm a ha hlo hhi mode) C
      (frameBorrowOwner_inA hm a ha mode) hC (n + 1) 0).symm

theorem cappedRingFold_ne_frameBorrowPoint (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (hj : F.j ≠ 3) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (a : ℕ) (ha : a % 2 = 0) (hlo : 2 ≤ a) (hhi : (a : ℤ) + 2 ≤ octRadius m) (mode : Bool)
    (hnear : mode = true ∨ 4 ≤ a) (hfar : mode = false ∨ (a : ℤ) + 4 ≤ octRadius m)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) (n : ℕ) :
    (cappedRingFold m hm heven F C D hC hD).pos i ≠ frameBorrowPoint (by omega) a ha hlo hhi mode n := by
  intro heq
  have hmem := (mem_foldSites (cappedRingFold m hm heven F C D hC hD) _).mpr ⟨i, heq⟩
  rw [cappedRingFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact Bcolumn_seed_ne_frameBorrowPoint m (by omega) C
      (by rw [hC]; exact ringTerminalSite_inB m (by omega) F 0 0) a ha hlo hhi mode n h.symm
  · obtain ⟨j, hj'⟩ := (mem_foldSites _ _).mp h
    exact ringFold_ne_frameBorrowPoint m hm heven F hj a ha hlo hhi mode hnear hfar j n hj'
  · exact Bcolumn_seed_ne_frameBorrowPoint m (by omega) D
      (by rw [hD]; exact ringTerminalSite_inB m (by omega) F 2 1) a ha hlo hhi mode n h.symm

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.NearFieldRingCaps
import ProteinFolding.Tetrahedral.NearFieldDimerBulkClearance

/-! The complete ring and its caps avoid the actual bulk interior and all
bulk endpoint columns, including every height used by far-field routing. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem ringTerminalSite_deleted (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (i : Fin 3) (e : Fin 2) : ringTerminalSite m F i e ∈ bulkDeletedEdges m :=
  edgeDimerHsites_subset_deleted (by omega : 1 ≤ m) (ringSideFrame F i) 1 (m - 3)
    (by omega) (ringTerminalSite_mem m hm F i e)

theorem ringSideFold_not_mem_bulkInterior (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (i : Fin (dimerChain (m - 2)).length) : (ringSideFold m hm F).pos i ∉ bulkInterior m := by
  let i' : Fin (dimerChain (m - 3 + 1)).length :=
    ⟨i.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact i.isLt⟩
  change (edgeDimerFold (by omega : 1 ≤ m) F 1 (m - 3) false (by omega)).pos i' ∉ bulkInterior m
  rcases edgeDimerFold_pos_cases (by omega : 1 ≤ m) F 1 (m - 3) false (by omega) i' with
    ⟨j, hj, s, hs⟩ | ⟨j, hj, s, hs⟩
  · rw [hs]
    intro h
    exact (Finset.mem_sdiff.mp h).2
      (edgeDimerHsites_subset_deleted (by omega : 1 ≤ m) F 1 (m - 3) (by omega)
        (dimerHIndex_mem_Hsites m F 1 (m - 3) false j hj s))
  · rw [hs]
    intro h
    have hb := dimerLinkIndex_bounds 1 false j
    exact edgePPPFold_outside (by omega : 1 ≤ m) F _ (by omega) s (Finset.mem_sdiff.mp h).1

theorem ringFold_not_mem_bulkInterior (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (i : Fin (dimerChain (3 * (m - 2))).length) :
    (ringFold m hm heven F).pos i ∉ bulkInterior m := by
  apply ringFold_property m hm heven F (fun x => x ∉ bulkInterior m) _ _ i
  · exact fun j r => ringSideFold_not_mem_bulkInterior m hm (ringSideFrame F j) r
  · intro c r h
    exact ringCornerFold_outside m hm _ r (Finset.mem_sdiff.mp h).1

theorem ringFold_ne_bulkEndColumn (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C : DanglingColumn m) (hC : C.owner ∈ bulkInterior m)
    (hend : (bulkCoverNeighbours m C.owner).card = 1)
    (i : Fin (dimerChain (3 * (m - 2))).length) (n : ℕ) :
    (ringFold m (by omega) heven F).pos i ≠ C.point n := by
  apply ringFold_property m (by omega) heven F (fun x => x ≠ C.point n) _ _ i
  · intro j r
    let r' : Fin (dimerChain (m - 3 + 1)).length :=
      ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
    exact edgeDimerFold_ne_bulkEndColumn m hm (ringSideFrame F j) 1 (m - 3) false
      (by omega) C hC hend r' n
  · intro c r
    exact edgePPPFold_ne_bulkEndColumn m hm (bulkReverseEdgeFrame (ringSideFrame F c.castSucc))
      1 (by omega) C hC hend r.rev n

theorem cappedRingFold_not_mem_bulkInterior (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) :
    (cappedRingFold m hm heven F C D hC hD).pos i ∉ bulkInterior m := by
  intro h
  have hmem := (mem_foldSites (cappedRingFold m hm heven F C D hC hD) _).mpr ⟨i, rfl⟩
  rw [cappedRingFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (hx | hx) | hx
  · rw [hx] at h
    exact C.seed_outside (Finset.mem_sdiff.mp h).1
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp hx
    rw [← hj] at h
    exact ringFold_not_mem_bulkInterior m (by omega) heven F j h
  · rw [hx] at h
    exact D.seed_outside (Finset.mem_sdiff.mp h).1

theorem cappedRingFold_ne_bulkEndColumn (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (D E : DanglingColumn m)
    (hD : D.owner = ringTerminalSite m F 0 0) (hE : E.owner = ringTerminalSite m F 2 1)
    (C : DanglingColumn m) (hC : C.owner ∈ bulkInterior m)
    (hend : (bulkCoverNeighbours m C.owner).card = 1)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) (n : ℕ) :
    (cappedRingFold m hm heven F D E hD hE).pos i ≠ C.point n := by
  intro heq
  have hmem := (mem_foldSites (cappedRingFold m hm heven F D E hD hE) _).mpr ⟨i, heq⟩
  rw [cappedRingFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · have hDm : D.owner ∈ bulkDeletedEdges m := by rw [hD]; exact ringTerminalSite_deleted m (by omega) F 0 0
    exact bulkColumn_ne_edgeColumn C D hC hDm n 0 h
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    exact ringFold_ne_bulkEndColumn m hm heven F C hC hend j n hj
  · have hEm : E.owner ∈ bulkDeletedEdges m := by rw [hE]; exact ringTerminalSite_deleted m (by omega) F 2 1
    exact bulkColumn_ne_edgeColumn C E hC hEm n 0 h

end ProteinFolding.Tetrahedral.NearField

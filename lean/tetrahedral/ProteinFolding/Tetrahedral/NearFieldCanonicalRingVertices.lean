import ProteinFolding.Tetrahedral.NearFieldRingBorrowedColumns

/-! Interior ring H sites avoid every octahedron vertex. Consequently the
complete capped ring avoids every column owned by a vertex. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem octVertex_tetraCoordinate_extreme (m : ℕ) (a : Fin 3) (positive : Bool) (d : Fin 4) :
    tetraCoordinate m (octVertexSite m a positive).val d = -octRadius m ∨
      tetraCoordinate m (octVertexSite m a positive).val d = octRadius m := by
  fin_cases a <;> cases positive <;> fin_cases d <;>
    dsimp [octVertexSite, octVertexCoordinates, octCentre, tetraCoordinate, octRadius] <;> omega

theorem ringEdgePoint_ne_vertex (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (r : ℕ)
    (hlo : 1 ≤ r) (hhi : r + 2 ≤ 2 * m - 1) (a : Fin 3) (positive : Bool) :
    octEdgeZigzag m F r ≠ octVertexSite m a positive := by
  have hm1 : 1 ≤ m := by omega
  intro heq
  by_cases hA : InASublattice (octEdgeZigzag m F r).val
  · have hmod := edgeZigzag_A_even hm1 F r hA
    have hr : r = 2 * (r / 2) := by omega
    have ha := (octEdgeZigzag_even hm1 F (r / 2)).2.2.2.1
    rw [← hr, heq] at ha
    rcases octVertex_tetraCoordinate_extreme m a positive F.a with hv | hv
    all_goals dsimp [octRadius] at ha hv
    all_goals omega
  · have hB := (inB_iff_not_inA _).mpr hA
    rw [heq] at hB
    exact sublattices_disjoint _ (octVertexCoordinates_inA m a positive) hB

theorem ringFold_ne_vertexSite (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (a : Fin 3) (positive : Bool)
    (i : Fin (dimerChain (3 * (m - 2))).length) :
    (ringFold m hm heven F).pos i ≠ octVertexSite m a positive := by
  have hm1 : 1 ≤ m := by omega
  apply ringFold_property m hm heven F (fun x => x ≠ octVertexSite m a positive) _ _ i
  · intro j r
    let r' : Fin (dimerChain (m - 3 + 1)).length :=
      ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
    change (edgeDimerFold hm1 (ringSideFrame F j) 1 (m - 3) false (by omega)).pos r' ≠ _
    rcases edgeDimerFold_pos_cases hm1 (ringSideFrame F j) 1 (m - 3) false
        (by omega) r' with ⟨k, hk, s, hs⟩ | ⟨k, hk, s, hs⟩
    · rw [hs]
      have hb := dimerHIndex_bounds 1 false k s
      exact ringEdgePoint_ne_vertex m hm (ringSideFrame F j) _ (by omega) (by omega) a positive
    · rw [hs]
      intro heq
      have hmem := octVertexSite_mem_octahedron hm1 a positive
      rw [← heq] at hmem
      have hb := dimerLinkIndex_bounds 1 false k
      exact edgePPPFold_outside hm1 (ringSideFrame F j) _ (by omega) s hmem
  · intro c r heq
    have hmem := octVertexSite_mem_octahedron hm1 a positive
    rw [← heq] at hmem
    exact ringCornerFold_outside m hm (ringSideFrame F c.castSucc) r hmem

theorem cappedRingFold_ne_vertexSite (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (a : Fin 3) (positive : Bool)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) :
    (cappedRingFold m hm heven F C D hC hD).pos i ≠ octVertexSite m a positive := by
  intro heq
  have hmem := (mem_foldSites (cappedRingFold m hm heven F C D hC hD) _).mpr ⟨i, heq⟩
  rw [cappedRingFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · have hv := octVertexSite_mem_octahedron (by omega : 1 ≤ m) a positive
    rw [h] at hv
    exact C.seed_dangling.1 hv
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    exact ringFold_ne_vertexSite m (by omega) heven F a positive j hj
  · have hv := octVertexSite_mem_octahedron (by omega : 1 ≤ m) a positive
    rw [h] at hv
    exact D.seed_dangling.1 hv

theorem ringFold_ne_vertexColumn (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C : DanglingColumn m) (a : Fin 3) (positive : Bool)
    (hC : C.owner = octVertexSite m a positive)
    (i : Fin (dimerChain (3 * (m - 2))).length) (n : ℕ) :
    (ringFold m (by omega) heven F).pos i ≠ C.point n := by
  apply ringFold_property m (by omega) heven F (fun x => x ≠ C.point n) _ _ i
  · intro j r
    let r' : Fin (dimerChain (m - 3 + 1)).length :=
      ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
    change (edgeDimerFold (by omega : 1 ≤ m) (ringSideFrame F j) 1 (m - 3) false
      (by omega)).pos r' ≠ C.point n
    rcases edgeDimerFold_pos_cases (by omega : 1 ≤ m) (ringSideFrame F j) 1 (m - 3)
        false (by omega) r' with ⟨k, hk, s, hs⟩ | ⟨k, hk, s, hs⟩
    · rw [hs]
      intro heq
      have hmem := edgeDimerHsites_subset_oct (by omega : 1 ≤ m) (ringSideFrame F j)
        1 (m - 3) (by omega) (dimerHIndex_mem_Hsites m (ringSideFrame F j) 1 (m - 3)
          false k hk s)
      rw [heq] at hmem
      exact C.point_outside n hmem
    · rw [hs]
      have hb := dimerLinkIndex_bounds 1 false k
      exact edgePPPFold_ne_vertex_column m (by omega) (ringSideFrame F j) _ (by omega)
        C a positive hC
        (by rw [hC]; exact (ringEdgePoint_ne_vertex m (by omega) (ringSideFrame F j)
          _ (by omega) (by omega) a positive).symm)
        (by rw [hC]; exact (ringEdgePoint_ne_vertex m (by omega) (ringSideFrame F j)
          _ (by omega) (by omega) a positive).symm) s n
  · intro c r
    exact edgePPPFold_ne_vertex_column m (by omega)
      (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 1 (by omega) C a positive hC
      (by rw [hC]; exact (ringEdgePoint_ne_vertex m (by omega)
        (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 1 (by omega) (by omega) a positive).symm)
      (by rw [hC]; exact (ringEdgePoint_ne_vertex m (by omega)
        (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) 3 (by omega) (by omega) a positive).symm)
      r.rev n

theorem cappedRingFold_ne_vertexColumn (m : ℕ) (hm : 30 ≤ m) (heven : m % 2 = 0)
    (F : OctEdgeFrame) (C D : DanglingColumn m)
    (hC : C.owner = ringTerminalSite m F 0 0) (hD : D.owner = ringTerminalSite m F 2 1)
    (E : DanglingColumn m) (a : Fin 3) (positive : Bool)
    (hE : E.owner = octVertexSite m a positive)
    (i : Fin (capWord (dimerChain (3 * (m - 2)))).length) (n : ℕ) :
    (cappedRingFold m hm heven F C D hC hD).pos i ≠ E.point n := by
  have hEA : InASublattice E.owner.val := by
    rw [hE]
    exact octVertexCoordinates_inA m a positive
  have hCB : InBSublattice C.owner.val := by
    rw [hC]
    exact ringTerminalSite_inB m (by omega) F 0 0
  have hDB : InBSublattice D.owner.val := by
    rw [hD]
    exact ringTerminalSite_inB m (by omega) F 2 1
  intro heq
  have hmem := (mem_foldSites (cappedRingFold m hm heven F C D hC hD) _).mpr ⟨i, heq⟩
  rw [cappedRingFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact DanglingColumn.points_ne_of_owner_colours E C hEA hCB n 0 h
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    exact ringFold_ne_vertexColumn m hm heven F E a positive hE j n hj
  · exact DanglingColumn.points_ne_of_owner_colours E D hEA hDB n 0 h

end ProteinFolding.Tetrahedral.NearField

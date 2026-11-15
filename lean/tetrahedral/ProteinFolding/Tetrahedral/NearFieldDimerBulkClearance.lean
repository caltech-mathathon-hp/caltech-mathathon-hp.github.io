import ProteinFolding.Tetrahedral.NearFieldCappedDimerDisjoint
import ProteinFolding.Tetrahedral.NearFieldPPPBulkClearance

/-! Every literal capped edge-chain unit avoids every actual bulk endpoint column. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgeDimerHsites_subset_deleted {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) : edgeDimerHsites m F base q ⊆ bulkDeletedEdges m := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have hi := i.isLt
  exact edgeZigzag_mem_deleted hm F (base + i.val) (by omega)

theorem edgeDimerFold_ne_bulkEndColumn (m : ℕ) (hm : 30 ≤ m) (F : OctEdgeFrame)
    (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (C : DanglingColumn m) (hC : C.owner ∈ bulkInterior m)
    (hend : (bulkCoverNeighbours m C.owner).card = 1)
    (i : Fin (dimerChain (q + 1)).length) (n : ℕ) :
    (edgeDimerFold (by omega) F base q reverse hroom).pos i ≠ C.point n := by
  have hm1 : 1 ≤ m := by omega
  rcases edgeDimerFold_pos_cases hm1 F base q reverse hroom i with ⟨j, hj, s, hs⟩ | ⟨j, hj, s, hs⟩
  · rw [hs]
    intro heq
    have hmem := edgeDimerHsites_subset_oct hm1 F base q hroom
      (dimerHIndex_mem_Hsites m F base q reverse j hj s)
    rw [heq] at hmem
    exact C.point_outside n hmem
  · rw [hs]
    have hb := dimerLinkIndex_bounds base reverse j
    exact edgePPPFold_ne_bulkEndColumn m hm F _ (by omega) C hC hend s n

theorem edgeDimerCap_ne_bulkColumn {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (D : DanglingColumn m)
    (hD : D.owner ∈ edgeDimerHsites m F base q) (C : DanglingColumn m)
    (hC : C.owner ∈ bulkInterior m) (n : ℕ) : D.seed ≠ C.point n := by
  exact (bulkColumn_ne_edgeColumn C D hC (edgeDimerHsites_subset_deleted hm F base q hroom hD) n 0).symm

theorem cappedEdgeDimerFold_ne_bulkEndColumn (m : ℕ) (hm : 30 ≤ m) (F : OctEdgeFrame)
    (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (D E : DanglingColumn m)
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hE : E.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1))
    (C : DanglingColumn m) (hC : C.owner ∈ bulkInterior m)
    (hend : (bulkCoverNeighbours m C.owner).card = 1)
    (i : Fin (capWord (dimerChain (q + 1))).length) (n : ℕ) :
    (cappedEdgeDimerFold (by omega) F base q reverse hroom D E hD hE).pos i ≠ C.point n := by
  have hm1 : 1 ≤ m := by omega
  intro heq
  have hmem : C.point n ∈ foldSites (cappedEdgeDimerFold hm1 F base q reverse hroom D E hD hE) :=
    (mem_foldSites _ _).mpr ⟨i, heq⟩
  rw [cappedEdgeDimerFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · have hDm : D.owner ∈ edgeDimerHsites m F base q := by
      rw [hD]
      exact dimerHIndex_mem_Hsites m F base q reverse 0 (by omega) 0
    exact edgeDimerCap_ne_bulkColumn hm1 F base q hroom D hDm C hC n h.symm
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    exact edgeDimerFold_ne_bulkEndColumn m hm F base q reverse hroom C hC hend j n hj
  · have hEm : E.owner ∈ edgeDimerHsites m F base q := by
      rw [hE]
      exact dimerHIndex_mem_Hsites m F base q reverse q le_rfl 1
    exact edgeDimerCap_ne_bulkColumn hm1 F base q hroom E hEm C hC n h.symm

end ProteinFolding.Tetrahedral.NearField

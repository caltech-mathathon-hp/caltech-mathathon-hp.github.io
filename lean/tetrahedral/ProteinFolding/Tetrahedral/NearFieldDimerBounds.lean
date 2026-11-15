import ProteinFolding.Tetrahedral.NearFieldCappedDimerDisjoint

/-! Actual capped dimer-chain folds lie entirely in the first solid skin. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgeDimerFold_mem_solid_one {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (i : Fin (dimerChain (q + 1)).length) :
    (edgeDimerFold hm F base q reverse hroom).pos i ∈ skinSolid m 1 := by
  rcases edgeDimerFold_pos_cases hm F base q reverse hroom i with ⟨j, hj, s, hs⟩ | ⟨j, hj, s, hs⟩
  · rw [hs]
    have ho := edgeDimerHsites_subset_oct hm F base q hroom
      (dimerHIndex_mem_Hsites m F base q reverse j hj s)
    have hz : octEdgeZigzag m F (dimerHIndex base reverse j s) ∈ skinSolid m 0 := by
      simpa only [skinSolid_zero] using ho
    exact skinSolid_mono m (by omega : 0 ≤ 1) hz
  · rw [hs]
    have hb := dimerLinkIndex_bounds base reverse j
    exact skin_subset_solid m 1 (edgePPPFold_mem_skin_one hm F _ (by omega) s)

theorem cappedEdgeDimerFold_mem_solid_one {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1))
    (i : Fin (capWord (dimerChain (q + 1))).length) :
    (cappedEdgeDimerFold hm F base q reverse hroom C D hC hD).pos i ∈ skinSolid m 1 := by
  have hmem := (mem_foldSites (cappedEdgeDimerFold hm F base q reverse hroom C D hC hD) _).mpr ⟨i, rfl⟩
  rw [cappedEdgeDimerFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · rw [h]
    exact C.point_zero_mem_solid_one
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    rw [← hj]
    exact edgeDimerFold_mem_solid_one hm F base q reverse hroom j
  · rw [h]
    exact D.point_zero_mem_solid_one

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.NearFieldDimerChainLocations

/-! Distinct H intervals give disjoint actual dimer-chain folds. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgeDimerHsites_subset_oct {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) : edgeDimerHsites m F base q ⊆ octahedron m := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have hi := i.isLt
  rcases octEdgeZigzag_mem hm F (show base + i.val < 2 * m - 1 by omega) with h | h
  · exact h.1.1
  · exact h.1.1

theorem edgeDimerLink_PPPs_disjoint {m : ℕ} (hm : 1 ≤ m) (F G : OctEdgeFrame)
    (base q base' q' : ℕ) (reverse reverse' : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (hroom' : base' + 2 * (q' + 1) ≤ 2 * m - 1)
    (hdis : Disjoint (edgeDimerHsites m F base q) (edgeDimerHsites m G base' q'))
    (j k : ℕ) (hj : j < q) (hk : k < q') (s t : Fin 3) :
    (edgePPPFold m F (dimerLinkIndex base reverse j)).pos s ≠
      (edgePPPFold m G (dimerLinkIndex base' reverse' k)).pos t := by
  have hjb := dimerLinkIndex_bounds base reverse j
  have hkb := dimerLinkIndex_bounds base' reverse' k
  have hne (a b : Fin 2) :
      octEdgeZigzag m F (dimerLinkIndex base reverse j + 2 * a.val) ≠
        octEdgeZigzag m G (dimerLinkIndex base' reverse' k + 2 * b.val) := by
    intro heq
    have hF := dimerLink_endpoint_mem_Hsites m F base q reverse j hj a
    have hG := dimerLink_endpoint_mem_Hsites m G base' q' reverse' k hk b
    rw [heq] at hF
    exact Finset.disjoint_left.mp hdis hF hG
  exact edgePPPFolds_disjoint_of_endpoints_ne hm F G _ _ (by omega) (by omega)
    (by simpa using hne 0 0) (by simpa using hne 0 1)
    (by simpa using hne 1 0) (by simpa using hne 1 1) s t

theorem edgeDimerFolds_disjoint {m : ℕ} (hm : 1 ≤ m) (F G : OctEdgeFrame)
    (base q base' q' : ℕ) (reverse reverse' : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (hroom' : base' + 2 * (q' + 1) ≤ 2 * m - 1)
    (hdis : Disjoint (edgeDimerHsites m F base q) (edgeDimerHsites m G base' q'))
    (i : Fin (dimerChain (q + 1)).length) (i' : Fin (dimerChain (q' + 1)).length) :
    (edgeDimerFold hm F base q reverse hroom).pos i ≠
      (edgeDimerFold hm G base' q' reverse' hroom').pos i' := by
  rcases edgeDimerFold_pos_cases hm F base q reverse hroom i with ⟨j, hj, s, hs⟩ | ⟨j, hj, s, hs⟩
  · rcases edgeDimerFold_pos_cases hm G base' q' reverse' hroom' i' with ⟨k, hk, t, ht⟩ | ⟨k, hk, t, ht⟩
    · rw [hs, ht]
      intro heq
      have hF := dimerHIndex_mem_Hsites m F base q reverse j hj s
      have hG := dimerHIndex_mem_Hsites m G base' q' reverse' k hk t
      rw [heq] at hF
      exact Finset.disjoint_left.mp hdis hF hG
    · rw [hs, ht]
      intro heq
      have hF := edgeDimerHsites_subset_oct hm F base q hroom
        (dimerHIndex_mem_Hsites m F base q reverse j hj s)
      have hkb := dimerLinkIndex_bounds base' reverse' k
      rw [heq] at hF
      exact edgePPPFold_outside hm G _ (by omega) t hF
  · rcases edgeDimerFold_pos_cases hm G base' q' reverse' hroom' i' with ⟨k, hk, t, ht⟩ | ⟨k, hk, t, ht⟩
    · rw [hs, ht]
      intro heq
      have hG := edgeDimerHsites_subset_oct hm G base' q' hroom'
        (dimerHIndex_mem_Hsites m G base' q' reverse' k hk t)
      have hjb := dimerLinkIndex_bounds base reverse j
      rw [← heq] at hG
      exact edgePPPFold_outside hm F _ (by omega) s hG
    · rw [hs, ht]
      exact edgeDimerLink_PPPs_disjoint hm F G base q base' q' reverse reverse'
        hroom hroom' hdis j k hj hk s t

end ProteinFolding.Tetrahedral.NearField

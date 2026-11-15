import ProteinFolding.Tetrahedral.NearFieldDimerChainFold

/-! Every chain site and every internal PPP endpoint has an explicit owner. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem dimerHIndex_mem_Hsites (m : ℕ) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (j : ℕ) (hj : j ≤ q) (s : Fin 2) :
    octEdgeZigzag m F (dimerHIndex base reverse j s) ∈ edgeDimerHsites m F base q := by
  have hb := dimerHIndex_bounds base reverse j s
  refine Finset.mem_image.mpr ⟨⟨dimerHIndex base reverse j s - base, by omega⟩, Finset.mem_univ _, ?_⟩
  congr 1
  change base + (dimerHIndex base reverse j s - base) = dimerHIndex base reverse j s
  omega

theorem dimerLink_endpoint_mem_Hsites (m : ℕ) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (j : ℕ) (hj : j < q) (s : Fin 2) :
    octEdgeZigzag m F (dimerLinkIndex base reverse j + 2 * s.val) ∈ edgeDimerHsites m F base q := by
  fin_cases s
  · simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, dimerHIndex_last] using
      dimerHIndex_mem_Hsites m F base q reverse j (by omega) 1
  · simpa only [dimerLinkIndex_next, Fin.val_one, Nat.mul_one] using
      dimerHIndex_mem_Hsites m F base q reverse (j + 1) (by omega) 0

theorem edgeDimerFold_pos_cases {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (i : Fin (dimerChain (q + 1)).length) :
    (∃ j, j ≤ q ∧ ∃ s : Fin 2, (edgeDimerFold hm F base q reverse hroom).pos i =
        octEdgeZigzag m F (dimerHIndex base reverse j s)) ∨
      (∃ j, j < q ∧ ∃ s : Fin 3, (edgeDimerFold hm F base q reverse hroom).pos i =
        (edgePPPFold m F (dimerLinkIndex base reverse j)).pos s) := by
  have hi : i.val < 5 * q + 2 := by simpa only [dimerChain_succ_length] using i.isLt
  by_cases hH : i.val % 5 < 2
  · exact Or.inl ⟨i.val / 5, dimerCurve_block_le q i.val hi, ⟨i.val % 5, hH⟩,
      by simp only [edgeDimerFold_pos, edgeDimerCurve, dif_pos hH]⟩
  · refine Or.inr ⟨i.val / 5, dimerCurve_Pblock_lt q i.val hi hH,
      ⟨i.val % 5 - 2, by have := Nat.mod_lt i.val (by decide : 0 < 5); omega⟩, ?_⟩
    simp only [edgeDimerFold_pos, edgeDimerCurve, dif_neg hH]

theorem edgeDimerFold_ne_cap_of_owner_not_mem {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (C : DanglingColumn m) (hC : C.owner ∉ edgeDimerHsites m F base q)
    (i : Fin (dimerChain (q + 1)).length) :
    (edgeDimerFold hm F base q reverse hroom).pos i ≠ C.seed := by
  rcases edgeDimerFold_pos_cases hm F base q reverse hroom i with ⟨j, hj, s, hs⟩ | ⟨j, hj, s, hs⟩
  · rw [hs]
    have hb := dimerHIndex_bounds base reverse j s
    have hmem : octEdgeZigzag m F (dimerHIndex base reverse j s) ∈ octahedron m := by
      rcases octEdgeZigzag_mem hm F (show dimerHIndex base reverse j s < 2 * m - 1 by omega) with h | h
      · exact h.1.1
      · exact h.1.1
    intro heq
    rw [heq] at hmem
    exact C.seed_outside hmem
  · rw [hs]
    have hb := dimerLinkIndex_bounds base reverse j
    have hr : dimerLinkIndex base reverse j + 2 < 2 * m - 1 := by omega
    apply facePPPFold_ne_cap_of_owner_ne m _ _ _ _ (edgePPPLateral_ne F _)
      (edgePPP_back_ne_normal F _) (edgePPP_normal_face hm F _ (by omega)) ?_ C ?_ ?_
    · rw [edgePPP_endpoint]
      rcases octEdgeZigzag_mem hm F hr with h | h <;> exact h.1.1
    · intro heq
      apply hC
      rw [heq]
      simpa using dimerLink_endpoint_mem_Hsites m F base q reverse j hj 0
    · rw [edgePPP_endpoint]
      intro heq
      apply hC
      rw [heq]
      simpa using dimerLink_endpoint_mem_Hsites m F base q reverse j hj 1

end ProteinFolding.Tetrahedral.NearField

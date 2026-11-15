import ProteinFolding.Tetrahedral.NearFieldDimerTethers
import ProteinFolding.Tetrahedral.NearFieldRingSideSeparation

/-! A literal chain avoids a valid edge PPP when neither PPP owner is an
internal link owner. Terminal H owners may be shared at the intended seams. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem edgeDimerFold_ne_edgePPPFold {m : ℕ} (hm : 1 ≤ m)
    (F G : OctEdgeFrame) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (r : ℕ) (hr : r + 2 < 2 * m - 1)
    (hs : DimerLinkOwnerExcluded m F base q reverse (octEdgeZigzag m G r))
    (ht : DimerLinkOwnerExcluded m F base q reverse (octEdgeZigzag m G (r + 2)))
    (i : Fin (dimerChain (q + 1)).length) (s : Fin 3) :
    (edgeDimerFold hm F base q reverse hroom).pos i ≠ (edgePPPFold m G r).pos s := by
  rcases edgeDimerFold_pos_cases hm F base q reverse hroom i with
      ⟨j, hj, a, he⟩ | ⟨j, hj, a, he⟩
  · rw [he]
    intro heq
    have hmem := edgeDimerHsites_subset_oct hm F base q hroom
      (dimerHIndex_mem_Hsites m F base q reverse j hj a)
    rw [heq] at hmem
    exact edgePPPFold_outside hm G r (by omega) s hmem
  · rw [he]
    have hb := dimerLinkIndex_bounds base reverse j
    exact edgePPPFolds_disjoint_of_endpoints_ne hm F G _ r (by omega) hr
      (by simpa using (hs j hj 0).symm) (by simpa using (ht j hj 0).symm)
      (by simpa using (hs j hj 1).symm) (by simpa using (ht j hj 1).symm) a s

theorem ringSideHsites_pairwise (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (edgeDimerHsites m (ringSideFrame F i) 1 (m - 3))
      (edgeDimerHsites m (ringSideFrame F j) 1 (m - 3)) := by
  have h01 := ringSideHsites_disjoint_next m hm F
  have h12 := ringSideHsites_disjoint_next m hm (ringNextFrame F)
  have h20 := ringSideHsites_disjoint_next m hm (ringNextFrame (ringNextFrame F))
  simp only [ringNextFrame_three] at h20
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact h01
    | exact h01.symm
    | exact h12
    | exact h12.symm
    | exact h20
    | exact h20.symm

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.NearFieldDimerChainFold
import ProteinFolding.Tetrahedral.NearFieldCapFold

/-! The endpoint caps belong to the very same self-avoiding dimer-chain fold. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgeDimerFold_ne_first_cap {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (C : DanglingColumn m)
    (howner : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (i : Fin (dimerChain (q + 1)).length) :
    (edgeDimerFold hm F base q reverse hroom).pos i ≠ C.seed := by
  have hi : i.val < 5 * q + 2 := by simpa only [dimerChain_succ_length] using i.isLt
  by_cases hH : i.val % 5 < 2
  · intro heq
    have hmem := edgeDimerCurve_H_mem hm F base q reverse hroom i.val hi hH
    rw [← edgeDimerFold_pos hm F base q reverse hroom i, heq] at hmem
    exact C.seed_outside hmem
  · rw [edgeDimerFold_pos]
    simp only [edgeDimerCurve, dif_neg hH]
    have hr := dimerCurve_Prange m base q reverse hroom i.val hi hH
    apply facePPPFold_ne_cap_of_owner_ne m _ _ _ _ (edgePPPLateral_ne F _)
      (edgePPP_back_ne_normal F _) (edgePPP_normal_face hm F _ (by omega)) ?_ C ?_ ?_
    · rw [edgePPP_endpoint]
      rcases octEdgeZigzag_mem hm F hr with h | h <;> exact h.1.1
    · rw [howner]
      intro heq
      exact dimerFirst_ne_link_endpoint base reverse (i.val / 5) 0
        (by simpa using octEdgeZigzag_injective hm F heq)
    · rw [howner, edgePPP_endpoint]
      intro heq
      exact dimerFirst_ne_link_endpoint base reverse (i.val / 5) 1
        (by simpa using octEdgeZigzag_injective hm F heq)

theorem edgeDimerFold_ne_last_cap {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (C : DanglingColumn m)
    (howner : C.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1))
    (i : Fin (dimerChain (q + 1)).length) :
    (edgeDimerFold hm F base q reverse hroom).pos i ≠ C.seed := by
  have hi : i.val < 5 * q + 2 := by simpa only [dimerChain_succ_length] using i.isLt
  by_cases hH : i.val % 5 < 2
  · intro heq
    have hmem := edgeDimerCurve_H_mem hm F base q reverse hroom i.val hi hH
    rw [← edgeDimerFold_pos hm F base q reverse hroom i, heq] at hmem
    exact C.seed_outside hmem
  · rw [edgeDimerFold_pos]
    simp only [edgeDimerCurve, dif_neg hH]
    have hr := dimerCurve_Prange m base q reverse hroom i.val hi hH
    have hj := dimerCurve_Pblock_lt q i.val hi hH
    apply facePPPFold_ne_cap_of_owner_ne m _ _ _ _ (edgePPPLateral_ne F _)
      (edgePPP_back_ne_normal F _) (edgePPP_normal_face hm F _ (by omega)) ?_ C ?_ ?_
    · rw [edgePPP_endpoint]
      rcases octEdgeZigzag_mem hm F hr with h | h <;> exact h.1.1
    · rw [howner]
      intro heq
      exact dimerLast_ne_link_endpoint base reverse q (i.val / 5) hj 0
        (by simpa using octEdgeZigzag_injective hm F heq)
    · rw [howner, edgePPP_endpoint]
      intro heq
      exact dimerLast_ne_link_endpoint base reverse q (i.val / 5) hj 1
        (by simpa using octEdgeZigzag_injective hm F heq)

theorem edgeDimerCaps_ne {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1)) : C.seed ≠ D.seed := by
  apply dangling_caps_ne_of_owner_ne m C.owner D.owner C.dir D.dir C.owner_mem D.owner_mem C.seed_outside
  rw [hC, hD]
  intro heq
  exact dimerFirst_ne_last base reverse q (octEdgeZigzag_injective hm F heq)

theorem edgeDimerFold_first_seam {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (C : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (i : Fin (dimerChain (q + 1)).length) (hi : i.val = 0) :
    tetrahedralLattice.Adj C.seed ((edgeDimerFold hm F base q reverse hroom).pos i) := by
  rw [edgeDimerFold_pos, hi]
  change tetrahedralLattice.Adj C.seed (edgeDimerCurve m F base reverse (5 * 0 + (0 : Fin 2).val))
  rw [edgeDimerCurve_H, ← hC]
  exact (step_adj C.owner C.dir).symm

theorem edgeDimerFold_last_seam {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (D : DanglingColumn m)
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1))
    (i : Fin (dimerChain (q + 1)).length) (hi : i.val + 1 = (dimerChain (q + 1)).length) :
    tetrahedralLattice.Adj ((edgeDimerFold hm F base q reverse hroom).pos i) D.seed := by
  have hiv : i.val = 5 * q + 1 := by have hlen := dimerChain_succ_length q; omega
  rw [edgeDimerFold_pos, hiv]
  change tetrahedralLattice.Adj (edgeDimerCurve m F base reverse (5 * q + (1 : Fin 2).val)) D.seed
  rw [edgeDimerCurve_H, ← hD]
  exact step_adj D.owner D.dir

def cappedEdgeDimerFold {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1)) :
    Fold tetrahedralLattice (capWord (dimerChain (q + 1))).length :=
  cappedWordFold (edgeDimerFold hm F base q reverse hroom) C.seed D.seed
    (by rw [dimerChain_succ_length]; omega)
    (fun i => (edgeDimerFold_ne_first_cap hm F base q reverse hroom C hC i).symm)
    (edgeDimerFold_ne_last_cap hm F base q reverse hroom D hD)
    (edgeDimerCaps_ne hm F base q reverse C D hC hD)
    (edgeDimerFold_first_seam hm F base q reverse hroom C hC)
    (edgeDimerFold_last_seam hm F base q reverse hroom D hD)

theorem cappedEdgeDimerFold_hSupport {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse q 1)) :
    hSupport (capWord (dimerChain (q + 1))) (cappedEdgeDimerFold hm F base q reverse hroom C D hC hD) =
      edgeDimerHsites m F base q := by
  rw [cappedEdgeDimerFold, cappedWordFold_hSupport, edgeDimerFold_hSupport]

end ProteinFolding.Tetrahedral.NearField

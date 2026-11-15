import ProteinFolding.Tetrahedral.NearFieldDimerChainCurve
import ProteinFolding.Tetrahedral.NearFieldPPPPairwiseEdges

/-! Self-avoidance of the complete, literal edge dimer walk. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem dimerCurve_block_le (q i : ℕ) (hi : i < 5 * q + 2) : i / 5 ≤ q := by
  omega

theorem dimerCurve_Pblock_lt (q i : ℕ) (hi : i < 5 * q + 2) (hP : ¬i % 5 < 2) :
    i / 5 < q := by omega

theorem dimerCurve_Hrange (m base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (i : ℕ) (hi : i < 5 * q + 2)
    (hH : i % 5 < 2) : dimerHIndex base reverse (i / 5) ⟨i % 5, hH⟩ < 2 * m - 1 := by
  have hb := dimerHIndex_bounds base reverse (i / 5) ⟨i % 5, hH⟩
  have hq := dimerCurve_block_le q i hi
  omega

theorem dimerCurve_Prange (m base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (i : ℕ) (hi : i < 5 * q + 2)
    (hP : ¬i % 5 < 2) : dimerLinkIndex base reverse (i / 5) + 2 < 2 * m - 1 := by
  have hb := dimerLinkIndex_bounds base reverse (i / 5)
  have hq := dimerCurve_Pblock_lt q i hi hP
  omega

theorem edgeDimerCurve_H_mem {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (i : ℕ)
    (hi : i < 5 * q + 2) (hH : i % 5 < 2) : edgeDimerCurve m F base reverse i ∈ octahedron m := by
  simp only [edgeDimerCurve, dif_pos hH]
  rcases octEdgeZigzag_mem hm F (dimerCurve_Hrange m base q reverse hroom i hi hH) with h | h
  · exact h.1.1
  · exact h.1.1

theorem edgeDimerCurve_P_outside {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (i : ℕ)
    (hi : i < 5 * q + 2) (hP : ¬i % 5 < 2) : edgeDimerCurve m F base reverse i ∉ octahedron m := by
  simp only [edgeDimerCurve, dif_neg hP]
  exact edgePPPFold_outside hm F _ (by have := dimerCurve_Prange m base q reverse hroom i hi hP; omega) _

theorem edgeDimerCurve_P_mem_skin_one {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (i : ℕ)
    (hi : i < 5 * q + 2) (hP : ¬i % 5 < 2) : edgeDimerCurve m F base reverse i ∈ skin m 1 := by
  simp only [edgeDimerCurve, dif_neg hP]
  exact edgePPPFold_mem_skin_one hm F _ (dimerCurve_Prange m base q reverse hroom i hi hP) _

theorem edgeDimerCurve_injective {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) :
    Function.Injective (fun i : Fin (5 * q + 2) => edgeDimerCurve m F base reverse i.val) := by
  intro i j heq
  change edgeDimerCurve m F base reverse i.val = edgeDimerCurve m F base reverse j.val at heq
  apply Fin.ext
  by_cases hi : i.val % 5 < 2
  · by_cases hj : j.val % 5 < 2
    · have he : dimerHIndex base reverse (i.val / 5) ⟨i.val % 5, hi⟩ =
          dimerHIndex base reverse (j.val / 5) ⟨j.val % 5, hj⟩ := by
        apply octEdgeZigzag_injective hm F
        simpa only [edgeDimerCurve, dif_pos hi, dif_pos hj] using heq
      have hp := @dimerHIndex_injective base reverse
        (i.val / 5, ⟨i.val % 5, hi⟩) (j.val / 5, ⟨j.val % 5, hj⟩) he
      have hd := congrArg (fun x : ℕ × Fin 2 => x.1) hp
      have hr := congrArg (fun x : ℕ × Fin 2 => x.2.val) hp
      change i.val / 5 = j.val / 5 at hd
      change i.val % 5 = j.val % 5 at hr
      omega
    · exfalso
      have hmem := edgeDimerCurve_H_mem hm F base q reverse hroom i.val i.isLt hi
      rw [heq] at hmem
      exact edgeDimerCurve_P_outside hm F base q reverse hroom j.val j.isLt hj hmem
  · by_cases hj : j.val % 5 < 2
    · exfalso
      have hmem := edgeDimerCurve_H_mem hm F base q reverse hroom j.val j.isLt hj
      rw [← heq] at hmem
      exact edgeDimerCurve_P_outside hm F base q reverse hroom i.val i.isLt hi hmem
    · have hri := dimerCurve_Prange m base q reverse hroom i.val i.isLt hi
      have hrj := dimerCurve_Prange m base q reverse hroom j.val j.isLt hj
      have hip : i.val % 5 - 2 < 3 := by have := Nat.mod_lt i.val (by decide : 0 < 5); omega
      have hjp : j.val % 5 - 2 < 3 := by have := Nat.mod_lt j.val (by decide : 0 < 5); omega
      have hep : (edgePPPFold m F (dimerLinkIndex base reverse (i.val / 5))).pos ⟨i.val % 5 - 2, hip⟩ =
          (edgePPPFold m F (dimerLinkIndex base reverse (j.val / 5))).pos ⟨j.val % 5 - 2, hjp⟩ := by
        simpa only [edgeDimerCurve, dif_neg hi, dif_neg hj] using heq
      by_cases hd : i.val / 5 = j.val / 5
      · rw [hd] at hep
        have hs := congrArg Fin.val ((edgePPPFold m F _).injective_pos hep)
        change i.val % 5 - 2 = j.val % 5 - 2 at hs
        omega
      · exfalso
        have hne (a b : Fin 2) :
            octEdgeZigzag m F (dimerLinkIndex base reverse (i.val / 5) + 2 * a.val) ≠
              octEdgeZigzag m F (dimerLinkIndex base reverse (j.val / 5) + 2 * b.val) := by
          intro h
          exact dimerLink_endpoints_ne base reverse _ _ hd a b (octEdgeZigzag_injective hm F h)
        exact edgePPPFolds_disjoint_of_endpoints_ne hm F F _ _ hri hrj
          (by simpa using hne 0 0) (by simpa using hne 0 1)
          (by simpa using hne 1 0) (by simpa using hne 1 1) _ _ hep

end ProteinFolding.Tetrahedral.NearField

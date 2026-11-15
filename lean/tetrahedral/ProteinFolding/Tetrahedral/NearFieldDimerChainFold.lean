import ProteinFolding.Tetrahedral.NearFieldDimerChainGeometry
import ProteinFolding.Tetrahedral.NearFieldDimerChainWords
import ProteinFolding.Tetrahedral.FoldAssembly

/-! Concrete folds of the literal dimer word, with exact hydrophobic support. -/

namespace ProteinFolding.Tetrahedral.NearField

def edgeDimerFoldCore {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) :
    Fold tetrahedralLattice (5 * q + 2) where
  pos i := edgeDimerCurve m F base reverse i.val
  injective_pos := edgeDimerCurve_injective hm F base q reverse hroom
  consecutive i j hij := by
    rw [← hij]
    exact edgeDimerCurve_consecutive m F base reverse i.val

def edgeDimerFold {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) :
    Fold tetrahedralLattice (dimerChain (q + 1)).length :=
  (edgeDimerFoldCore hm F base q reverse hroom).onLength (dimerChain_succ_length q)

theorem edgeDimerFold_pos {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (i : Fin (dimerChain (q + 1)).length) :
    (edgeDimerFold hm F base q reverse hroom).pos i = edgeDimerCurve m F base reverse i.val := rfl

theorem edgeDimerFold_H {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (j : ℕ) (hj : j ≤ q) (s : Fin 2) :
    (edgeDimerFold hm F base q reverse hroom).pos
      ⟨5 * j + s.val, by rw [dimerChain_succ_length]; omega⟩ =
      octEdgeZigzag m F (dimerHIndex base reverse j s) :=
  edgeDimerCurve_H m F base reverse j s

def edgeDimerHsites (m : ℕ) (F : OctEdgeFrame) (base q : ℕ) : Finset Site :=
  Finset.univ.image (fun i : Fin (2 * (q + 1)) => octEdgeZigzag m F (base + i.val))

theorem edgeDimerHsites_card {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ) :
    (edgeDimerHsites m F base q).card = 2 * (q + 1) := by
  rw [edgeDimerHsites, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    have he := octEdgeZigzag_injective hm F hij
    omega

theorem edgeDimerFold_hSupport {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) :
    hSupport (dimerChain (q + 1)) (edgeDimerFold hm F base q reverse hroom) =
      edgeDimerHsites m F base q := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨i, hH, rfl⟩ := (mem_hSupport _ _ p).mp hp
    have hmod : i.val % 5 < 2 := by
      rw [dimerChain_get_mod5] at hH
      by_contra hn
      simp only [if_neg hn] at hH
      cases hH
    have hb := dimerHIndex_bounds base reverse (i.val / 5) ⟨i.val % 5, hmod⟩
    have hq := dimerCurve_block_le q i.val (by simpa only [dimerChain_succ_length] using i.isLt)
    refine Finset.mem_image.mpr ⟨⟨dimerHIndex base reverse (i.val / 5) ⟨i.val % 5, hmod⟩ - base,
      by omega⟩, Finset.mem_univ _, ?_⟩
    rw [edgeDimerFold_pos]
    simp only [edgeDimerCurve, dif_pos hmod]
    congr 1
    omega
  · rw [edgeDimerHsites_card hm, hSupport_card, dimerChain_count]

theorem edgeDimerFold_P_skin {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (base q : ℕ)
    (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (i : Fin (dimerChain (q + 1)).length) (hP : (dimerChain (q + 1)).get i = .P) :
    (edgeDimerFold hm F base q reverse hroom).pos i ∈ skin m 1 := by
  have hn : ¬i.val % 5 < 2 := by
    intro h
    rw [dimerChain_get_mod5] at hP
    simp only [if_pos h] at hP
    cases hP
  exact edgeDimerCurve_P_mem_skin_one hm F base q reverse hroom i.val
    (by simpa only [dimerChain_succ_length] using i.isLt) hn

end ProteinFolding.Tetrahedral.NearField

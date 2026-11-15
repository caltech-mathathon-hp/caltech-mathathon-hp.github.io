import ProteinFolding.Tetrahedral.NearFieldDimerChainDisjoint
import ProteinFolding.Tetrahedral.NearFieldPPPFrameSeparation

/-! A dimer-chain interval disjoint from the frame Hs avoids its whole P link. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem edgeDimerFold_ne_framePFold {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (base q : ℕ) (reverse : Bool) (hroom : base + 2 * (q + 1) ≤ 2 * m - 1)
    (f : ℕ) (kind : Fin 6) (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius m)
    (hstart : frameStartH m f kind ∉ edgeDimerHsites m F base q)
    (hend : frameEndH m f kind ∉ edgeDimerHsites m F base q)
    (i : Fin (dimerChain (q + 1)).length) (t : Fin (nearFrameLength kind - 2)) :
    (edgeDimerFold hm F base q reverse hroom).pos i ≠ (framePFold m f kind hf).pos t := by
  rcases edgeDimerFold_pos_cases hm F base q reverse hroom i with ⟨j, hj, s, hs⟩ | ⟨j, hj, s, hs⟩
  · rw [hs]
    intro heq
    have hmem := edgeDimerHsites_subset_oct hm F base q hroom
      (dimerHIndex_mem_Hsites m F base q reverse j hj s)
    rw [heq] at hmem
    exact framePFold_outside m f kind hf t hmem
  · rw [hs]
    have hb := dimerLinkIndex_bounds base reverse j
    have hne (a : Fin 2) (p : Site) (hp : p ∉ edgeDimerHsites m F base q) :
        octEdgeZigzag m F (dimerLinkIndex base reverse j + 2 * a.val) ≠ p := by
      intro heq
      apply hp
      rw [← heq]
      exact dimerLink_endpoint_mem_Hsites m F base q reverse j hj a
    exact edgePPPFold_ne_framePFold m f hm F _ (by omega) kind hf hflo hfhi
      (by simpa using hne 0 _ hstart) (by simpa using hne 0 _ hend)
      (by simpa using hne 1 _ hstart) (by simpa using hne 1 _ hend) s t

theorem edgeDimerCap_ne_framePFold (m : ℕ) (F : OctEdgeFrame) (base q : ℕ)
    (C : DanglingColumn m) (hC : C.owner ∈ edgeDimerHsites m F base q)
    (f : ℕ) (kind : Fin 6) (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius m)
    (hstart : frameStartH m f kind ∉ edgeDimerHsites m F base q)
    (hend : frameEndH m f kind ∉ edgeDimerHsites m F base q)
    (t : Fin (nearFrameLength kind - 2)) : C.seed ≠ (framePFold m f kind hf).pos t := by
  apply danglingCap_ne_framePFold m f kind hf hflo hfhi C.owner C.dir C.owner_mem C.seed_outside
  · intro heq
    exact hstart (heq ▸ hC)
  · intro heq
    exact hend (heq ▸ hC)

end ProteinFolding.Tetrahedral.NearField

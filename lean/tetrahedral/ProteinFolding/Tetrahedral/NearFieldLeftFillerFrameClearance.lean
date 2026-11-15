import ProteinFolding.Tetrahedral.NearFieldLeftFillerFrameOwners
import ProteinFolding.Tetrahedral.NearFieldPPPFrameSeparation

/-! The complete special left filler avoids every Appendix C frame P-link. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

private theorem mem_ne_not_mem {α : Type*} [DecidableEq α] {S : Finset α}
    {x y : α} (hx : x ∈ S) (hy : y ∉ S) : x ≠ y := by
  intro h
  exact hy (h ▸ hx)

private theorem column_seed_ne_frameP (m f : ℕ) (kind : Fin 6)
    (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius m)
    (C : DanglingColumn m) (hstart : C.owner ≠ frameStartH m f kind)
    (hend : C.owner ≠ frameEndH m f kind) (t : Fin (nearFrameLength kind - 2)) :
    C.seed ≠ (framePFold m f kind hf).pos t := by
  exact danglingCap_ne_framePFold m f kind hf hflo hfhi C.owner C.dir
    C.owner_mem C.seed_outside hstart hend t

theorem leftFillerLink_endpoint_mem (p : ConstructionParameters) (j : ℕ)
    (hj : j < p.leftFiller - 1) (a : Fin 2) :
    octEdgeZigzag p.side trackEdgeFrame (dimerLinkIndex 0 false j + 2 * a.val) ∈ leftFillerHsites p := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hbase : 1 ≤ dimerLinkIndex 0 false j := by
    by_cases hj0 : j = 0
    · subst j
      decide
    · have hb := dimerLinkIndex_bounds 0 false j
      omega
  apply Finset.mem_insert_of_mem
  apply Finset.mem_erase.mpr
  constructor
  · intro heq
    have hi := octEdgeZigzag_injective hm trackEdgeFrame heq
    omega
  · exact dimerLink_endpoint_mem_Hsites p.side trackEdgeFrame 0 (p.leftFiller - 1) false j hj a

theorem leftFillerFold_ne_framePFold (p : ConstructionParameters) (f : ℕ) (kind : Fin 6)
    (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side)
    (i : Fin (dimerChain p.leftFiller).length) (t : Fin (nearFrameLength kind - 2)) :
    (leftFillerFold p).pos i ≠ (framePFold p.side f kind hf).pos t := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hi : i.val < 5 * (p.leftFiller - 1) + 2 := by
    rw [← leftFiller_word_length p]
    exact i.isLt
  by_cases hi0 : i.val = 0
  · rw [leftFillerFold_first p i hi0]
    with_reducible
      exact mem_ne_not_mem (leftFillerStart_mem_oct p) (framePFold_outside p.side f kind hf t)
  · rw [leftFillerFold_pos, leftFillerCurve, if_neg hi0]
    by_cases hH : i.val % 5 < 2
    · with_reducible
        exact mem_ne_not_mem
          (edgeDimerCurve_H_mem hm trackEdgeFrame 0 (p.leftFiller - 1) false
            (leftFiller_room p) i.val hi hH)
          (framePFold_outside p.side f kind hf t)
    · simp only [edgeDimerCurve, dif_neg hH]
      have hj := dimerCurve_Pblock_lt (p.leftFiller - 1) i.val hi hH
      have hr := dimerCurve_Prange p.side 0 (p.leftFiller - 1) false (leftFiller_room p) i.val hi hH
      have hne (a : Fin 2) (last : Bool) :
          octEdgeZigzag p.side trackEdgeFrame (dimerLinkIndex 0 false (i.val / 5) + 2 * a.val) ≠
            if last then frameEndH p.side f kind else frameStartH p.side f kind := by
        have hmem := leftFillerLink_endpoint_mem p (i.val / 5) hj a
        with_reducible
          exact mem_ne_not_mem hmem (leftFiller_excludes_frameH p f kind hflo hfhi last)
      exact edgePPPFold_ne_framePFold p.side f hm trackEdgeFrame _ hr kind hf hflo hfhi
        (by simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using hne 0 false)
        (by simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using hne 0 true)
        (by simpa only [Fin.val_one, Nat.mul_one] using hne 1 false)
        (by simpa only [Fin.val_one, Nat.mul_one] using hne 1 true) _ t

theorem leftFillerCap_ne_framePFold (p : ConstructionParameters) (C : DanglingColumn p.side)
    (hC : C.owner ∈ leftFillerHsites p) (f : ℕ) (kind : Fin 6)
    (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side)
    (t : Fin (nearFrameLength kind - 2)) : C.seed ≠ (framePFold p.side f kind hf).pos t := by
  have hs := leftFiller_excludes_frameH p f kind hflo hfhi false
  have he := leftFiller_excludes_frameH p f kind hflo hfhi true
  simp only [Bool.false_eq_true, if_false, if_true] at hs he
  with_reducible
    exact column_seed_ne_frameP p.side f kind hf hflo hfhi C
      (mem_ne_not_mem hC hs) (mem_ne_not_mem hC he) t

theorem leftFillerLast_mem_Hsites (p : ConstructionParameters) :
    octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2) ∈ leftFillerHsites p := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply Finset.mem_insert_of_mem
  apply Finset.mem_erase.mpr
  constructor
  · intro heq
    have hi := octEdgeZigzag_injective hm trackEdgeFrame heq
    have hl := p.leftFiller_ge
    omega
  · rw [← leftFillerLast_index p]
    exact dimerHIndex_mem_Hsites p.side trackEdgeFrame 0 (p.leftFiller - 1) false
      (p.leftFiller - 1) le_rfl 1

theorem cappedLeftFillerFold_ne_framePFold (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2))
    (f : ℕ) (kind : Fin 6) (hf : f % 2 = 1) (hflo : 5 ≤ f)
    (hfhi : (f : ℤ) + 10 ≤ octRadius p.side)
    (i : Fin (capWord (dimerChain p.leftFiller)).length) (t : Fin (nearFrameLength kind - 2)) :
    (cappedLeftFillerFold p C D hC hD).pos i ≠ (framePFold p.side f kind hf).pos t := by
  intro heq
  have hmem := (mem_foldSites (cappedLeftFillerFold p C D hC hD) _).mpr ⟨i, heq⟩
  rw [cappedLeftFillerFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · apply leftFillerCap_ne_framePFold p C _ f kind hf hflo hfhi t h.symm
    rw [hC]
    exact Finset.mem_insert_self _ _
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    exact leftFillerFold_ne_framePFold p f kind hf hflo hfhi j t hj
  · apply leftFillerCap_ne_framePFold p D _ f kind hf hflo hfhi t h.symm
    rw [hD]
    exact leftFillerLast_mem_Hsites p

end ProteinFolding.Tetrahedral.NearField

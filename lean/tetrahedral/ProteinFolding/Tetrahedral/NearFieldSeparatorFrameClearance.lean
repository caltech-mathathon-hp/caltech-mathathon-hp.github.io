import ProteinFolding.Tetrahedral.NearFieldSeparatorFrameOwners
import ProteinFolding.Tetrahedral.NearFieldDimerChainFrame
import ProteinFolding.Tetrahedral.NearFieldSeparatorCaps
import ProteinFolding.Tetrahedral.NearFieldFrameTethers

/-! The complete capped separator units avoid every actual Appendix C frame P-link. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

theorem separatorFold_ne_framePFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (f : ℕ) (kind : Fin 6) (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side)
    (hentry : kind = 1 → f % 6 = 5) (hexit : kind = 4 → f % 10 = 5)
    (i : Fin (p.separatorWord k).length) (t : Fin (nearFrameLength kind - 2)) :
    (separatorFold p k hk).pos i ≠ (framePFold p.side f kind hf).pos t := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hlen := nearFrameLength_ge_five kind
  apply separatorFold_property p k hk (fun x => x ≠ (framePFold p.side f kind hf).pos t) _ _ _ _ _ i
  · exact fun j => edgeDimerFold_ne_framePFold hm entryEdgeFrame (6 * (k + 1)) 0 false
      (separatorEntry_room p k hk) f kind hf hflo hfhi
      (separatorEntry_excludes_frameH p k hk f kind hfhi hentry false)
      (separatorEntry_excludes_frameH p k hk f kind hfhi hentry true) j t
  · intro j
    rw [entryTetherWordFold_pos]
    exact entryTetherFold_ne_frameP p k hk f hf kind hentry hflo hfhi _
      ⟨t.val + 1, by have ht := t.isLt; omega⟩
      (by change 0 < t.val + 1; omega)
      (by change t.val + 1 + 1 < nearFrameLength kind; have ht := t.isLt; omega)
  · exact fun j => edgeDimerFold_ne_framePFold hm trackEdgeFrame (2 * p.separatorIndex k) 1 true
      (separatorCenter_room p k hk) f kind hf hflo hfhi
      (separatorCenter_excludes_frameH p k hk f kind hfhi false)
      (separatorCenter_excludes_frameH p k hk f kind hfhi true) j t
  · intro j
    rw [exitTetherWordFold_pos]
    exact exitTetherFold_ne_frameP p k hk f hf kind hexit hflo hfhi _
      ⟨t.val + 1, by have ht := t.isLt; omega⟩
      (by change 0 < t.val + 1; omega)
      (by change t.val + 1 + 1 < nearFrameLength kind; have ht := t.isLt; omega)
  · exact fun j => edgeDimerFold_ne_framePFold hm exitEdgeFrame (10 * p.exitSlot k + 6) 2 true
      (separatorExit_room p k) f kind hf hflo hfhi
      (separatorExit_excludes_frameH p k f kind hfhi hexit false)
      (separatorExit_excludes_frameH p k f kind hfhi hexit true) j t

theorem separatorFirstCap_ne_framePFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C : DanglingColumn p.side) (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (f : ℕ) (kind : Fin 6) (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side)
    (hentry : kind = 1 → f % 6 = 5) (t : Fin (nearFrameLength kind - 2)) :
    C.seed ≠ (framePFold p.side f kind hf).pos t := by
  have hCm : C.owner ∈ edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0 := by
    rw [hC]
    exact dimerHIndex_mem_Hsites p.side entryEdgeFrame (6 * (k + 1)) 0 false 0 le_rfl 0
  apply danglingCap_ne_framePFold p.side f kind hf hflo hfhi C.owner C.dir C.owner_mem C.seed_outside
  · intro heq
    rw [heq] at hCm
    exact separatorEntry_excludes_frameH p k hk f kind hfhi hentry false hCm
  · intro heq
    rw [heq] at hCm
    exact separatorEntry_excludes_frameH p k hk f kind hfhi hentry true hCm

theorem separatorLastCap_ne_framePFold (p : ConstructionParameters) (k : ℕ)
    (D : DanglingColumn p.side) (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (f : ℕ) (kind : Fin 6) (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side)
    (hexit : kind = 4 → f % 10 = 5) (t : Fin (nearFrameLength kind - 2)) :
    D.seed ≠ (framePFold p.side f kind hf).pos t := by
  have hDm : D.owner ∈ edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 := by
    rw [hD]
    exact dimerHIndex_mem_Hsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2 true 2 le_rfl 1
  apply danglingCap_ne_framePFold p.side f kind hf hflo hfhi D.owner D.dir D.owner_mem D.seed_outside
  · intro heq
    rw [heq] at hDm
    exact separatorExit_excludes_frameH p k f kind hfhi hexit false hDm
  · intro heq
    rw [heq] at hDm
    exact separatorExit_excludes_frameH p k f kind hfhi hexit true hDm

theorem cappedSeparatorFold_ne_framePFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side) (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (f : ℕ) (kind : Fin 6) (hf : f % 2 = 1) (hflo : 5 ≤ f) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side)
    (hentry : kind = 1 → f % 6 = 5) (hexit : kind = 4 → f % 10 = 5)
    (i : Fin (capWord (p.separatorWord k)).length) (t : Fin (nearFrameLength kind - 2)) :
    (cappedSeparatorFold p k hk C D hC hD).pos i ≠ (framePFold p.side f kind hf).pos t := by
  intro heq
  have hmem := (mem_foldSites (cappedSeparatorFold p k hk C D hC hD) _).mpr ⟨i, heq⟩
  change (framePFold p.side f kind hf).pos t ∈ foldSites (cappedWordFold _ _ _ _ _ _ _ _ _) at hmem
  rw [cappedWordFold_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact separatorFirstCap_ne_framePFold p k hk C hC f kind hf hflo hfhi hentry t h.symm
  · obtain ⟨j, hj⟩ := (mem_foldSites _ _).mp h
    exact separatorFold_ne_framePFold p k hk f kind hf hflo hfhi hentry hexit j t hj
  · exact separatorLastCap_ne_framePFold p k D hD f kind hf hflo hfhi hexit t h.symm

end ProteinFolding.Tetrahedral.NearField

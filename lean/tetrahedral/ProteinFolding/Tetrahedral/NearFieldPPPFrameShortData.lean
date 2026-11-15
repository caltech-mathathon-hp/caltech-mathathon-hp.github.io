import ProteinFolding.Tetrahedral.NearFieldPPPFrameLong

/-! The three short Appendix C frame links are exactly O2 PPPs. -/

namespace ProteinFolding.Tetrahedral.NearField

def shortFrameNormal (kind : Fin 6) : Fin 4 := if kind = 2 then 2 else 0
def shortFrameBack (kind : Fin 6) : Fin 4 := if kind = 2 then 1 else 2
def shortFrameForward (kind : Fin 6) : Fin 4 := if kind = 2 then 0 else 1

theorem shortFrame_length (kind : Fin 6) (hkind : kind = 2 ∨ kind = 3 ∨ kind = 5) :
    nearFrameLength kind = 5 := by rcases hkind with rfl | rfl | rfl <;> rfl

theorem shortFrame_directions (kind : Fin 6) (hkind : kind = 2 ∨ kind = 3 ∨ kind = 5) :
    nearFrameDirection kind 0 = shortFrameNormal kind ∧
    nearFrameDirection kind 1 = shortFrameBack kind ∧
    nearFrameDirection kind 2 = shortFrameForward kind ∧
    nearFrameDirection kind 3 = shortFrameNormal kind := by
  rcases hkind with rfl | rfl | rfl <;> decide

theorem shortFrame_distinct (kind : Fin 6) :
    shortFrameBack kind ≠ shortFrameForward kind ∧
    shortFrameBack kind ≠ shortFrameNormal kind ∧ shortFrameForward kind ≠ shortFrameNormal kind := by
  revert kind
  decide

def frameHeadPoint (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1) (r : Fin 5) : Site :=
  nearFramePoint m q kind hq ⟨r.val, by have h := nearFrameLength_ge_five kind; have hr := r.isLt; omega⟩

theorem shortFrame_steps (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hkind : kind = 2 ∨ kind = 3 ∨ kind = 5) :
    frameHeadPoint m q kind hq 1 = step (frameHeadPoint m q kind hq 0) (shortFrameNormal kind) ∧
    frameHeadPoint m q kind hq 2 = step (step (frameHeadPoint m q kind hq 0) (shortFrameNormal kind)) (shortFrameBack kind) ∧
    frameHeadPoint m q kind hq 3 = step (step (step (frameHeadPoint m q kind hq 0) (shortFrameNormal kind))
      (shortFrameBack kind)) (shortFrameForward kind) ∧
    frameHeadPoint m q kind hq 4 = faceFourStep (frameHeadPoint m q kind hq 0)
      (shortFrameNormal kind) (shortFrameBack kind) (shortFrameForward kind) := by
  have hn := nearFrameLength_ge_five kind
  have hd := shortFrame_directions kind hkind
  have h1 := nearFramePoint_step m q kind hq ⟨0, by omega⟩
  have h2 := nearFramePoint_step m q kind hq ⟨1, by omega⟩
  have h3 := nearFramePoint_step m q kind hq ⟨2, by omega⟩
  have h4 := nearFramePoint_step m q kind hq ⟨3, by omega⟩
  change frameHeadPoint m q kind hq 1 = step (frameHeadPoint m q kind hq 0) (nearFrameDirection kind 0) at h1
  change frameHeadPoint m q kind hq 2 = step (frameHeadPoint m q kind hq 1) (nearFrameDirection kind 1) at h2
  change frameHeadPoint m q kind hq 3 = step (frameHeadPoint m q kind hq 2) (nearFrameDirection kind 2) at h3
  change frameHeadPoint m q kind hq 4 = step (frameHeadPoint m q kind hq 3) (nearFrameDirection kind 3) at h4
  rw [hd.1] at h1
  rw [hd.2.1, h1] at h2
  rw [hd.2.2.1, h2] at h3
  rw [hd.2.2.2, h3] at h4
  exact ⟨h1, h2, h3, h4⟩

theorem shortFrame_head_start (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) :
    frameHeadPoint m q kind hq 0 = frameStartH m q kind :=
  nearFrame_start_eq m q kind hq hqlo hqhi

theorem shortFrame_head_end (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hkind : kind = 2 ∨ kind = 3 ∨ kind = 5)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) :
    frameHeadPoint m q kind hq 4 = frameEndH m q kind := by
  have h := nearFrame_end_eq m q kind hq hqlo hqhi
  have hn := shortFrame_length kind hkind
  simpa only [hn, frameHeadPoint, frameEndH] using h

theorem shortFrame_endpoint (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hkind : kind = 2 ∨ kind = 3 ∨ kind = 5)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) :
    faceFourStep (frameStartH m q kind) (shortFrameNormal kind)
      (shortFrameBack kind) (shortFrameForward kind) = frameEndH m q kind := by
  have h := (shortFrame_steps m q kind hq hkind).2.2.2
  rw [shortFrame_head_start m q kind hq hqlo hqhi, shortFrame_head_end m q kind hq hkind hqlo hqhi] at h
  exact h.symm

theorem shortFrame_face (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hkind : kind = 2 ∨ kind = 3 ∨ kind = 5)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) :
    OctBigFace m (shortFrameNormal kind) (frameStartH m q kind) ∨
      OctSmallFace m (shortFrameNormal kind) (frameStartH m q kind) := by
  have hmem := frameHs_mem_oct m q kind hq hqlo hqhi
  have hA := nearFramePoint_inA m q kind hq
    ⟨0, by have h := nearFrameLength_ge_five kind; omega⟩
    (by change nearFrameIsA kind 0; rcases hkind with rfl | rfl | rfl <;> decide)
  rw [nearFrame_start_eq m q kind hq hqlo hqhi] at hA
  refine Or.inl ⟨hmem.1, hA, ?_⟩
  unfold frameStartH
  rw [← nearFrame_start_eq m q kind hq hqlo hqhi]
  change tetraCoordinate m (nearFrameCoordinates m q kind 0) (shortFrameNormal kind) = octRadius m
  rcases hkind with rfl | rfl | rfl
  all_goals dsimp [nearFrameCoordinates, nearFrameReference, nearFrameOffset, nearFrameOffsetTriple,
    shortFrameNormal, tetraCoordinate, octRadius]
  all_goals omega

theorem shortFrame_Ppoint (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hkind : kind = 2 ∨ kind = 3 ∨ kind = 5)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) (s : Fin 3) :
    nearFramePoint m q kind hq ⟨s.val + 1, by have h := nearFrameLength_ge_five kind; have hs := s.isLt; omega⟩ =
      (facePPPFold (frameStartH m q kind) (shortFrameNormal kind) (shortFrameBack kind)
        (shortFrameForward kind) (shortFrame_distinct kind).1).pos s := by
  have hs := shortFrame_steps m q kind hq hkind
  rw [shortFrame_head_start m q kind hq hqlo hqhi] at hs
  fin_cases s
  · exact hs.1
  · exact hs.2.1
  · exact hs.2.2.1

end ProteinFolding.Tetrahedral.NearField

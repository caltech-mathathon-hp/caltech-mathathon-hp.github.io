import ProteinFolding.Tetrahedral.FrameForcingMiddle
import ProteinFolding.Tetrahedral.FrameForcingIncidence

/-! The actual incoming and outgoing P3 links use different dangling sites
of the middle vertex, so the forced edges have distinct big faces. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

theorem frame_middle_big_faces_distinct (p : ConstructionParameters)
    (P : OctWordPath p.side p.frameWord) (F₁ F₂ : OctEdgeFrame)
    (hf₁ : ∀ j ≤ p.frameGaps1.length, P.site (1 + frameHOffset p.frameGaps1 j) =
      octEdgeZigzag p.side F₁ (((p.frameGaps1.take j).map frameGapAdvance).sum))
    (hf₂ : ∀ j ≤ p.frameGaps2.length, P.site (p.framePart1.length + frameHOffset p.frameGaps2 j) =
      octEdgeZigzag p.side F₂ (((p.frameGaps2.take j).map frameGapAdvance).sum)) :
    F₁.k ≠ F₂.k := by
  have hm := p.side_ge
  have hmid := p.framePart1_length_ge_five
  have hspan := p.frame_middle_span_bound
  have hinEnd : p.framePart1.length - 4 + 4 = p.framePart1.length := by omega
  obtain ⟨d₁, hcap₁start, hcap₁end⟩ := P.P3_caps_direction (p.framePart1.length - 4)
    (by omega) p.frameWord_incoming_H
    (by rw [hinEnd]; exact p.frameWord_middle_H) p.frameWord_before_middle_P
  have hlastPos := p.frameGaps1_length_pos
  have hIn := hf₁ (p.frameGaps1.length - 1) (by omega)
  rw [p.frame_last_run_offset.1, p.frame_last_run_offset.2] at hIn
  have hindexIn : 2 * (p.side - 2) = 2 * p.side - 4 := by omega
  have hIn' : P.site (p.framePart1.length - 4) = octEdgeZigzag p.side F₁ (2 * (p.side - 2)) := by
    simpa only [hindexIn] using hIn
  have hOut₁ : step (octEdgeZigzag p.side F₁ (2 * (p.side - 2))) d₁ ∉ octahedron p.side := by
    rw [← hIn', ← hcap₁start]
    exact P.P_out _ (by omega) (p.frameWord_before_middle_P 1 (by decide) (by decide))
  have hd₁ := inner_A_edge_dangling_direction p.side (by omega) F₁ (p.side - 2)
    (by omega) (by omega) d₁ hOut₁
  have hIncoming : P.site (p.framePart1.length - 1) = step (P.site p.framePart1.length) F₁.k := by
    rw [hinEnd, hd₁] at hcap₁end
    simpa only [show p.framePart1.length - 4 + 3 = p.framePart1.length - 1 by omega] using hcap₁end
  obtain ⟨d₂, hcap₂start, hcap₂end⟩ := P.P3_caps_direction p.framePart1.length hspan
    p.frameWord_middle_H p.frameWord_outgoing_H p.frameWord_after_middle_P
  have hnextPos := p.frameGaps2_length_pos
  have hOut : P.site (p.framePart1.length + 4) = octEdgeZigzag p.side F₂ (2 * 1) := by
    have h := hf₂ 1 (by omega)
    change P.site (p.framePart1.length + 4) = octEdgeZigzag p.side F₂ 2 at h
    exact h
  have hOut₂ : step (octEdgeZigzag p.side F₂ (2 * 1)) d₂ ∉ octahedron p.side := by
    rw [← hOut, ← hcap₂end]
    exact P.P_out _ (by omega) (p.frameWord_after_middle_P 3 (by decide) (by decide))
  have hd₂ := inner_A_edge_dangling_direction p.side (by omega) F₂ 1
    (by decide) (by omega) d₂ hOut₂
  have hOutgoing : P.site (p.framePart1.length + 1) = step (P.site p.framePart1.length) F₂.k := by
    simpa only [hd₂] using hcap₂start
  intro hsame
  have hcapEq : P.site (p.framePart1.length - 1) = P.site (p.framePart1.length + 1) := by
    rw [hIncoming, hOutgoing, hsame]
  have hbad := P.injective (p.framePart1.length - 1) (by omega)
    (p.framePart1.length + 1) (by omega) hcapEq
  omega

theorem frame_word_forced_incidence (p : ConstructionParameters)
    (P : OctWordPath p.side p.frameWord) :
    ∃ F₁ F₂ : OctEdgeFrame,
      P.site 1 = octEdgeStart p.side F₁ ∧
      P.site p.framePart1.length = octEdgeZigzag p.side F₁ (2 * p.side - 2) ∧
      P.site p.framePart1.length = octEdgeStart p.side F₂ ∧
      (∀ j ≤ p.frameGaps1.length, P.site (1 + frameHOffset p.frameGaps1 j) =
        octEdgeZigzag p.side F₁ (((p.frameGaps1.take j).map frameGapAdvance).sum)) ∧
      (∀ j ≤ p.frameGaps2.length, P.site (p.framePart1.length + frameHOffset p.frameGaps2 j) =
        octEdgeZigzag p.side F₂ (((p.frameGaps2.take j).map frameGapAdvance).sum)) ∧
      F₁.k ≠ F₂.k ∧ F₂.k = F₁.a ∧ F₂.b = F₁.k ∧
      ((F₂.j = F₁.j ∧ F₂.a = F₁.b) ∨ (F₂.j = F₁.b ∧ F₂.a = F₁.j)) := by
  obtain ⟨F₁, F₂, hs, he, hs₂, hf₁, hf₂⟩ := p.frame_word_forced_edges P
  have hbig := p.frame_middle_big_faces_distinct P F₁ F₂ hf₁ hf₂
  have hm : 2 ≤ p.side := by have h := p.side_ge; omega
  have hcases := frame_edges_incidence_cases p.side hm F₁ F₂ (he.symm.trans hs₂) hbig
  exact ⟨F₁, F₂, hs, he, hs₂, hf₁, hf₂, hbig, hcases⟩

end ProteinFolding.Tetrahedral.ConstructionParameters

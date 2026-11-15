import ProteinFolding.Tetrahedral.FrameForcingCapped
import ProteinFolding.Tetrahedral.ReductionWord

/-! Concrete forcing of both literal frame parts, and their occurrence in the
actual reduction word. No frame-rigidity assumption is made. -/

namespace ProteinFolding.Tetrahedral

theorem getElem_append_last_singleton {α : Type*} (xs : List α) (a : α) :
    (xs ++ [a])[(xs ++ [a]).length - 1]'(by simp) = a := by
  simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel,
    Nat.zero_add, List.getElem_cons_zero] using
      (List.getElem_append_right' xs (l₂ := [a]) (i := 0) (by simp)).symm

theorem assembleCappedBodies_occurrence (gaps : ℕ → ℕ) (i : ℕ) (us : List Sequence)
    (u : Sequence) (hu : u ∈ us) :
    ∃ pre post : Sequence, assembleCappedBodies gaps i us = pre ++ capWord u ++ post := by
  induction us generalizing i with
  | nil => simp at hu
  | cons v vs ih =>
    rcases List.mem_cons.mp hu with huv | huvs
    · subst v
      exact ⟨List.replicate (gaps i) .P, assembleCappedBodies gaps (i + 1) vs, rfl⟩
    · obtain ⟨pre, post, heq⟩ := ih (i + 1) huvs
      refine ⟨List.replicate (gaps i) .P ++ capWord v ++ pre, post, ?_⟩
      rw [assembleCappedBodies, heq]
      simp only [List.append_assoc]

theorem assembleReductionWord_occurrence (gaps : ℕ → ℕ) (us : List Sequence)
    (u : Sequence) (hu : u ∈ us) :
    ∃ pre post : Sequence, assembleReductionWord gaps us = pre ++ capWord u ++ post := by
  obtain ⟨pre, post, heq⟩ := assembleCappedBodies_occurrence gaps 0 us u hu
  refine ⟨[.H, .P] ++ pre, post, ?_⟩
  rw [assembleReductionWord, heq]
  simp only [List.append_assoc]

namespace ConstructionParameters

def frameMiddlePrefix (p : ConstructionParameters) : Sequence :=
  [.P, .H] ++ List.replicate 6 .P ++ List.replicate 3 .H ++
    repeatWord (List.replicate 6 .P ++ List.replicate 4 .H) p.bins ++
    List.replicate 6 .P ++ List.replicate p.frameTail1 .H ++ List.replicate 2 .P

theorem frameMiddlePrefix_length (p : ConstructionParameters) :
    p.frameMiddlePrefix.length + 1 = p.framePart1.length := by
  simp only [frameMiddlePrefix, framePart1, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

theorem frame_first_capped_factor (p : ConstructionParameters) :
    p.frameWord = [] ++ capWord (frameGapWord p.frameGaps1) ++ (p.framePart2.tail ++ [.P]) := by
  rw [← p.framePart1_eq_gapWord]
  simp only [frameWord, framePart2, capWord, List.replicate_succ, List.replicate_zero,
    List.tail_cons, List.cons_append, List.nil_append, List.append_assoc]

theorem frame_second_capped_factor (p : ConstructionParameters) :
    p.frameWord = p.frameMiddlePrefix ++ capWord (frameGapWord p.frameGaps2) ++ [] := by
  rw [frameGapWord, ← p.framePart2_eq_gapTail]
  simp only [frameWord, framePart1, frameMiddlePrefix, capWord, List.replicate_succ,
    List.replicate_zero, List.cons_append, List.nil_append, List.append_nil, List.append_assoc]

theorem frameGaps1_length_pos (p : ConstructionParameters) : 0 < p.frameGaps1.length := by
  simp [frameGaps1]

theorem frameGaps2_length_pos (p : ConstructionParameters) : 0 < p.frameGaps2.length := by
  simp [frameGaps2]

theorem frameGaps1_first_pos (p : ConstructionParameters) :
    0 < p.frameGaps1[0]'(p.frameGaps1_length_pos) := by change 0 < 6; decide

theorem frameGaps2_first_pos (p : ConstructionParameters) :
    0 < p.frameGaps2[0]'(p.frameGaps2_length_pos) := by change 0 < 3; decide

theorem frameGaps1_last_pos (p : ConstructionParameters) :
    0 < p.frameGaps1[p.frameGaps1.length - 1]'(by have h := p.frameGaps1_length_pos; omega) := by
  unfold frameGaps1
  rw [getElem_append_last_singleton]
  decide

theorem frameGaps2_last_pos (p : ConstructionParameters) :
    0 < p.frameGaps2[p.frameGaps2.length - 1]'(by have h := p.frameGaps2_length_pos; omega) := by
  unfold frameGaps2
  rw [getElem_append_last_singleton]
  decide

/-- Every frame H has its prescribed zigzag index on one of two edges. The
second edge begins at the endpoint of the first. -/
theorem frame_word_forced_edges (p : ConstructionParameters)
    (P : OctWordPath p.side p.frameWord) :
    ∃ F₁ F₂ : OctEdgeFrame,
      P.site 1 = octEdgeStart p.side F₁ ∧
      P.site p.framePart1.length = octEdgeZigzag p.side F₁ (2 * p.side - 2) ∧
      P.site p.framePart1.length = octEdgeStart p.side F₂ ∧
      (∀ j ≤ p.frameGaps1.length, P.site (1 + frameHOffset p.frameGaps1 j) =
        octEdgeZigzag p.side F₁ (((p.frameGaps1.take j).map frameGapAdvance).sum)) ∧
      (∀ j ≤ p.frameGaps2.length, P.site (p.framePart1.length + frameHOffset p.frameGaps2 j) =
        octEdgeZigzag p.side F₂ (((p.frameGaps2.take j).map frameGapAdvance).sum)) := by
  have hm : 2 ≤ p.side := by have h := p.side_ge; omega
  let P₁ := P.factor [] (capWord (frameGapWord p.frameGaps1)) (p.framePart2.tail ++ [.P]) p.frame_first_capped_factor
  let P₂ := P.factor p.frameMiddlePrefix (capWord (frameGapWord p.frameGaps2)) [] p.frame_second_capped_factor
  obtain ⟨F₁, hs₁, hf₁, he₁⟩ := capped_frame_forced_edge p.side hm p.frameGaps1 P₁
    p.frameGaps1_length_pos p.frameGaps1_first_pos p.frameGaps1_last_pos p.frameGaps1_allowed p.frameGaps1_budget
  obtain ⟨F₂, hs₂, hf₂, he₂⟩ := capped_frame_forced_edge p.side hm p.frameGaps2 P₂
    p.frameGaps2_length_pos p.frameGaps2_first_pos p.frameGaps2_last_pos p.frameGaps2_allowed p.frameGaps2_budget
  refine ⟨F₁, F₂, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [P₁, OctWordPath.factor, List.length_nil, Nat.zero_add] using hs₁
  · have hlen : (frameGapWord p.frameGaps1).length = p.framePart1.length :=
      (congrArg List.length p.framePart1_eq_gapWord).symm
    simpa only [P₁, OctWordPath.factor, List.length_nil, Nat.zero_add, hlen] using he₁
  · change P.site (p.frameMiddlePrefix.length + 1) = _ at hs₂
    rw [p.frameMiddlePrefix_length] at hs₂
    exact hs₂
  · intro j hj
    simpa only [P₁, OctWordPath.factor, List.length_nil, Nat.zero_add] using hf₁ j hj
  · intro j hj
    have h := hf₂ j hj
    change P.site (p.frameMiddlePrefix.length + (1 + frameHOffset p.frameGaps2 j)) = _ at h
    rw [← Nat.add_assoc, p.frameMiddlePrefix_length] at h
    exact h

theorem reductionWord_frame_occurrence (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (gaps : ℕ → ℕ) :
    ∃ pre post : Sequence, p.reductionWord items bulkLengths gaps = pre ++ p.frameWord ++ post := by
  have hmem : p.framePart1 ++ p.framePart2 ∈ p.reductionUnitBodies items bulkLengths := by
    simp only [reductionUnitBodies, List.mem_append, List.mem_cons, List.mem_nil_iff]
    tauto
  obtain ⟨pre, post, heq⟩ := assembleReductionWord_occurrence gaps
    (p.reductionUnitBodies items bulkLengths) (p.framePart1 ++ p.framePart2) hmem
  refine ⟨pre, post, ?_⟩
  rw [p.frameWord_eq_cap]
  exact heq

end ConstructionParameters

end ProteinFolding.Tetrahedral

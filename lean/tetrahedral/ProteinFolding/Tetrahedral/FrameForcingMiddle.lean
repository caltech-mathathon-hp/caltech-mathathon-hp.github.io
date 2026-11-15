import ProteinFolding.Tetrahedral.FrameForcingCaps

/-! Exact letter and offset data around the shared frame vertex. -/

namespace ProteinFolding.Tetrahedral.ConstructionParameters

def frameWindowPrefix (p : ConstructionParameters) : Sequence :=
  [.P, .H] ++ List.replicate 6 .P ++ List.replicate 3 .H ++
    repeatWord (List.replicate 6 .P ++ List.replicate 4 .H) p.bins ++
    List.replicate 6 .P ++ List.replicate p.frameTail1 .H

def frameWindowSuffix (p : ConstructionParameters) : Sequence :=
  List.replicate p.frameTail2 .H ++
    repeatWord (List.replicate 10 .P ++ List.replicate 4 .H) (p.bins + 1) ++
    List.replicate 3 .P ++ [.H, .P]

theorem frameWord_middle_window (p : ConstructionParameters) :
    p.frameWord = p.frameWindowPrefix ++ [.P, .P, .P, .H, .P, .P, .P] ++ p.frameWindowSuffix := by
  simp only [frameWord, framePart1, framePart2, frameWindowPrefix, frameWindowSuffix,
    List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append, List.append_assoc]

theorem frameWindowPrefix_length (p : ConstructionParameters) :
    p.frameWindowPrefix.length + 3 = p.framePart1.length := by
  simp only [frameWindowPrefix, framePart1, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

theorem framePart1_length_ge_five (p : ConstructionParameters) : 5 ≤ p.framePart1.length := by
  simp only [framePart1, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

theorem frame_middle_span_bound (p : ConstructionParameters) :
    p.framePart1.length + 4 < p.frameWord.length := by
  simp only [frameWord, framePart2, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

theorem frameWord_before_middle_P (p : ConstructionParameters) (r : ℕ)
    (hr : 0 < r) (hr4 : r < 4) :
    p.frameWord[p.framePart1.length - 4 + r]? = some .P := by
  have hpre := p.frameWindowPrefix_length
  have hlen := p.framePart1_length_ge_five
  have hrCases : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hrCases with rfl | rfl | rfl
  · have h := word_factor_getElem p.frameWord p.frameWindowPrefix
      [.P, .P, .P, .H, .P, .P, .P] p.frameWindowSuffix p.frameWord_middle_window 0 (by decide)
    simpa only [show p.framePart1.length - 4 + 1 = p.frameWindowPrefix.length + 0 by omega] using h
  · have h := word_factor_getElem p.frameWord p.frameWindowPrefix
      [.P, .P, .P, .H, .P, .P, .P] p.frameWindowSuffix p.frameWord_middle_window 1 (by decide)
    simpa only [show p.framePart1.length - 4 + 2 = p.frameWindowPrefix.length + 1 by omega] using h
  · have h := word_factor_getElem p.frameWord p.frameWindowPrefix
      [.P, .P, .P, .H, .P, .P, .P] p.frameWindowSuffix p.frameWord_middle_window 2 (by decide)
    simpa only [show p.framePart1.length - 4 + 3 = p.frameWindowPrefix.length + 2 by omega] using h

theorem frameWord_after_middle_P (p : ConstructionParameters) (r : ℕ)
    (hr : 0 < r) (hr4 : r < 4) :
    p.frameWord[p.framePart1.length + r]? = some .P := by
  have hpre := p.frameWindowPrefix_length
  have hrCases : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hrCases with rfl | rfl | rfl
  · have h := word_factor_getElem p.frameWord p.frameWindowPrefix
      [.P, .P, .P, .H, .P, .P, .P] p.frameWindowSuffix p.frameWord_middle_window 4 (by decide)
    simpa only [show p.framePart1.length + 1 = p.frameWindowPrefix.length + 4 by omega] using h
  · have h := word_factor_getElem p.frameWord p.frameWindowPrefix
      [.P, .P, .P, .H, .P, .P, .P] p.frameWindowSuffix p.frameWord_middle_window 5 (by decide)
    simpa only [show p.framePart1.length + 2 = p.frameWindowPrefix.length + 5 by omega] using h
  · have h := word_factor_getElem p.frameWord p.frameWindowPrefix
      [.P, .P, .P, .H, .P, .P, .P] p.frameWindowSuffix p.frameWord_middle_window 6 (by decide)
    simpa only [show p.framePart1.length + 3 = p.frameWindowPrefix.length + 6 by omega] using h

theorem frameWord_gap1_H (p : ConstructionParameters) (j : ℕ) (hj : j ≤ p.frameGaps1.length) :
    p.frameWord[1 + frameHOffset p.frameGaps1 j]? = some .H := by
  have hinner := frameGapWord_H_at_offset p.frameGaps1 j hj
  have hbound := (List.getElem?_eq_some_iff.mp hinner).choose
  have hlocal := (capWord_get_inner (frameGapWord p.frameGaps1) _ hbound).trans hinner
  have hlocalBound := (List.getElem?_eq_some_iff.mp hlocal).choose
  have h := word_factor_getElem p.frameWord [] (capWord (frameGapWord p.frameGaps1))
    (p.framePart2.tail ++ [.P]) p.frame_first_capped_factor _ hlocalBound
  have heq : 1 + frameHOffset p.frameGaps1 j = frameHOffset p.frameGaps1 j + 1 := by omega
  simpa only [List.length_nil, Nat.zero_add, ← heq] using h.trans hlocal

theorem frameWord_gap2_H (p : ConstructionParameters) (j : ℕ) (hj : j ≤ p.frameGaps2.length) :
    p.frameWord[p.framePart1.length + frameHOffset p.frameGaps2 j]? = some .H := by
  have hinner := frameGapWord_H_at_offset p.frameGaps2 j hj
  have hbound := (List.getElem?_eq_some_iff.mp hinner).choose
  have hlocal := (capWord_get_inner (frameGapWord p.frameGaps2) _ hbound).trans hinner
  have hlocalBound := (List.getElem?_eq_some_iff.mp hlocal).choose
  have h := word_factor_getElem p.frameWord p.frameMiddlePrefix (capWord (frameGapWord p.frameGaps2))
    [] p.frame_second_capped_factor _ hlocalBound
  have heq : p.frameMiddlePrefix.length + (frameHOffset p.frameGaps2 j + 1) =
      p.framePart1.length + frameHOffset p.frameGaps2 j := by have h := p.frameMiddlePrefix_length; omega
  simpa only [heq] using h.trans hlocal

theorem frameGaps1_last_eq (p : ConstructionParameters) :
    p.frameGaps1[p.frameGaps1.length - 1]'(by have h := p.frameGaps1_length_pos; omega) = 3 := by
  unfold frameGaps1
  exact getElem_append_last_singleton _ 3

theorem frame_last_run_offset (p : ConstructionParameters) :
    1 + frameHOffset p.frameGaps1 (p.frameGaps1.length - 1) = p.framePart1.length - 4 ∧
      (((p.frameGaps1.take (p.frameGaps1.length - 1)).map frameGapAdvance).sum) = 2 * p.side - 4 := by
  have hpos := p.frameGaps1_length_pos
  have hj : p.frameGaps1.length - 1 < p.frameGaps1.length := by omega
  have hnext := frameHOffset_next p.frameGaps1 (p.frameGaps1.length - 1) hj
  have hnextBudget := sum_map_take_succ frameGapAdvance p.frameGaps1 (p.frameGaps1.length - 1) hj
  have hlen : p.framePart1.length = 1 + frameHOffset p.frameGaps1 p.frameGaps1.length := by
    rw [p.framePart1_eq_gapWord]
    exact frameGapWord_length _
  have hind : p.frameGaps1.length - 1 + 1 = p.frameGaps1.length := by omega
  rw [hind, p.frameGaps1_last_eq] at hnext
  rw [hind, List.take_length, p.frameGaps1_last_eq, p.frameGaps1_budget] at hnextBudget
  change 2 * p.side - 2 =
    (((p.frameGaps1.take (p.frameGaps1.length - 1)).map frameGapAdvance).sum) + 2 at hnextBudget
  have hm := p.side_ge
  constructor <;> omega

theorem frameWord_middle_H (p : ConstructionParameters) :
    p.frameWord[p.framePart1.length]? = some .H := by
  have h := p.frameWord_gap1_H p.frameGaps1.length le_rfl
  have hlen : p.framePart1.length = 1 + frameHOffset p.frameGaps1 p.frameGaps1.length := by
    rw [p.framePart1_eq_gapWord]
    exact frameGapWord_length _
  simpa only [← hlen] using h

theorem frameWord_incoming_H (p : ConstructionParameters) :
    p.frameWord[p.framePart1.length - 4]? = some .H := by
  have hpos := p.frameGaps1_length_pos
  have h := p.frameWord_gap1_H (p.frameGaps1.length - 1) (by omega)
  simpa only [p.frame_last_run_offset.1] using h

theorem frameWord_outgoing_H (p : ConstructionParameters) :
    p.frameWord[p.framePart1.length + 4]? = some .H := by
  have hpos := p.frameGaps2_length_pos
  have h := p.frameWord_gap2_H 1 (by omega)
  change p.frameWord[p.framePart1.length + 4]? = some .H at h
  exact h

end ProteinFolding.Tetrahedral.ConstructionParameters

import ProteinFolding.Tetrahedral.FrameForcingMiddle

/-! Strictly increasing forced H indices, including the exact entry-slot links. -/

namespace ProteinFolding.Tetrahedral

def frameAdvanceAt (gaps : List ℕ) (j : ℕ) : ℕ := ((gaps.take j).map frameGapAdvance).sum

theorem frameGapAdvance_pos (k : ℕ) (hk : FrameGapAllowed k) : 0 < frameGapAdvance k := by
  rcases hk with rfl | rfl | rfl | rfl <;> decide

theorem frameAdvanceAt_next (gaps : List ℕ) (j : ℕ) (hj : j < gaps.length) :
    frameAdvanceAt gaps (j + 1) = frameAdvanceAt gaps j + frameGapAdvance gaps[j] :=
  sum_map_take_succ frameGapAdvance gaps j hj

theorem frameAdvanceAt_strict (gaps : List ℕ) (hallow : ∀ k ∈ gaps, FrameGapAllowed k)
    (i j : ℕ) (hij : i < j) (hj : j ≤ gaps.length) : frameAdvanceAt gaps i < frameAdvanceAt gaps j := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hj' : j < gaps.length := by omega
    have hstep := frameAdvanceAt_next gaps j hj'
    have hpos := frameGapAdvance_pos gaps[j] (hallow _ (List.getElem_mem hj'))
    by_cases heq : i = j
    · rw [heq]
      omega
    · have hprev := ih (by omega) (by omega)
      omega

theorem frameAdvanceAt_avoids_gap (gaps : List ℕ) (hallow : ∀ k ∈ gaps, FrameGapAllowed k)
    (j : ℕ) (hj : j < gaps.length) (r : ℕ)
    (hrlo : frameAdvanceAt gaps j < r) (hrhi : r < frameAdvanceAt gaps (j + 1))
    (q : ℕ) (hq : q ≤ gaps.length) : frameAdvanceAt gaps q ≠ r := by
  intro heq
  by_cases hqj : q ≤ j
  · by_cases hsame : q = j
    · rw [hsame] at heq
      omega
    · have hlt := frameAdvanceAt_strict gaps hallow q j (by omega) (by omega)
      omega
  · by_cases hsame : q = j + 1
    · rw [hsame] at heq
      omega
    · have hlt := frameAdvanceAt_strict gaps hallow (j + 1) q (by omega) hq
      omega

theorem six_gap_repeat_head (n : ℕ) (tail : List ℕ) :
    ∃ right : List ℕ, (List.replicate n [6, 0, 0, 0]).flatten ++ 6 :: tail = 6 :: right := by
  cases n with
  | zero => exact ⟨tail, rfl⟩
  | succ n => exact ⟨[0, 0, 0] ++ (List.replicate n [6, 0, 0, 0]).flatten ++ 6 :: tail, rfl⟩

namespace ConstructionParameters

theorem frameGaps1_slot_split (p : ConstructionParameters) (k : ℕ)
    (hklo : 1 ≤ k) (hkhi : k ≤ p.bins + 1) :
    ∃ left right : List ℕ, p.frameGaps1 = left ++ 6 :: right ∧
      left.length + 1 = 4 * k ∧ (left.map frameGapAdvance).sum + 1 = 6 * k := by
  let left : List ℕ := [6, 0, 0] ++ (List.replicate (k - 1) [6, 0, 0, 0]).flatten
  let tail : List ℕ := List.replicate (p.frameTail1 - 1) 0 ++ [3]
  have hdecomp : p.bins = (k - 1) + (p.bins - (k - 1)) := by omega
  have hrep : List.replicate p.bins [6, 0, 0, 0] =
      List.replicate (k - 1) [6, 0, 0, 0] ++ List.replicate (p.bins - (k - 1)) [6, 0, 0, 0] := by
    simpa only [List.replicate_add] using congrArg (fun n => List.replicate n [6, 0, 0, 0]) hdecomp
  have heq : p.frameGaps1 = left ++ ((List.replicate (p.bins - (k - 1)) [6, 0, 0, 0]).flatten ++ 6 :: tail) := by
    rw [frameGaps1, hrep, List.flatten_append]
    simp only [left, tail, List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨right, hright⟩ := six_gap_repeat_head (p.bins - (k - 1)) tail
  rw [hright] at heq
  refine ⟨left, right, heq, ?_, ?_⟩
  · simp only [left, List.length_append, List.length_flatten, List.map_replicate,
      List.length_cons, List.length_nil, List.sum_replicate, nsmul_eq_mul, Nat.cast_id]
    omega
  · simp only [left, List.map_append, List.sum_append, frameGapBudget_repeat]
    norm_num [frameGapAdvance]
    omega

theorem frameGaps1_slot_indices (p : ConstructionParameters) (k : ℕ)
    (hklo : 1 ≤ k) (hkhi : k ≤ p.bins + 1) :
    ∃ j < p.frameGaps1.length, frameAdvanceAt p.frameGaps1 j + 1 = 6 * k ∧
      frameAdvanceAt p.frameGaps1 (j + 1) = 6 * k + 2 := by
  obtain ⟨left, right, heq, _, hbudget⟩ := p.frameGaps1_slot_split k hklo hkhi
  have hj : left.length < p.frameGaps1.length := by rw [heq, List.length_append, List.length_cons]; omega
  have hgap : p.frameGaps1[left.length]'hj = 6 := List.getElem_of_append heq rfl
  have hpref : frameAdvanceAt p.frameGaps1 left.length + 1 = 6 * k := by
    unfold frameAdvanceAt
    rw [heq, List.take_left]
    exact hbudget
  have hnext := frameAdvanceAt_next p.frameGaps1 left.length hj
  rw [hgap] at hnext
  change frameAdvanceAt p.frameGaps1 (left.length + 1) = frameAdvanceAt p.frameGaps1 left.length + 3 at hnext
  exact ⟨left.length, hj, hpref, by omega⟩

end ConstructionParameters

end ProteinFolding.Tetrahedral

import ProteinFolding.Tetrahedral.FrameForcingSlotIndices

/-! Exact forced boundary H indices of every six-site exit slot. -/

namespace ProteinFolding.Tetrahedral

theorem ten_gap_repeat_head (n : ℕ) (hn : 0 < n) (tail : List ℕ) :
    ∃ right : List ℕ, (List.replicate n [10, 0, 0, 0]).flatten ++ tail = 10 :: right := by
  cases n with
  | zero => omega
  | succ n => exact ⟨[0, 0, 0] ++ (List.replicate n [10, 0, 0, 0]).flatten ++ tail, rfl⟩

namespace ConstructionParameters

theorem frameGaps2_slot_split (p : ConstructionParameters) (t : ℕ) (ht : t ≤ p.bins) :
    ∃ left right : List ℕ, p.frameGaps2 = left ++ 10 :: right ∧
      left.length = p.frameTail2 + 4 * t ∧
      (left.map frameGapAdvance).sum = p.frameTail2 + 1 + 10 * t := by
  let left : List ℕ := [3] ++ List.replicate (p.frameTail2 - 1) 0 ++
    (List.replicate t [10, 0, 0, 0]).flatten
  have hdecomp : p.bins + 1 = t + (p.bins + 1 - t) := by omega
  have hrep : List.replicate (p.bins + 1) [10, 0, 0, 0] =
      List.replicate t [10, 0, 0, 0] ++ List.replicate (p.bins + 1 - t) [10, 0, 0, 0] := by
    simpa only [List.replicate_add] using congrArg (fun n => List.replicate n [10, 0, 0, 0]) hdecomp
  have heq : p.frameGaps2 = left ++ ((List.replicate (p.bins + 1 - t) [10, 0, 0, 0]).flatten ++ [3]) := by
    rw [frameGaps2, hrep, List.flatten_append]
    simp only [left, List.append_assoc]
  obtain ⟨right, hright⟩ := ten_gap_repeat_head (p.bins + 1 - t) (by omega) [3]
  rw [hright] at heq
  have htail := p.frameTail2_ge_three
  refine ⟨left, right, heq, ?_, ?_⟩
  · simp only [left, List.length_append, List.length_replicate, List.length_flatten,
      List.map_replicate, List.length_cons, List.length_nil, List.sum_replicate, nsmul_eq_mul, Nat.cast_id]
    omega
  · simp only [left, List.map_append, List.sum_append, frameGapBudget_repeat,
      List.map_replicate, List.sum_replicate, nsmul_eq_mul]
    norm_num [frameGapAdvance]
    omega

theorem frameGaps2_slot_indices (p : ConstructionParameters) (κ : ℕ) (hκ : κ ≤ p.bins) :
    ∃ j < p.frameGaps2.length,
      frameAdvanceAt p.frameGaps2 j + 10 * κ + 12 = 2 * p.side - 2 ∧
      frameAdvanceAt p.frameGaps2 (j + 1) + 10 * κ + 5 = 2 * p.side - 2 := by
  obtain ⟨left, right, heq, _, hbudget⟩ := p.frameGaps2_slot_split (p.bins - κ) (by omega)
  have hj : left.length < p.frameGaps2.length := by rw [heq, List.length_append, List.length_cons]; omega
  have hgap : p.frameGaps2[left.length]'hj = 10 := List.getElem_of_append heq rfl
  have hpref : frameAdvanceAt p.frameGaps2 left.length = p.frameTail2 + 1 + 10 * (p.bins - κ) := by
    unfold frameAdvanceAt
    rw [heq, List.take_left]
    exact hbudget
  have hnext := frameAdvanceAt_next p.frameGaps2 left.length hj
  rw [hgap] at hnext
  change frameAdvanceAt p.frameGaps2 (left.length + 1) = frameAdvanceAt p.frameGaps2 left.length + 7 at hnext
  have htail := p.frameTail2_add
  have hm := p.side_ge
  exact ⟨left.length, hj, by omega, by omega⟩

end ConstructionParameters

end ProteinFolding.Tetrahedral

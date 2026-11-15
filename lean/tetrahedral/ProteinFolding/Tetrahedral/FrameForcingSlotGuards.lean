import ProteinFolding.Tetrahedral.FrameForcingSlots
import ProteinFolding.Tetrahedral.FrameForcingTriangleBlocks

/-! The literal frame has two occupied H guards on each side of every
entry or exit slot, so dimer chains cannot leave those slots through P3 links. -/

namespace ProteinFolding.Tetrahedral

theorem append_repeat_zero_tail (u v : List ℕ) (n : ℕ)
    (hu : ∃ pre, u = pre ++ [0]) (hv : ∃ pre, v = pre ++ [0]) :
    ∃ pre, u ++ (List.replicate n v).flatten = pre ++ [0] := by
  cases n with
  | zero => simpa using hu
  | succ n =>
    obtain ⟨pre, heq⟩ := hv
    refine ⟨u ++ (List.replicate n v).flatten ++ pre, ?_⟩
    rw [List.replicate_succ', List.flatten_append]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, heq, List.append_assoc]

theorem six_gap_repeat_zero_head (n : ℕ) (tail : List ℕ) :
    ∃ right, (List.replicate n [6, 0, 0, 0]).flatten ++ 6 :: 0 :: tail = 6 :: 0 :: right := by
  cases n with
  | zero => exact ⟨tail, rfl⟩
  | succ n => exact ⟨[0, 0] ++ (List.replicate n [6, 0, 0, 0]).flatten ++ 6 :: 0 :: tail, rfl⟩

theorem ten_gap_repeat_zero_head (n : ℕ) (hn : 0 < n) (tail : List ℕ) :
    ∃ right, (List.replicate n [10, 0, 0, 0]).flatten ++ tail = 10 :: 0 :: right := by
  cases n with
  | zero => omega
  | succ n => exact ⟨[0, 0] ++ (List.replicate n [10, 0, 0, 0]).flatten ++ tail, rfl⟩

namespace ConstructionParameters

theorem frameGaps1_slot_guard_context (p : ConstructionParameters) (k : ℕ)
    (hklo : 1 ≤ k) (hkhi : k ≤ p.bins + 1) :
    ∃ pre post, p.frameGaps1 = pre ++ [0, 6, 0] ++ post ∧
      (pre.map frameGapAdvance).sum + 2 = 6 * k := by
  let left : List ℕ := [6, 0, 0] ++ (List.replicate (k - 1) [6, 0, 0, 0]).flatten
  let tail : List ℕ := List.replicate (p.frameTail1 - 1) 0 ++ [3]
  have hdecomp : p.bins = (k - 1) + (p.bins - (k - 1)) := by omega
  have hrep : List.replicate p.bins [6, 0, 0, 0] =
      List.replicate (k - 1) [6, 0, 0, 0] ++ List.replicate (p.bins - (k - 1)) [6, 0, 0, 0] := by
    simpa only [List.replicate_add] using congrArg (fun n => List.replicate n [6, 0, 0, 0]) hdecomp
  have heq : p.frameGaps1 = left ++ ((List.replicate (p.bins - (k - 1)) [6, 0, 0, 0]).flatten ++ 6 :: tail) := by
    rw [frameGaps1, hrep, List.flatten_append]
    simp only [left, tail, List.append_assoc, List.cons_append, List.nil_append]
  have htail := p.frameTail1_ge_three
  obtain ⟨t, ht⟩ : ∃ t, p.frameTail1 - 1 = t + 1 := ⟨p.frameTail1 - 2, by omega⟩
  have htail' : tail = 0 :: (List.replicate t 0 ++ [3]) := by
    simp only [tail, ht, List.replicate_succ, List.cons_append]
  obtain ⟨pre, hleft⟩ := append_repeat_zero_tail [6, 0, 0] [6, 0, 0, 0] (k - 1)
    ⟨[6, 0], rfl⟩ ⟨[6, 0, 0], rfl⟩
  change left = pre ++ [0] at hleft
  rw [htail'] at heq
  obtain ⟨post, hright⟩ := six_gap_repeat_zero_head (p.bins - (k - 1)) (List.replicate t 0 ++ [3])
  rw [hleft, hright] at heq
  have hbudget : (left.map frameGapAdvance).sum + 1 = 6 * k := by
    simp only [left, List.map_append, List.sum_append, frameGapBudget_repeat]
    norm_num [frameGapAdvance]
    omega
  rw [hleft] at hbudget
  simp only [List.map_append, List.sum_append] at hbudget
  change (pre.map frameGapAdvance).sum + 1 + 1 = 6 * k at hbudget
  exact ⟨pre, post, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using heq, by omega⟩

theorem frameGaps2_slot_guard_context (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    ∃ pre post, p.frameGaps2 = pre ++ [0, 10, 0] ++ post ∧
      (pre.map frameGapAdvance).sum + 2 = 2 * p.side - (10 * k + 13) := by
  let t := p.bins - k
  let base : List ℕ := [3] ++ List.replicate (p.frameTail2 - 1) 0
  let left : List ℕ := base ++ (List.replicate t [10, 0, 0, 0]).flatten
  have ht : t ≤ p.bins := by dsimp [t]; omega
  have hdecomp : p.bins + 1 = t + (p.bins + 1 - t) := by omega
  have hrep : List.replicate (p.bins + 1) [10, 0, 0, 0] =
      List.replicate t [10, 0, 0, 0] ++ List.replicate (p.bins + 1 - t) [10, 0, 0, 0] := by
    simpa only [List.replicate_add] using congrArg (fun n => List.replicate n [10, 0, 0, 0]) hdecomp
  have heq : p.frameGaps2 = left ++ ((List.replicate (p.bins + 1 - t) [10, 0, 0, 0]).flatten ++ [3]) := by
    rw [frameGaps2, hrep, List.flatten_append]
    simp only [left, base, List.append_assoc]
  have htail := p.frameTail2_ge_three
  obtain ⟨r, hr⟩ : ∃ r, p.frameTail2 - 1 = r + 1 := ⟨p.frameTail2 - 2, by omega⟩
  have hbase : base = ([3] ++ List.replicate r 0) ++ [0] := by
    simp only [base, hr, List.replicate_succ', List.append_assoc]
  obtain ⟨pre, hleft⟩ := append_repeat_zero_tail base [10, 0, 0, 0] t
    ⟨_, hbase⟩ ⟨[10, 0, 0], rfl⟩
  change left = pre ++ [0] at hleft
  obtain ⟨post, hright⟩ := ten_gap_repeat_zero_head (p.bins + 1 - t) (by omega) [3]
  rw [hleft, hright] at heq
  have hbudget : (left.map frameGapAdvance).sum = p.frameTail2 + 1 + 10 * t := by
    simp only [left, base, List.map_append, List.sum_append, frameGapBudget_repeat,
      List.map_replicate, List.sum_replicate, nsmul_eq_mul]
    norm_num [frameGapAdvance]
    omega
  rw [hleft] at hbudget
  simp only [List.map_append, List.sum_append] at hbudget
  change (pre.map frameGapAdvance).sum + 1 = p.frameTail2 + 1 + 10 * t at hbudget
  have htailadd := p.frameTail2_add
  have hside := p.side_ge
  refine ⟨pre, post, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using heq, ?_⟩
  dsimp [t] at hbudget
  omega

theorem forced_family_entry_slot_P3_closed (p : ConstructionParameters) (H : Finset Site)
    (F : ForcedFrameFamily p.side H p.frameGaps1 p.frameGaps2)
    (k : ℕ) (hklo : 1 ≤ k) (hkhi : k ≤ p.bins + 1) :
    ∀ x ∈ edgeBlock p.side F.first (6 * k) 2,
      ∀ y ∈ bulkDeletedEdges p.side \ (H ∪ octVertices p.side),
      OctTriangularNeighbours p.side x y → y ∈ edgeBlock p.side F.first (6 * k) 2 := by
  obtain ⟨pre, post, heq, hprefix⟩ := p.frameGaps1_slot_guard_context k hklo hkhi
  have hm := p.side_ge
  have hfamily := p.family_side_bound
  exact F.guarded_gap_triangular_isolated (by omega) pre post 6 (6 * k) 2 heq hprefix rfl (by omega) (by omega)

theorem forced_family_exit_slot_P3_closed (p : ConstructionParameters) (H : Finset Site)
    (F : ForcedFrameFamily p.side H p.frameGaps1 p.frameGaps2) (k : ℕ) (hk : k ≤ p.bins) :
    ∀ x ∈ edgeBlock p.side F.second (2 * p.side - (10 * k + 13)) 6,
      ∀ y ∈ bulkDeletedEdges p.side \ (H ∪ octVertices p.side),
      OctTriangularNeighbours p.side x y → y ∈ edgeBlock p.side F.second (2 * p.side - (10 * k + 13)) 6 := by
  obtain ⟨pre, post, heq, hprefix⟩ := p.frameGaps2_slot_guard_context k hk
  have hm := p.side_ge
  have hfamily := p.family_side_bound
  exact F.swap.guarded_gap_triangular_isolated (by omega) pre post 10
    (2 * p.side - (10 * k + 13)) 6 heq hprefix rfl (by omega) (by omega)

end ConstructionParameters

end ProteinFolding.Tetrahedral

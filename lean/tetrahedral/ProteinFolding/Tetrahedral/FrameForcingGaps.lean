import ProteinFolding.Tetrahedral.FrameWord
import ProteinFolding.Tetrahedral.FrameForcingChain

/-! The actual frame as its consecutive-H gap list, without geometric assumptions. -/

namespace ProteinFolding.Tetrahedral

def frameGapTail (gaps : List ℕ) : Sequence :=
  gaps.flatMap (fun k => List.replicate k .P ++ [.H])

def frameGapWord (gaps : List ℕ) : Sequence := .H :: frameGapTail gaps

theorem frameGapTail_append (xs ys : List ℕ) :
    frameGapTail (xs ++ ys) = frameGapTail xs ++ frameGapTail ys := by
  simp only [frameGapTail, List.flatMap_append]

theorem frameGapTail_replicate_zero (n : ℕ) :
    frameGapTail (List.replicate n 0) = List.replicate n .H := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change .H :: frameGapTail (List.replicate n 0) = .H :: List.replicate n .H
    rw [ih]

theorem frameGapTail_repeat (gaps : List ℕ) (n : ℕ) :
    frameGapTail (List.replicate n gaps).flatten = repeatWord (frameGapTail gaps) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change frameGapTail (gaps ++ (List.replicate n gaps).flatten) =
      frameGapTail gaps ++ repeatWord (frameGapTail gaps) n
    rw [frameGapTail_append, ih]

theorem frameGapBudget_repeat (gaps : List ℕ) (n : ℕ) :
    (((List.replicate n gaps).flatten).map frameGapAdvance).sum =
      n * (gaps.map frameGapAdvance).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.map_append, List.sum_append, ih,
      Nat.succ_mul, Nat.add_comm]

theorem replicate_H_pred (n : ℕ) (hn : 0 < n) :
    .H :: List.replicate (n - 1) Residue.H = List.replicate n .H := by
  cases n with
  | zero => omega
  | succ n => rfl

theorem replicate_H_pred_append (n : ℕ) (hn : 0 < n) (S : Sequence) :
    .H :: (List.replicate (n - 1) .H ++ S) = List.replicate n .H ++ S := by
  rw [← List.cons_append, replicate_H_pred n hn]

namespace ConstructionParameters

def frameGaps1 (p : ConstructionParameters) : List ℕ :=
  [6, 0, 0] ++ (List.replicate p.bins [6, 0, 0, 0]).flatten ++ [6] ++
    List.replicate (p.frameTail1 - 1) 0 ++ [3]

def frameGaps2 (p : ConstructionParameters) : List ℕ :=
  [3] ++ List.replicate (p.frameTail2 - 1) 0 ++
    (List.replicate (p.bins + 1) [10, 0, 0, 0]).flatten ++ [3]

theorem framePart1_eq_gapWord (p : ConstructionParameters) :
    p.framePart1 = frameGapWord p.frameGaps1 := by
  have ht : 0 < p.frameTail1 := by have h := p.frameTail1_ge_three; omega
  simp only [frameGapWord, frameGaps1, frameGapTail_append,
    frameGapTail_replicate_zero, frameGapTail_repeat]
  simp only [frameGapTail, List.flatMap_cons, List.flatMap_nil, List.replicate_zero,
    List.nil_append, List.cons_append, List.append_assoc]
  rw [replicate_H_pred_append p.frameTail1 ht]
  simp only [framePart1, List.replicate_succ, List.replicate_zero,
    List.cons_append, List.nil_append, List.append_assoc]

theorem framePart2_eq_gapTail (p : ConstructionParameters) :
    p.framePart2 = frameGapTail p.frameGaps2 := by
  have ht : 0 < p.frameTail2 := by have h := p.frameTail2_ge_three; omega
  simp only [frameGaps2, frameGapTail_append, frameGapTail_replicate_zero, frameGapTail_repeat]
  simp only [frameGapTail, List.flatMap_cons, List.flatMap_nil, List.replicate_zero,
    List.nil_append, List.cons_append, List.append_assoc]
  rw [replicate_H_pred_append p.frameTail2 ht]
  simp only [framePart2, List.replicate_succ, List.replicate_zero,
    List.cons_append, List.nil_append, List.append_assoc]

theorem frame_body_eq_gapWord (p : ConstructionParameters) :
    p.framePart1 ++ p.framePart2 = frameGapWord (p.frameGaps1 ++ p.frameGaps2) := by
  rw [framePart1_eq_gapWord, framePart2_eq_gapTail]
  simp only [frameGapWord, frameGapTail_append, List.cons_append]

theorem frameGaps1_budget (p : ConstructionParameters) :
    (p.frameGaps1.map frameGapAdvance).sum = 2 * p.side - 2 := by
  have ht := p.frameTail1_add
  have hpos := p.frameTail1_ge_three
  simp only [frameGaps1, List.map_append, List.sum_append, frameGapBudget_repeat,
    List.map_replicate, List.sum_replicate, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [frameGapAdvance]
  omega

theorem frameGaps2_budget (p : ConstructionParameters) :
    (p.frameGaps2.map frameGapAdvance).sum = 2 * p.side - 2 := by
  have ht := p.frameTail2_add
  have hpos := p.frameTail2_ge_three
  simp only [frameGaps2, List.map_append, List.sum_append, frameGapBudget_repeat,
    List.map_replicate, List.sum_replicate, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [frameGapAdvance]
  omega

theorem frameGapAllowed_of_mem_repeat (gaps : List ℕ) (n k : ℕ)
    (hallow : ∀ j ∈ gaps, FrameGapAllowed j) (hk : k ∈ (List.replicate n gaps).flatten) :
    FrameGapAllowed k := by
  obtain ⟨block, hblock, hkblock⟩ := List.mem_flatten.mp hk
  have hb : block = gaps := (List.mem_replicate.mp hblock).2
  subst block
  exact hallow k hkblock

theorem frameGaps1_allowed (p : ConstructionParameters) :
    ∀ k ∈ p.frameGaps1, FrameGapAllowed k := by
  intro k hk
  simp only [frameGaps1, List.mem_append] at hk
  rcases hk with (((hk | hk) | hk) | hk) | hk
  · simp only [List.mem_cons, List.mem_nil_iff] at hk
    rcases hk with rfl | rfl | rfl | h <;> simp_all [FrameGapAllowed]
  · apply frameGapAllowed_of_mem_repeat [6, 0, 0, 0] p.bins k ?_ hk
    intro j hj
    simp only [List.mem_cons, List.mem_nil_iff] at hj
    rcases hj with rfl | rfl | rfl | rfl | h <;> simp_all [FrameGapAllowed]
  · have heq : k = 6 := by simpa using hk
    simp [heq, FrameGapAllowed]
  · have heq : k = 0 := (List.mem_replicate.mp hk).2
    simp [heq, FrameGapAllowed]
  · have heq : k = 3 := by simpa using hk
    simp [heq, FrameGapAllowed]

theorem frameGaps2_allowed (p : ConstructionParameters) :
    ∀ k ∈ p.frameGaps2, FrameGapAllowed k := by
  intro k hk
  simp only [frameGaps2, List.mem_append] at hk
  rcases hk with ((hk | hk) | hk) | hk
  · have heq : k = 3 := by simpa using hk
    simp [heq, FrameGapAllowed]
  · have heq : k = 0 := (List.mem_replicate.mp hk).2
    simp [heq, FrameGapAllowed]
  · apply frameGapAllowed_of_mem_repeat [10, 0, 0, 0] (p.bins + 1) k ?_ hk
    intro j hj
    simp only [List.mem_cons, List.mem_nil_iff] at hj
    rcases hj with rfl | rfl | rfl | rfl | h <;> simp_all [FrameGapAllowed]
  · have heq : k = 3 := by simpa using hk
    simp [heq, FrameGapAllowed]

end ConstructionParameters

end ProteinFolding.Tetrahedral

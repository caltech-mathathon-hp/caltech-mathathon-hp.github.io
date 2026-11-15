import ProteinFolding.Tetrahedral.WordPieces

/-! The literal frame word of Section 6 and Appendix C.
The two final long runs are the indices after the last slots. -/

namespace ProteinFolding.Tetrahedral

namespace ConstructionParameters

def frameTail1 (p : ConstructionParameters) : ℕ := 2 * p.side - (6 * p.bins + 11)
def frameTail2 (p : ConstructionParameters) : ℕ := 2 * p.side - (10 * p.bins + 15)

theorem frameTail1_add (p : ConstructionParameters) :
    p.frameTail1 + 6 * p.bins + 11 = 2 * p.side := by
  have h := p.family_side_bound
  unfold frameTail1
  omega

theorem frameTail2_add (p : ConstructionParameters) :
    p.frameTail2 + 10 * p.bins + 15 = 2 * p.side := by
  have h := p.family_side_bound
  unfold frameTail2
  omega

theorem frameTail1_ge_three (p : ConstructionParameters) : 3 ≤ p.frameTail1 := by
  have h := p.family_side_bound
  have ht := p.frameTail1_add
  omega

theorem frameTail2_ge_three (p : ConstructionParameters) : 3 ≤ p.frameTail2 := by
  have h := p.family_side_bound
  have ht := p.frameTail2_add
  omega

/-- From V_a to V_b: the initial skip {1,2}, K+1 two-slots,
then the corner at index 2m-3. -/
def framePart1 (p : ConstructionParameters) : Sequence :=
  [.H] ++ List.replicate 6 .P ++ List.replicate 3 .H ++
    repeatWord (List.replicate 6 .P ++ List.replicate 4 .H) p.bins ++
    List.replicate 6 .P ++ List.replicate p.frameTail1 .H ++
    List.replicate 3 .P ++ [.H]

/-- From V_b to V_c, traversing the second edge opposite to its slot indices:
one corner, the final long run, K+1 six-slots, then the last corner. -/
def framePart2 (p : ConstructionParameters) : Sequence :=
  List.replicate 3 .P ++ List.replicate p.frameTail2 .H ++
    repeatWord (List.replicate 10 .P ++ List.replicate 4 .H) (p.bins + 1) ++
    List.replicate 3 .P ++ [.H]

/-- Both end caps are included, as in the actual builder's frame unit. -/
def frameWord (p : ConstructionParameters) : Sequence :=
  [.P] ++ p.framePart1 ++ p.framePart2 ++ [.P]

/-- Every H-run, including the three singleton vertex runs, in chain order. -/
def frameHRunLengths (p : ConstructionParameters) : List ℕ :=
  [1, 3] ++ List.replicate p.bins 4 ++ [p.frameTail1, 1, p.frameTail2] ++
    List.replicate (p.bins + 1) 4 ++ [1]

theorem frameHRunLengths_positive (p : ConstructionParameters) :
    ∀ n ∈ p.frameHRunLengths, 0 < n := by
  intro n hn
  have ht1 := p.frameTail1_ge_three
  have ht2 := p.frameTail2_ge_three
  simp only [frameHRunLengths, List.mem_append] at hn
  rcases hn with (((hn | hn) | hn) | hn) | hn
  all_goals simp only [List.mem_cons, List.mem_replicate, List.mem_nil_iff] at hn
  · rcases hn with h | h | h <;> first | omega | contradiction
  · omega
  · rcases hn with h | h | h | h <;> first | omega | contradiction
  · omega
  · rcases hn with h | h <;> first | omega | contradiction

theorem frame_nonvertex_runs_ge_three (p : ConstructionParameters) :
    ∀ n ∈ p.frameHRunLengths, n ≠ 1 → 3 ≤ n := by
  intro n hn hne
  have ht1 := p.frameTail1_ge_three
  have ht2 := p.frameTail2_ge_three
  simp only [frameHRunLengths, List.mem_append] at hn
  rcases hn with (((hn | hn) | hn) | hn) | hn
  all_goals simp only [List.mem_cons, List.mem_replicate, List.mem_nil_iff] at hn
  · rcases hn with h | h | h <;> first | omega | contradiction
  · omega
  · rcases hn with h | h | h | h <;> first | omega | contradiction
  · omega
  · rcases hn with h | h <;> first | omega | contradiction

theorem frameHRunLengths_singleton_count (p : ConstructionParameters) :
    p.frameHRunLengths.count 1 = 3 := by
  have ht1 := p.frameTail1_ge_three
  have ht2 := p.frameTail2_ge_three
  have hn1 : p.frameTail1 ≠ 1 := by omega
  have hn2 : p.frameTail2 ≠ 1 := by omega
  simp [frameHRunLengths, List.count_append, List.count_replicate, hn1, hn2]

theorem frameWord_count (p : ConstructionParameters) :
    hydrophobicCount p.frameWord + 8 * p.bins + 16 = 4 * p.side := by
  have ht1 := p.frameTail1_add
  have ht2 := p.frameTail2_add
  have hcount : hydrophobicCount p.frameWord = p.frameTail1 + p.frameTail2 + 8 * p.bins + 10 := by
    simp only [frameWord, framePart1, framePart2, hydrophobicCount_append,
      hydrophobicCount_replicate, hydrophobicCount_repeatWord]
    simp [hydrophobicCount_eq_count]
    omega
  omega

theorem frameWord_length (p : ConstructionParameters) :
    p.frameWord.length = 4 * p.side + 8 * p.bins + 17 := by
  have ht1 := p.frameTail1_add
  have ht2 := p.frameTail2_add
  simp only [frameWord, framePart1, framePart2, List.length_append,
    List.length_replicate, List.length_singleton, repeatWord_length]
  omega

/-- The advance budget of each frame part is the full edge length 2m-2. -/
theorem framePart1_maximal_advance (p : ConstructionParameters) :
    3 * (p.bins + 2) + 2 + 3 * p.bins + (p.frameTail1 - 1) + 2 = 2 * p.side - 2 := by
  have ht := p.frameTail1_add
  have hpos := p.frameTail1_ge_three
  omega

theorem framePart2_maximal_advance (p : ConstructionParameters) :
    2 + (p.frameTail2 - 1) + 10 * (p.bins + 1) + 2 = 2 * p.side - 2 := by
  have ht := p.frameTail2_add
  have hpos := p.frameTail2_ge_three
  omega

end ConstructionParameters

end ProteinFolding.Tetrahedral

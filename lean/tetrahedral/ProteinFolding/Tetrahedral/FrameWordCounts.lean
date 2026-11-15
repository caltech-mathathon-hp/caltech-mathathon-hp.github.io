import ProteinFolding.Tetrahedral.FrameWordPHP

/-! PHP counts of the literal frame and separator units. -/

namespace ProteinFolding.Tetrahedral

theorem phpStartCount_long_run_prefix_assoc (k n : ℕ) (hk : 0 < k) (hn : 2 ≤ n)
    (S : Sequence) :
    phpStartCount (List.replicate k .P ++ (List.replicate n .H ++ S)) = phpStartCount S := by
  simpa only [List.append_assoc] using phpStartCount_long_run_prefix k n hk hn S

theorem phpStartCount_isolated_H_cons (j : ℕ) (hj : 0 < j) (S : Sequence) :
    phpStartCount (.P :: .H :: (List.replicate j .P ++ S)) =
      1 + phpStartCount (List.replicate j .P ++ S) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simpa only [List.replicate_succ, List.cons_append] using
    phpStartCount_PHP_cons (List.replicate j .P ++ S)

theorem phpStartCount_between_P_runs (k j : ℕ) (hk : 0 < k) (hj : 0 < j)
    (S : Sequence) :
    phpStartCount (List.replicate k .P ++ .H :: (List.replicate j .P ++ S)) =
      1 + phpStartCount (List.replicate j .P ++ S) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [phpStartCount_replicate_P]
  exact phpStartCount_isolated_H_cons j hj S

theorem phpStartCount_dimer_after_P_run (k q : ℕ) (hk : 0 < k) (S : Sequence) :
    phpStartCount (List.replicate k .P ++ (dimerChain (q + 1) ++ S)) = phpStartCount S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [phpStartCount_replicate_P]
  exact phpStartCount_dimer_prefix q S

namespace ConstructionParameters

theorem frameWord_eq_cap (p : ConstructionParameters) :
    p.frameWord = capWord (p.framePart1 ++ p.framePart2) := by
  simp only [frameWord, capWord, List.cons_append, List.nil_append, List.append_assoc]

theorem frameWord_phpStartCount (p : ConstructionParameters) : phpStartCount p.frameWord = 3 := by
  simp only [frameWord, framePart1, framePart2,
    List.cons_append, List.nil_append, List.append_assoc]
  rw [phpStartCount_isolated_H_cons 6 (by decide)]
  rw [phpStartCount_long_run_prefix_assoc 6 3 (by decide) (by decide)]
  rw [phpStartCount_repeat_long_run_prefix 6 4 p.bins (by decide) (by decide)]
  rw [phpStartCount_long_run_prefix_assoc 6 p.frameTail1 (by decide) (by have h := p.frameTail1_ge_three; omega)]
  rw [phpStartCount_between_P_runs 3 3 (by decide) (by decide)]
  rw [phpStartCount_long_run_prefix_assoc 3 p.frameTail2 (by decide) (by have h := p.frameTail2_ge_three; omega)]
  rw [phpStartCount_repeat_long_run_prefix 10 4 (p.bins + 1) (by decide) (by decide)]
  simp [List.replicate_succ, phpStartCount_cons]

theorem frameWord_phpIndices_card (p : ConstructionParameters) : (phpIndices p.frameWord).card = 3 := by
  rw [phpIndices_card_eq_startCount, frameWord_phpStartCount]

theorem entryTether_pos (p : ConstructionParameters) (k : ℕ) : 0 < p.entryTether k := by
  unfold entryTether
  omega

theorem exitTether_pos (p : ConstructionParameters) (k : ℕ) : 0 < p.exitTether k := by
  unfold exitTether
  omega

theorem separatorWord_phpStartCount (p : ConstructionParameters) (k : ℕ) :
    phpStartCount (capWord (p.separatorWord k)) = 0 := by
  simp only [capWord, separatorWord, List.append_assoc]
  rw [phpStartCount_dimer_prefix 0]
  rw [phpStartCount_dimer_after_P_run (p.entryTether k) 1 (p.entryTether_pos k)]
  rw [phpStartCount_dimer_after_P_run (p.exitTether k) 2 (p.exitTether_pos k)]
  exact phpStartCount_singleton .P

end ConstructionParameters

end ProteinFolding.Tetrahedral

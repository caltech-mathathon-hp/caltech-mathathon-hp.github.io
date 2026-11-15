import ProteinFolding.Tetrahedral.FrameForcingDimerWords

/-! The actual Section 6 word has exactly the stated D disjoint HH runs. -/

namespace ProteinFolding.Tetrahedral

theorem dimerStartCount_isolated_H_cons (j : ℕ) (hj : 0 < j) (S : Sequence) :
    dimerStartCount (.P :: .H :: (List.replicate j .P ++ S)) =
      dimerStartCount (List.replicate j .P ++ S) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simp only [List.replicate_succ, List.cons_append, dimerStartCount_PHP_cons]

theorem dimerStartCount_dimer_cons_Ptail (q j : ℕ) (hj : 0 < j) (S : Sequence) :
    dimerStartCount (.P :: (dimerChain (q + 1) ++ (List.replicate j .P ++ S))) =
      (q + 1) + dimerStartCount (List.replicate j .P ++ S) := by
  simpa only [List.replicate_one, List.singleton_append] using
    dimerStartCount_dimer_Ptail 1 q j (by decide) hj S

namespace ConstructionParameters

def reductionDimerCount (p : ConstructionParameters) : ℕ :=
  (p.side - 1) + 4 * (p.bins + 1) + 9 * (p.side - 2)

theorem frameWord_dimerStartCount (p : ConstructionParameters) : dimerStartCount p.frameWord = 0 := by
  simp only [frameWord, framePart1, framePart2, List.cons_append, List.nil_append, List.append_assoc]
  rw [dimerStartCount_isolated_H_cons 6 (by decide)]
  rw [dimerStartCount_long_run_prefix 6 3 (by decide) (by decide)]
  rw [dimerStartCount_repeat_long_run_prefix 6 4 p.bins (by decide) (by decide)]
  rw [dimerStartCount_long_run_prefix 6 p.frameTail1 (by decide) p.frameTail1_ge_three]
  rw [dimerStartCount_between_P_runs 3 3 (by decide) (by decide)]
  rw [dimerStartCount_long_run_prefix 3 p.frameTail2 (by decide) p.frameTail2_ge_three]
  rw [dimerStartCount_repeat_long_run_prefix 10 4 (p.bins + 1) (by decide) (by decide)]
  simp [List.replicate_succ, dimerStartCount_cons]

theorem separatorWord_dimerStartCount (p : ConstructionParameters) (k : ℕ) :
    dimerStartCount (capWord (p.separatorWord k)) = 6 := by
  simp only [capWord, separatorWord, List.append_assoc]
  rw [dimerStartCount_dimer_cons_Ptail 0 (p.entryTether k) (p.entryTether_pos k)]
  rw [dimerStartCount_dimer_Ptail (p.entryTether k) 1 (p.exitTether k)
    (p.entryTether_pos k) (p.exitTether_pos k)]
  have hlast := dimerStartCount_dimer_Ptail (p.exitTether k) 2 1 (p.exitTether_pos k) (by decide) []
  simp only [List.replicate_one, List.append_nil, dimerStartCount_singleton] at hlast
  rw [hlast]

theorem itemUnits_dimerStartCount_sum (p : ConstructionParameters) (items : List ℕ) :
    ((items.map (fun s => dimerChain (p.itemDimers s))).map (fun u => dimerStartCount (capWord u))).sum =
      p.scale * items.sum := by
  induction items with
  | nil => simp
  | cons s items ih =>
    simp only [List.map_cons, List.sum_cons, dimerStartCount_capped_dimer, ih]
    unfold itemDimers
    ring

theorem reductionWord_dimerStartCount (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (gaps : ℕ → ℕ) (htotal : items.sum = p.bins * p.capacity)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) :
    dimerStartCount (p.reductionWord items bulkLengths gaps) = p.reductionDimerCount := by
  have hframe : dimerStartCount (capWord (p.framePart1 ++ p.framePart2)) = 0 := by
    rw [← p.frameWord_eq_cap, p.frameWord_dimerStartCount]
  have hbulkzero : (bulkLengths.map (fun n => dimerStartCount (capWord (List.replicate n .H)))).sum = 0 :=
    word_sum_map_zero _ _ (fun n hn => dimerStartCount_capped_long_H n (hbulk n hn))
  have hsep :
      (((List.range (p.bins + 1)).map p.separatorWord).map (fun u => dimerStartCount (capWord u))).sum =
        6 * (p.bins + 1) := by
    simp [List.map_map, Function.comp_def, separatorWord_dimerStartCount, Nat.mul_comm]
  have hcount : dimerStartCount (p.reductionWord items bulkLengths gaps) =
      6 * (p.bins + 1) + p.leftFiller + p.scale * items.sum + p.rightFiller + 9 * (p.side - 2) := by
    rw [reductionWord, dimerStartCount_assembleReductionWord]
    simp only [reductionUnitBodies, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, dimerStartCount_capped_single_H, hframe]
    rw [hsep, itemUnits_dimerStartCount_sum]
    simp only [dimerStartCount_capped_dimer, List.map_map, Function.comp_def]
    simp [dimerStartCount_capped_dimer, hbulkzero]
    ring
  have hitems : p.scale * items.sum = p.bins * p.binDimers := by
    rw [htotal]
    unfold binDimers
    ring
  rw [hitems] at hcount
  have htrack := p.track_total_dimer_count
  have hlarge := p.side_ge
  unfold reductionDimerCount
  omega

theorem reductionWord_dimerStartIndices_card (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (gaps : ℕ → ℕ) (htotal : items.sum = p.bins * p.capacity)
    (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) :
    (dimerStartIndices (p.reductionWord items bulkLengths gaps)).card = p.reductionDimerCount := by
  rw [dimerStartIndices_card, p.reductionWord_dimerStartCount items bulkLengths gaps htotal hbulk]

end ConstructionParameters

end ProteinFolding.Tetrahedral

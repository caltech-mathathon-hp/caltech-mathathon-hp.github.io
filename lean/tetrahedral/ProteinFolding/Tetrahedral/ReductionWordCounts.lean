import ProteinFolding.Tetrahedral.ReductionWord

/-! Exact letter counts of the literal Section 6 assembly.
The bulk-cover mass equation is displayed as an explicit hypothesis. -/

namespace ProteinFolding.Tetrahedral

theorem word_sum_map_zero {α : Type*} (f : α → ℕ) (xs : List α)
    (hzero : ∀ x ∈ xs, f x = 0) : (xs.map f).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hzero x (by simp), ih (fun y hy => hzero y (by simp [hy]))]

namespace ConstructionParameters

theorem reductionWord_phpStartCount (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (gaps : ℕ → ℕ) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) :
    phpStartCount (p.reductionWord items bulkLengths gaps) = 6 := by
  have hframe : phpStartCount (capWord (p.framePart1 ++ p.framePart2)) = 3 := by
    rw [← p.frameWord_eq_cap, p.frameWord_phpStartCount]
  have hbulkzero : (bulkLengths.map (fun n => phpStartCount (capWord (List.replicate n .H)))).sum = 0 :=
    word_sum_map_zero _ _ (fun n hn => phpStartCount_capped_long_H n (by have h := hbulk n hn; omega))
  rw [reductionWord, phpStartCount_assembleReductionWord]
  simp only [reductionUnitBodies, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, hframe, phpStartCount_capped_single_H]
  have hsep :
      (((List.range (p.bins + 1)).map p.separatorWord).map (fun u => phpStartCount (capWord u))).sum = 0 := by
    simp [List.map_map, Function.comp_def, separatorWord_phpStartCount]
  rw [hsep]
  simp only [phpStartCount_capped_dimer, List.map_map, Function.comp_def]
  simp [phpStartCount_capped_dimer, hbulkzero]

theorem reductionWord_phpIndices_card (p : ConstructionParameters) (items bulkLengths : List ℕ)
    (gaps : ℕ → ℕ) (hbulk : ∀ n ∈ bulkLengths, 3 ≤ n) :
    (phpIndices (p.reductionWord items bulkLengths gaps)).card = 6 := by
  rw [phpIndices_card_eq_startCount, reductionWord_phpStartCount p items bulkLengths gaps hbulk]

theorem itemUnits_hydrophobicCount_sum (p : ConstructionParameters) (items : List ℕ) :
    ((items.map (fun s => dimerChain (p.itemDimers s))).map hydrophobicCount).sum =
      2 * p.scale * items.sum := by
  induction items with
  | nil => simp
  | cons s items ih =>
    simp only [List.map_cons, List.sum_cons, dimerChain_count, ih]
    unfold itemDimers
    ring

theorem bulkUnits_hydrophobicCount_sum (bulkLengths : List ℕ) :
    ((bulkLengths.map (fun n => List.replicate n .H)).map hydrophobicCount).sum = bulkLengths.sum := by
  simp [List.map_map, Function.comp_def, hydrophobicCount_replicate]

theorem reductionUnitBodies_hydrophobicCount_sum (p : ConstructionParameters)
    (items bulkLengths : List ℕ) :
    ((p.reductionUnitBodies items bulkLengths).map hydrophobicCount).sum =
      3 + hydrophobicCount p.frameWord + 12 * (p.bins + 1) + 2 * p.leftFiller +
        2 * p.scale * items.sum + 2 * p.rightFiller + 18 * (p.side - 2) + bulkLengths.sum := by
  have hframe : hydrophobicCount (p.framePart1 ++ p.framePart2) = hydrophobicCount p.frameWord := by
    rw [p.frameWord_eq_cap, hydrophobicCount_capWord]
  have hsep : (((List.range (p.bins + 1)).map p.separatorWord).map hydrophobicCount).sum =
      12 * (p.bins + 1) := by
    simp [List.map_map, Function.comp_def, separatorWord_count, Nat.mul_comm]
  have hsingle : hydrophobicCount [.H] = 1 := by decide
  simp only [reductionUnitBodies, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  rw [hframe, hsingle, hsep, itemUnits_hydrophobicCount_sum, bulkUnits_hydrophobicCount_sum]
  simp only [List.map_replicate, List.sum_replicate, dimerChain_count]
  ring

theorem track_total_dimer_count (p : ConstructionParameters) :
    p.leftFiller + p.rightFiller + p.bins * p.binDimers + 2 * p.bins + 3 = p.side := by
  simp only [side, separatorIndex, rightFiller]
  ring

/-- Before the bulk cover is supplied, the remaining H mass is exactly the
number of octahedral edge sites, 24m-42. -/
theorem reductionWord_hydrophobicCount_add (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity) :
    hydrophobicCount (p.reductionWord items bulkLengths gaps) + 42 =
      24 * p.side + bulkLengths.sum := by
  have hcount := hydrophobicCount_assembleReductionWord gaps (p.reductionUnitBodies items bulkLengths)
  rw [reductionUnitBodies_hydrophobicCount_sum] at hcount
  change hydrophobicCount (p.reductionWord items bulkLengths gaps) = _ at hcount
  have hitems : 2 * p.scale * items.sum = 2 * (p.bins * p.binDimers) := by
    rw [htotal]
    unfold binDimers
    ring
  rw [hitems] at hcount
  have hframe := p.frameWord_count
  have htrack := p.track_total_dimer_count
  have hlarge := p.side_ge
  omega

theorem reductionWord_hydrophobicCount (p : ConstructionParameters)
    (items bulkLengths : List ℕ) (gaps : ℕ → ℕ)
    (htotal : items.sum = p.bins * p.capacity)
    (hbulk : 24 * p.side + bulkLengths.sum = octahedralNumber p.side + 42) :
    hydrophobicCount (p.reductionWord items bulkLengths gaps) = octahedralNumber p.side := by
  have h := p.reductionWord_hydrophobicCount_add items bulkLengths gaps htotal
  omega

end ConstructionParameters

end ProteinFolding.Tetrahedral

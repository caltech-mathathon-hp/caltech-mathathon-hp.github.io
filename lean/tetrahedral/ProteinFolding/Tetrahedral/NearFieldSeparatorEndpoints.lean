import ProteinFolding.Tetrahedral.NearFieldSeparatorFold

/-! Exact H endpoints of the complete literal separator fold. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

theorem separatorEntryWalk_length_pos (p : ConstructionParameters) (k : ℕ) :
    0 < (separatorEntryWalkWord p k).length := by
  have h : 0 < (dimerChain 1).length := by decide
  simp only [separatorEntryWalkWord, List.length_append]
  omega

theorem separatorMiddle_length_pos (p : ConstructionParameters) (k : ℕ) :
    0 < (separatorMiddleWord p k).length := by
  have h := separatorEntryWalk_length_pos p k
  simp only [separatorMiddleWord, List.length_append]
  omega

theorem separatorMiddleOut_length_pos (p : ConstructionParameters) (k : ℕ) :
    0 < (separatorMiddleOutWord p k).length := by
  have h := separatorMiddle_length_pos p k
  simp only [separatorMiddleOutWord, List.length_append]
  omega

theorem separatorWord_length_pos (p : ConstructionParameters) (k : ℕ) :
    0 < (p.separatorWord k).length := by
  have h := separatorMiddleOut_length_pos p k
  change 0 < (separatorMiddleOutWord p k ++ dimerChain 3).length
  simp only [List.length_append]
  omega

theorem separatorEntryWalk_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (separatorEntryWalkWord p k).length) (hi : i.val = 0) :
    (separatorEntryWalk p k hk).pos i = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)) :=
  appendWord_first _ _ _ _ (by decide : 0 < (dimerChain 1).length) _ (separatorEntryChain_first p k hk) i hi

theorem separatorMiddle_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (separatorMiddleWord p k).length) (hi : i.val = 0) :
    (separatorMiddle p k hk).pos i = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)) :=
  appendWord_first _ _ _ _ (separatorEntryWalk_length_pos p k) _ (separatorEntryWalk_first p k hk) i hi

theorem separatorMiddleOut_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (separatorMiddleOutWord p k).length) (hi : i.val = 0) :
    (separatorMiddleOut p k hk).pos i = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)) :=
  appendWord_first _ _ _ _ (separatorMiddle_length_pos p k) _ (separatorMiddle_first p k hk) i hi

theorem separatorFold_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.separatorWord k).length) (hi : i.val = 0) :
    (separatorFold p k hk).pos i = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)) :=
  appendWord_first _ _ _ _ (separatorMiddleOut_length_pos p k) _ (separatorMiddleOut_first p k hk) i hi

theorem separatorFold_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.separatorWord k).length) (hi : i.val + 1 = (p.separatorWord k).length) :
    (separatorFold p k hk).pos i = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10) :=
  appendWord_last _ _ _ _ (by decide : 0 < (dimerChain 3).length) _ (separatorExitChain_last p k) i hi

theorem separatorFirstH_inA (p : ConstructionParameters) (k : ℕ) :
    InASublattice (octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1))).val := by
  have hi : 6 * (k + 1) = 2 * (3 * (k + 1)) := by omega
  rw [hi]
  exact (octEdgeZigzag_even (by have h := p.side_ge; omega) entryEdgeFrame _).1

theorem separatorLastH_inA (p : ConstructionParameters) (k : ℕ) :
    InASublattice (octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10)).val := by
  have hi : 10 * p.exitSlot k + 10 = 2 * (5 * p.exitSlot k + 5) := by omega
  rw [hi]
  exact (octEdgeZigzag_even (by have h := p.side_ge; omega) exitEdgeFrame _).1

end ProteinFolding.Tetrahedral.NearField

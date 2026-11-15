import ProteinFolding.Tetrahedral.NearFieldSeparatorChainSeparation

/-! Distinct prescribed separator indices give disjoint same-edge chains. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem edgeDimerHsites_disjoint_intervals {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame)
    (base q base' q' : ℕ)
    (hinterval : base + 2 * (q + 1) ≤ base' ∨ base' + 2 * (q' + 1) ≤ base) :
    Disjoint (edgeDimerHsites m F base q) (edgeDimerHsites m F base' q') := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp'
  have heq := octEdgeZigzag_injective hm F hj
  have hi := i.isLt
  have hjb := j.isLt
  rcases hinterval with h | h <;> omega

theorem separatorEntry_entry_Hdisjoint (p : ConstructionParameters) (k l : ℕ) (hne : k ≠ l) :
    Disjoint (edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0)
      (edgeDimerHsites p.side entryEdgeFrame (6 * (l + 1)) 0) := by
  apply edgeDimerHsites_disjoint_intervals (by have h := p.side_ge; omega)
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem separatorCenter_center_Hdisjoint (p : ConstructionParameters) (k l : ℕ) (hne : k ≠ l) :
    Disjoint (edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k) 1)
      (edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex l) 1) := by
  have hordered (a b : ℕ) (hab : a < b) : 2 * p.separatorIndex a + 4 ≤ 2 * p.separatorIndex b := by
    have hmul := Nat.mul_le_mul_right (p.binDimers + 2) (show a + 1 ≤ b by omega)
    simp only [Nat.add_mul, Nat.one_mul] at hmul
    have hd := p.binDimers_ge
    unfold ConstructionParameters.separatorIndex
    omega
  apply edgeDimerHsites_disjoint_intervals (by have h := p.side_ge; omega)
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl (hordered k l h)
  · exact Or.inr (hordered l k h)

theorem separatorExit_exit_Hdisjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l) :
    Disjoint (edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2)
      (edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot l + 6) 2) := by
  have hslot : p.exitSlot k ≠ p.exitSlot l := by
    have h1 := p.exitSlot_add k hk
    have h2 := p.exitSlot_add l hl
    omega
  apply edgeDimerHsites_disjoint_intervals (by have h := p.side_ge; omega)
  rcases lt_or_gt_of_ne hslot with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem separatorEntry_entry_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (dimerChain 1).length) (j : Fin (dimerChain 1).length) :
    (separatorEntryChain p k hk).pos i ≠ (separatorEntryChain p l hl).pos j :=
  edgeDimerFolds_disjoint (by have h := p.side_ge; omega) entryEdgeFrame entryEdgeFrame
    (6 * (k + 1)) 0 (6 * (l + 1)) 0 false false
    (separatorEntry_room p k hk) (separatorEntry_room p l hl) (separatorEntry_entry_Hdisjoint p k l hne) i j

theorem separatorCenter_center_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (dimerChain 2).length) (j : Fin (dimerChain 2).length) :
    (separatorCenterChain p k hk).pos i ≠ (separatorCenterChain p l hl).pos j :=
  edgeDimerFolds_disjoint (by have h := p.side_ge; omega) trackEdgeFrame trackEdgeFrame
    (2 * p.separatorIndex k) 1 (2 * p.separatorIndex l) 1 true true
    (separatorCenter_room p k hk) (separatorCenter_room p l hl) (separatorCenter_center_Hdisjoint p k l hne) i j

theorem separatorExit_exit_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (dimerChain 3).length) (j : Fin (dimerChain 3).length) :
    (separatorExitChain p k).pos i ≠ (separatorExitChain p l).pos j :=
  edgeDimerFolds_disjoint (by have h := p.side_ge; omega) exitEdgeFrame exitEdgeFrame
    (10 * p.exitSlot k + 6) 2 (10 * p.exitSlot l + 6) 2 true true
    (separatorExit_room p k) (separatorExit_room p l) (separatorExit_exit_Hdisjoint p k l hk hl hne) i j

end ProteinFolding.Tetrahedral.NearField

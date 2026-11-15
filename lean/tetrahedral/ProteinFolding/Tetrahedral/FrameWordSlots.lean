import ProteinFolding.Tetrahedral.FrameWord

/-! Exact arithmetic correspondence between the frame run intervals and the
slot masks used by the builder. Indices on the second edge start at V_c. -/

namespace ProteinFolding.Tetrahedral

namespace ConstructionParameters

def frameEntryOmitted (p : ConstructionParameters) (i : ℕ) : Prop :=
  i = 1 ∨ i = 2 ∨ i = 2 * p.side - 3 ∨
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ p.bins + 1 ∧ (i = 6 * k ∨ i = 6 * k + 1)

def frameExitOmitted (p : ConstructionParameters) (i : ℕ) : Prop :=
  i = 1 ∨ i = 2 * p.side - 3 ∨
    ∃ k : ℕ, k ≤ p.bins ∧ 10 * k + 6 ≤ i ∧ i ≤ 10 * k + 11

theorem frame_entry_retained_iff (p : ConstructionParameters) (i : ℕ) :
    (1 ≤ i ∧ i ≤ 2 * p.side - 3 ∧ ¬ p.frameEntryOmitted i) ↔
      (3 ≤ i ∧ i ≤ 5) ∨
      (∃ k : ℕ, k < p.bins ∧ 6 * k + 8 ≤ i ∧ i ≤ 6 * k + 11) ∨
      (6 * p.bins + 8 ≤ i ∧ i ≤ 2 * p.side - 4) := by
  have hlarge := p.family_side_bound
  constructor
  · rintro ⟨hlo, hhi, hnot⟩
    have hne1 : i ≠ 1 := fun h => hnot (Or.inl h)
    have hne2 : i ≠ 2 := fun h => hnot (Or.inr (Or.inl h))
    have hneend : i ≠ 2 * p.side - 3 := fun h => hnot (Or.inr (Or.inr (Or.inl h)))
    by_cases hfirst : i ≤ 5
    · exact Or.inl ⟨by omega, hfirst⟩
    · by_cases hlast : 6 * p.bins + 8 ≤ i
      · exact Or.inr (Or.inr ⟨hlast, by omega⟩)
      · have hdiv := Nat.mod_add_div i 6
        have hmod := Nat.mod_lt i (by decide : 0 < 6)
        have hqlo : 1 ≤ i / 6 := by omega
        have hqhi : i / 6 ≤ p.bins + 1 := by omega
        have hr : 2 ≤ i % 6 := by
          by_contra hbad
          apply hnot
          apply Or.inr
          apply Or.inr
          apply Or.inr
          exact ⟨i / 6, hqlo, hqhi, by omega⟩
        exact Or.inr (Or.inl ⟨i / 6 - 1, by omega, by omega, by omega⟩)
  · intro hseg
    rcases hseg with ⟨hl, hh⟩ | ⟨k, hk, hl, hh⟩ | ⟨hl, hh⟩
    all_goals refine ⟨by omega, by omega, ?_⟩
    all_goals intro homit
    all_goals rcases homit with h | h | h | ⟨j, hjlo, hjhi, h | h⟩ <;> omega

theorem frame_exit_retained_iff (p : ConstructionParameters) (i : ℕ) :
    (1 ≤ i ∧ i ≤ 2 * p.side - 3 ∧ ¬ p.frameExitOmitted i) ↔
      (∃ k : ℕ, k ≤ p.bins ∧ 10 * k + 2 ≤ i ∧ i ≤ 10 * k + 5) ∨
      (10 * p.bins + 12 ≤ i ∧ i ≤ 2 * p.side - 4) := by
  have hlarge := p.family_side_bound
  constructor
  · rintro ⟨hlo, hhi, hnot⟩
    have hne1 : i ≠ 1 := fun h => hnot (Or.inl h)
    have hneend : i ≠ 2 * p.side - 3 := fun h => hnot (Or.inr (Or.inl h))
    by_cases hlast : 10 * p.bins + 12 ≤ i
    · exact Or.inr ⟨hlast, by omega⟩
    · have hdiv := Nat.mod_add_div (i - 2) 10
      have hmod := Nat.mod_lt (i - 2) (by decide : 0 < 10)
      have hqhi : (i - 2) / 10 ≤ p.bins := by omega
      have hr : (i - 2) % 10 < 4 := by
        by_contra hbad
        apply hnot
        apply Or.inr
        apply Or.inr
        exact ⟨(i - 2) / 10, hqhi, by omega, by omega⟩
      exact Or.inl ⟨(i - 2) / 10, hqhi, by omega, by omega⟩
  · intro hseg
    rcases hseg with ⟨k, hk, hl, hh⟩ | ⟨hl, hh⟩
    all_goals refine ⟨by omega, by omega, ?_⟩
    all_goals intro homit
    all_goals rcases homit with h | h | ⟨j, hj, hlow, hhigh⟩ <;> omega

theorem frame_entry_tail_length (p : ConstructionParameters) :
    (2 * p.side - 4) + 1 - (6 * p.bins + 8) = p.frameTail1 := by
  have h := p.frameTail1_add
  omega

theorem frame_exit_tail_length (p : ConstructionParameters) :
    (2 * p.side - 4) + 1 - (10 * p.bins + 12) = p.frameTail2 := by
  have h := p.frameTail2_add
  omega

end ConstructionParameters

end ProteinFolding.Tetrahedral

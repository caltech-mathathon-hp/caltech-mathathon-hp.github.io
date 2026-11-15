import ProteinFolding.Tetrahedral.ProfileComposition
import Mathlib.Data.Finset.Max

/-! Compressing a finite ordered set of positive gap weights into a composition.
Integer gaps absent from the set are omitted; the newly adjacent compressed
parts contribute nonnegative extra terms, so the capped profile cannot decrease. -/

namespace ProteinFolding.Tetrahedral

open scoped BigOperators

def rawPrefix (A : Finset ℤ) (β : ℤ → ℕ) (k : ℤ) : ℕ :=
  ∑ j ∈ A.filter (fun j => j < k), β j

def rawProfileValue (C : ℕ) (A : Finset ℤ) (β : ℤ → ℕ) : ℕ :=
  ∑ k ∈ A, if k - 1 ∈ A then
    min (min (rawPrefix A β k) (C - rawPrefix A β k)) (β (k - 1) * β k) else 0

theorem rawProfileValue_singleton (C : ℕ) (β : ℤ → ℕ) (b : ℤ) :
    rawProfileValue C {b} β = 0 := by
  simp [rawProfileValue, show b - 1 ≠ b by omega]

theorem rawProfileValue_insert_max (C : ℕ) (β : ℤ → ℕ) (A : Finset ℤ) (b : ℤ)
    (hmax : ∀ k ∈ A, k < b) :
    rawProfileValue C (insert b A) β = rawProfileValue C A β +
      if b - 1 ∈ A then min (min (∑ j ∈ A, β j) (C - ∑ j ∈ A, β j))
        (β (b - 1) * β b) else 0 := by
  have hbnot : b ∉ A := by intro hb; exact lt_irrefl b (hmax b hb)
  have hprefix : rawPrefix (insert b A) β b = ∑ j ∈ A, β j := by
    unfold rawPrefix
    have heq : (insert b A).filter (fun j => j < b) = A := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hjb⟩
        · omega
        · exact hj
      · intro hj
        exact ⟨Or.inr hj, hmax j hj⟩
    rw [heq]
  have hprefix_old : ∀ k ∈ A, rawPrefix (insert b A) β k = rawPrefix A β k := by
    intro k hk
    unfold rawPrefix
    have heq : (insert b A).filter (fun j => j < k) = A.filter (fun j => j < k) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hjk⟩
        · have hkb := hmax k hk
          omega
        · exact ⟨hj, hjk⟩
      · rintro ⟨hj, hjk⟩
        exact ⟨Or.inr hj, hjk⟩
    rw [heq]
  unfold rawProfileValue
  rw [Finset.sum_insert hbnot]
  have hold : (∑ k ∈ A, if k - 1 ∈ insert b A then
      min (min (rawPrefix (insert b A) β k) (C - rawPrefix (insert b A) β k))
        (β (k - 1) * β k) else 0) =
      ∑ k ∈ A, if k - 1 ∈ A then
        min (min (rawPrefix A β k) (C - rawPrefix A β k)) (β (k - 1) * β k) else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hne : k - 1 ≠ b := by have hkb := hmax k hk; omega
    simp only [Finset.mem_insert, hne, false_or, hprefix_old k hk]
  rw [hold, hprefix]
  have hne : b - 1 ≠ b := by omega
  simp only [Finset.mem_insert, hne, false_or]
  omega

/-- Positive finite gap weights admit a composition of the same mass whose
two-sided capped functional dominates the uncompressed integer-gap sum. -/
theorem rawProfile_composition_exists (C : ℕ) (β : ℤ → ℕ) (A : Finset ℤ)
    (hne : A.Nonempty) (hβ : ∀ k ∈ A, 0 < β k) :
    ∃ (c : PositiveComposition) (k : ℤ), k ∈ A ∧ (∀ j ∈ A, j ≤ k) ∧
      c.mass = ∑ j ∈ A, β j ∧ c.lastPart = β k ∧
      rawProfileValue C A β ≤ profileValue C 0 c := by
  induction A using Finset.induction_on_max with
  | h0 => simp at hne
  | step b A hmax ih =>
    have hbnot : b ∉ A := by intro hb; exact lt_irrefl b (hmax b hb)
    have hbpos : 0 < β b := hβ b (Finset.mem_insert_self _ _)
    rcases A.eq_empty_or_nonempty with hnil | hA
    · subst A
      refine ⟨.single (β b) hbpos, b, by simp, ?_, ?_, rfl, ?_⟩
      · intro j hj
        have hjeq : j = b := by simpa using hj
        omega
      · simp [PositiveComposition.mass]
      · simpa [profileValue] using
          (rawProfileValue_singleton C β b).le
    · obtain ⟨c, a, ha, hAmax, hmass, hlast, hval⟩ :=
        ih hA (fun j hj => hβ j (Finset.mem_insert_of_mem hj))
      refine ⟨.snoc c (β b) hbpos, b, Finset.mem_insert_self _ _, ?_, ?_, rfl, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact le_rfl
        · exact le_of_lt (hmax j hj)
      · simp [PositiveComposition.mass, Finset.sum_insert hbnot, hmass, Nat.add_comm]
      · rw [rawProfileValue_insert_max C β A b hmax]
        change rawProfileValue C A β + _ ≤ profileValue C 0 c +
          min (min (0 + c.mass) (C - (0 + c.mass))) (c.lastPart * β b)
        simp only [Nat.zero_add]
        by_cases hprev : b - 1 ∈ A
        · have haeq : a = b - 1 := by
            have h₁ := hAmax (b - 1) hprev
            have h₂ := hmax a ha
            omega
          rw [if_pos hprev, hmass, hlast, haeq]
          exact Nat.add_le_add_right hval _
        · rw [if_neg hprev, Nat.add_zero]
          omega

end ProteinFolding.Tetrahedral

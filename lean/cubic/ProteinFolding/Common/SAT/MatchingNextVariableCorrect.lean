import ProteinFolding.Common.SAT.MatchingNextVariable
import ProteinFolding.Common.SAT.OccurrenceCyclesOrder

/-! The explicit bounded binary-variable searches compute exactly the sorted
occurrence cycle used by the abstract 3-dimensional-matching reduction. -/

namespace ProteinFolding.TM2BoundedSearch

theorem boundedSearch_eq_least {A : Type} (test : A × ℕ → Bool) (x : A) (bound target : ℕ)
    (htarget : target < bound) (htrue : test (x, target) = true)
    (hprior : ∀ j, j < target → test (x, j) = false) :
    boundedSearch test (x, bound) = target := by
  have hs := boundedSearch_spec test x bound
  have hle : boundedSearch test (x, bound) ≤ target := by
    by_contra h
    have hf := hs.2.2 target (by omega)
    rw [htrue] at hf
    cases hf
  have hge : target ≤ boundedSearch test (x, bound) := by
    by_contra h
    have ht : boundedSearch test (x, bound) < target := by omega
    have hsuccess := hs.2.1 (by omega)
    have hfailure := hprior _ ht
    rw [hfailure] at hsuccess
    cases hsuccess
  exact Nat.le_antisymm hle hge

end ProteinFolding.TM2BoundedSearch

namespace ProteinFolding.ThreeDimensionalMatching.SourceQueries

open SAT TM2BoundedSearch

theorem laterMatch_eq_occurrenceCycle (φ : CNF) (i : Fin (indexedOccurrences φ).length)
    (hex : ∃ k, occurrenceVariable φ k = occurrenceVariable φ i ∧ i.val < k.val) :
    laterMatch (φ, i.val) = (occurrenceCycle (occurrenceVariable φ) i).val := by
  let m := occurrenceCycle (occurrenceVariable φ) i
  have hafter := occurrenceCycle_next_after (occurrenceVariable φ) i hex
  apply boundedSearch_eq_least laterVariableAt (φ, i.val) (indexedOccurrences φ).length m.val m.isLt
  · rw [laterVariableAt_correct φ i m]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(occurrenceCycle_variable (occurrenceVariable φ) i).symm, hafter.1⟩
  · intro j hj
    have hjq : j < (indexedOccurrences φ).length := Nat.lt_trans hj m.isLt
    let jf : Fin (indexedOccurrences φ).length := ⟨j, hjq⟩
    change laterVariableAt ((φ, i.val), jf.val) = false
    rw [laterVariableAt_correct φ i jf]
    by_cases heq : occurrenceVariable φ i = occurrenceVariable φ jf
    · by_cases hgt : i.val < j
      · have hmin := hafter.2 jf heq.symm hgt
        change m.val ≤ j at hmin
        omega
      · simp only [heq, decide_true, Bool.true_and]
        change decide (i.val < j) = false
        simp only [hgt, decide_false]
    · simp only [heq, decide_false, Bool.false_and]

theorem firstMatch_eq_occurrenceCycle_of_last (φ : CNF) (i : Fin (indexedOccurrences φ).length)
    (hnone : ∀ k, occurrenceVariable φ k = occurrenceVariable φ i → k.val ≤ i.val) :
    firstMatch (φ, i.val) = (occurrenceCycle (occurrenceVariable φ) i).val := by
  let m := occurrenceCycle (occurrenceVariable φ) i
  have hleast := occurrenceCycle_next_wrap (occurrenceVariable φ) i hnone
  apply boundedSearch_eq_least sameVariableAt (φ, i.val) (indexedOccurrences φ).length m.val m.isLt
  · rw [sameVariableAt_correct φ i m]
    simp only [decide_eq_true_eq]
    exact (occurrenceCycle_variable (occurrenceVariable φ) i).symm
  · intro j hj
    have hjq : j < (indexedOccurrences φ).length := Nat.lt_trans hj m.isLt
    let jf : Fin (indexedOccurrences φ).length := ⟨j, hjq⟩
    change sameVariableAt ((φ, i.val), jf.val) = false
    rw [sameVariableAt_correct φ i jf]
    by_cases heq : occurrenceVariable φ i = occurrenceVariable φ jf
    · have hmin := hleast jf heq.symm
      change m.val ≤ j at hmin
      omega
    · simp only [heq, decide_false]

theorem laterMatch_eq_bound_of_last (φ : CNF) (i : Fin (indexedOccurrences φ).length)
    (hnone : ∀ k, occurrenceVariable φ k = occurrenceVariable φ i → k.val ≤ i.val) :
    laterMatch (φ, i.val) = (indexedOccurrences φ).length := by
  have hs := boundedSearch_spec laterVariableAt (φ, i.val) (indexedOccurrences φ).length
  change laterMatch (φ, i.val) ≤ (indexedOccurrences φ).length ∧
    (laterMatch (φ, i.val) < (indexedOccurrences φ).length →
      laterVariableAt ((φ, i.val), laterMatch (φ, i.val)) = true) ∧
      (∀ j < laterMatch (φ, i.val), laterVariableAt ((φ, i.val), j) = false) at hs
  have hnot : ¬ laterMatch (φ, i.val) < (indexedOccurrences φ).length := by
    intro hlt
    let jf : Fin (indexedOccurrences φ).length := ⟨laterMatch (φ, i.val), hlt⟩
    have htrue := hs.2.1 hlt
    change laterVariableAt ((φ, i.val), jf.val) = true at htrue
    rw [laterVariableAt_correct φ i jf] at htrue
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htrue
    have hle := hnone jf htrue.1.symm
    omega
  omega

/-- The actual total bounded-search function agrees with the canonical cycle
on every valid occurrence index, including the wrap-around case. -/
theorem nextVariableIndex_correct (φ : CNF) (i : Fin (indexedOccurrences φ).length) :
    nextVariableIndex (φ, i.val) = (occurrenceCycle (occurrenceVariable φ) i).val := by
  by_cases hex : ∃ k, occurrenceVariable φ k = occurrenceVariable φ i ∧ i.val < k.val
  · have hl := laterMatch_eq_occurrenceCycle φ i hex
    have hbound := (occurrenceCycle (occurrenceVariable φ) i).isLt
    simp only [nextVariableIndex, hl, hbound, decide_true, if_true]
  · have hnone : ∀ k, occurrenceVariable φ k = occurrenceVariable φ i → k.val ≤ i.val := by
      intro k hkv
      by_contra hn
      exact hex ⟨k, hkv, by omega⟩
    have hl := laterMatch_eq_bound_of_last φ i hnone
    have hf := firstMatch_eq_occurrenceCycle_of_last φ i hnone
    simp only [nextVariableIndex, hl, lt_self_iff_false, decide_false, Bool.false_eq_true, if_false, hf]

end ProteinFolding.ThreeDimensionalMatching.SourceQueries

import ProteinFolding.Common.TM2ProductMap

/-! Least successful index in a finite interval. The later machine constructor
takes actual polynomial-time predicate data and computes this total function.
No predicate oracle or complexity assumption is introduced here. -/

namespace ProteinFolding.TM2BoundedSearch

def searchFrom {A : Type} (test : A × ℕ → Bool) (x : A) : ℕ → ℕ → ℕ
  | j, 0 => j
  | j, r + 1 => if test (x, j) then j else searchFrom test x (j + 1) r

def boundedSearch {A : Type} (test : A × ℕ → Bool) (input : A × ℕ) : ℕ :=
  searchFrom test input.1 0 input.2

theorem searchFrom_bounds {A : Type} (test : A × ℕ → Bool) (x : A) (j r : ℕ) :
    j ≤ searchFrom test x j r ∧ searchFrom test x j r ≤ j + r := by
  induction r generalizing j with
  | zero => simp [searchFrom]
  | succ r ih =>
    cases ht : test (x, j)
    · simp only [searchFrom, ht, Bool.false_eq_true, if_false]
      have h := ih (j + 1)
      omega
    · simp [searchFrom, ht]

theorem searchFrom_success {A : Type} (test : A × ℕ → Bool) (x : A) (j r : ℕ)
    (h : searchFrom test x j r < j + r) : test (x, searchFrom test x j r) = true := by
  induction r generalizing j with
  | zero => simp [searchFrom] at h
  | succ r ih =>
    cases ht : test (x, j)
    · simp only [searchFrom, ht, Bool.false_eq_true, if_false] at h ⊢
      exact ih (j + 1) (by omega)
    · simp [searchFrom, ht]

theorem searchFrom_minimal {A : Type} (test : A × ℕ → Bool) (x : A) (j r i : ℕ)
    (hji : j ≤ i) (hi : i < searchFrom test x j r) : test (x, i) = false := by
  induction r generalizing j with
  | zero => simp [searchFrom] at hi; omega
  | succ r ih =>
    cases ht : test (x, j)
    · simp only [searchFrom, ht, Bool.false_eq_true, if_false] at hi
      by_cases he : i = j
      · simpa [he] using ht
      · exact ih (j + 1) (by omega) hi
    · simp [searchFrom, ht] at hi
      omega

theorem boundedSearch_spec {A : Type} (test : A × ℕ → Bool) (x : A) (k : ℕ) :
    boundedSearch test (x, k) ≤ k ∧
      (boundedSearch test (x, k) < k → test (x, boundedSearch test (x, k)) = true) ∧
      ∀ i < boundedSearch test (x, k), test (x, i) = false := by
  refine ⟨by simpa [boundedSearch] using (searchFrom_bounds test x 0 k).2, ?_, ?_⟩
  · intro h
    exact searchFrom_success test x 0 k (by simpa [boundedSearch] using h)
  · intro i hi
    exact searchFrom_minimal test x 0 k i (Nat.zero_le _) hi

end ProteinFolding.TM2BoundedSearch

import ProteinFolding.Tetrahedral.ReductionTM2WalkModel

/-! Correctness of the deterministic index walker on an entire finite path.
The path is a proof witness only; the algorithm receives the adjacency test
and start index, and computes every next index by bounded search. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BoundedWalk

open Computability Turing

variable {P : Type} {adj : P × (ℕ × ℕ) → Bool}

theorem next_eq_of_unique (s : State P) (v : ℕ) (hv : v < s.1.2)
    (hadj : adj (s.1.1, (s.2.1.2, v)) = true) (hprev : v ≠ s.2.1.1)
    (hunique : ∀ k < s.1.2, adj (s.1.1, (s.2.1.2, k)) = true →
      k ≠ s.2.1.1 → k = v) : next adj s = v := by
  have hs := TM2BoundedSearch.boundedSearch_spec (test adj) (s.1.1, s.2.1) s.1.2
  by_cases hn : next adj s < s.1.2
  · have ht := next_success adj s hn
    exact hunique _ hn ht.1 ht.2
  · have he : next adj s = s.1.2 := by have hl := next_le adj s; omega
    have hsmall : v < next adj s := by omega
    have hf := hs.2.2 v hsmall
    simp [test, hadj, hprev] at hf

theorem next_eq_bound_of_no_next (s : State P)
    (h : ∀ k < s.1.2, adj (s.1.1, (s.2.1.2, k)) = true → k = s.2.1.1) :
    next adj s = s.1.2 := by
  have hn := next_le adj s
  by_contra he
  have hl : next adj s < s.1.2 := by omega
  have ht := next_success adj s hl
  exact ht.2 (h _ hl ht.1)

/-- An indexed complete path: its listed vertices are distinct and its only
graph neighbours are the predecessor and successor in this list. -/
structure IndexedPath (adj : P × (ℕ × ℕ) → Bool) (p : P) (N L : ℕ) (v : ℕ → ℕ) : Prop where
  positive : 0 < L
  bound : ∀ i < L, v i < N
  injective : ∀ i < L, ∀ j < L, v i = v j → i = j
  neighbours : ∀ i < L, ∀ k < N, adj (p, (v i, k)) = true ↔
    (0 < i ∧ k = v (i - 1)) ∨ (i + 1 < L ∧ k = v (i + 1))

def pathState (p : P) (N : ℕ) (v : ℕ → ℕ) (i : ℕ) : State P :=
  ((p, N), ((if i = 0 then N else v (i - 1), v i), (i + 1, false)))

def pathFinish (p : P) (N L : ℕ) (v : ℕ → ℕ) : State P :=
  ((p, N), ((if L - 1 = 0 then N else v (L - 1 - 1), v (L - 1)), (L, true)))

variable {p : P} {N L : ℕ} {v : ℕ → ℕ}

theorem IndexedPath.next_successor (hp : IndexedPath adj p N L v) (i : ℕ)
    (hi : i + 1 < L) : next adj (pathState p N v i) = v (i + 1) := by
  have hiL : i < L := by omega
  apply next_eq_of_unique (pathState p N v i) (v (i + 1)) (hp.bound _ hi)
  · exact (hp.neighbours i hiL _ (hp.bound _ hi)).2 (Or.inr ⟨hi, rfl⟩)
  · change v (i + 1) ≠ if i = 0 then N else v (i - 1)
    split
    · exact Nat.ne_of_lt (hp.bound _ hi)
    · intro he
      have hj : i - 1 < L := by omega
      have hh := hp.injective (i + 1) hi (i - 1) hj he
      omega
  · intro k hk hadj hprev
    rcases (hp.neighbours i hiL k hk).1 hadj with ⟨hip, hkprev⟩ | ⟨_, hksucc⟩
    · exfalso
      apply hprev
      change k = if i = 0 then N else v (i - 1)
      simpa only [if_neg (by omega : i ≠ 0)] using hkprev
    · exact hksucc

theorem IndexedPath.next_at_end (hp : IndexedPath adj p N L v) :
    next adj (pathState p N v (L - 1)) = N := by
  have hi : L - 1 < L := by have h := hp.positive; omega
  apply next_eq_bound_of_no_next
  intro k hk hadj
  rcases (hp.neighbours (L - 1) hi k hk).1 hadj with ⟨hip, he⟩ | ⟨hbad, _⟩
  · change k = if L - 1 = 0 then N else v (L - 1 - 1)
    simpa only [if_neg (by omega : L - 1 ≠ 0)] using he
  · omega

theorem IndexedPath.step_successor (hp : IndexedPath adj p N L v) (i : ℕ)
    (hi : i + 1 < L) : step adj (pathState p N v i) = pathState p N v (i + 1) := by
  have hn := hp.next_successor i hi
  have hb := hp.bound (i + 1) hi
  simp only [step, pathState, Bool.false_eq_true, ↓reduceIte] at hn ⊢
  rw [hn]
  simp only [hb, ↓reduceIte, Nat.add_sub_cancel_right, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false]

theorem IndexedPath.iterate_before_end (hp : IndexedPath adj p N L v) (i : ℕ)
    (hi : i < L) : (step adj)^[i] (initial p N (v 0)) = pathState p N v i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    exact hp.step_successor i hi

theorem IndexedPath.iterate_to_end (hp : IndexedPath adj p N L v) :
    (step adj)^[L] (initial p N (v 0)) = pathFinish p N L v := by
  have hL := hp.positive
  have he : L = (L - 1) + 1 := by omega
  conv_lhs => rw [he, Function.iterate_succ_apply']
  rw [hp.iterate_before_end (L - 1) (by omega)]
  have hn := hp.next_at_end
  simp only [step, pathState, Bool.false_eq_true, ↓reduceIte] at hn ⊢
  rw [hn]
  simp only [lt_self_iff_false, ↓reduceIte]
  change ((p, N), ((if L - 1 = 0 then N else v (L - 1 - 1), v (L - 1)),
    (L - 1 + 1, true))) = pathFinish p N L v
  have hlen : L - 1 + 1 = L := by omega
  rw [hlen]
  rfl

theorem iterate_of_finished (s : State P) (hs : s.2.2.2 = true) (n : ℕ) :
    (step adj)^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, step_finished adj s hs]

theorem IndexedPath.iterate_after_end (hp : IndexedPath adj p N L v) (n : ℕ)
    (hn : L ≤ n) : (step adj)^[n] (initial p N (v 0)) = pathFinish p N L v := by
  have he : n = (n - L) + L := by omega
  rw [he, Function.iterate_add_apply, hp.iterate_to_end]
  exact iterate_of_finished _ rfl _

end ProteinFolding.Tetrahedral.ReductionTM2.BoundedWalk

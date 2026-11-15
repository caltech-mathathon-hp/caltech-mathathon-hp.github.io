import ProteinFolding.Tetrahedral.ReductionTM2Iterate
import ProteinFolding.Common.TM2BoundedSearch
import ProteinFolding.Tetrahedral.ReductionTM2Basics

/-! Deterministic bounded graph following on natural vertex indices.
Only a least-neighbour search is used; no maximal-path choice occurs in this
construction. The machine instantiation is in ReductionTM2Walk. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BoundedWalk

open Computability Turing

variable {P : Type}

/-- Parameter and vertex bound, previous/current indices, length and stop bit. -/
abbrev State (P : Type) := (P × ℕ) × ((ℕ × ℕ) × (ℕ × Bool))

abbrev Query (P : Type) := P × (ℕ × ℕ)

def stateEncoding (ep : FinEncoding P) : FinEncoding (State P) :=
  pairEncoding (pairEncoding ep unaryFinEncodingNat)
    (pairEncoding (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)
      (pairEncoding unaryFinEncodingNat finEncodingBoolBool))

def queryEncoding (ep : FinEncoding P) : FinEncoding (Query P) :=
  pairEncoding ep (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)

def test (adj : P × (ℕ × ℕ) → Bool) (qj : Query P × ℕ) : Bool :=
  adj (qj.1.1, (qj.1.2.2, qj.2)) && decide (qj.2 ≠ qj.1.2.1)

def next (adj : P × (ℕ × ℕ) → Bool) (s : State P) : ℕ :=
  TM2BoundedSearch.boundedSearch (test adj) ((s.1.1, s.2.1), s.1.2)

def step (adj : P × (ℕ × ℕ) → Bool) (s : State P) : State P :=
  if s.2.2.2 then s
  else if next adj s < s.1.2 then
    (s.1, ((s.2.1.2, next adj s), (s.2.2.1 + 1, false)))
  else (s.1, (s.2.1, (s.2.2.1, true)))

def initial (p : P) (N start : ℕ) : State P :=
  ((p, N), ((N, start), (1, false)))

theorem next_le (adj : P × (ℕ × ℕ) → Bool) (s : State P) : next adj s ≤ s.1.2 :=
  (TM2BoundedSearch.boundedSearch_spec (test adj) (s.1.1, s.2.1) s.1.2).1

theorem next_success (adj : P × (ℕ × ℕ) → Bool) (s : State P)
    (h : next adj s < s.1.2) :
    adj (s.1.1, (s.2.1.2, next adj s)) = true ∧ next adj s ≠ s.2.1.1 := by
  have ht := (TM2BoundedSearch.boundedSearch_spec (test adj) (s.1.1, s.2.1) s.1.2).2.1 h
  simpa only [test, Bool.and_eq_true, decide_eq_true_eq] using ht

theorem next_minimal (adj : P × (ℕ × ℕ) → Bool) (s : State P) (j : ℕ)
    (hj : j < next adj s) :
    adj (s.1.1, (s.2.1.2, j)) = false ∨ j = s.2.1.1 := by
  have ht := (TM2BoundedSearch.boundedSearch_spec (test adj) (s.1.1, s.2.1) s.1.2).2.2 j hj
  simpa only [test, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_not] using ht

theorem step_parameter (adj : P × (ℕ × ℕ) → Bool) (s : State P) :
    (step adj s).1 = s.1 := by
  unfold step
  split
  · rfl
  · split <;> rfl

theorem step_finished (adj : P × (ℕ × ℕ) → Bool) (s : State P)
    (h : s.2.2.2 = true) : step adj s = s := by
  simp only [step, h, ↓reduceIte]

theorem step_bounds (adj : P × (ℕ × ℕ) → Bool) (s : State P) (M : ℕ)
    (hp : s.2.1.1 ≤ M) (hc : s.2.1.2 ≤ M) (hN : s.1.2 ≤ M) :
    (step adj s).2.1.1 ≤ M ∧ (step adj s).2.1.2 ≤ M ∧
      (step adj s).2.2.1 ≤ s.2.2.1 + 1 := by
  unfold step
  split
  · exact ⟨hp, hc, by omega⟩
  · split
    · change s.2.1.2 ≤ M ∧ next adj s ≤ M ∧ s.2.2.1 + 1 ≤ s.2.2.1 + 1
      exact ⟨hc, by have hn := next_le adj s; omega, by omega⟩
    · change s.2.1.1 ≤ M ∧ s.2.1.2 ≤ M ∧ s.2.2.1 ≤ s.2.2.1 + 1
      exact ⟨hp, hc, by omega⟩

theorem iterate_parameter (adj : P × (ℕ × ℕ) → Bool) (s : State P) (j : ℕ) :
    ((step adj)^[j] s).1 = s.1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', step_parameter, ih]

theorem iterate_bounds (adj : P × (ℕ × ℕ) → Bool) (s : State P) (j : ℕ) :
    ((step adj)^[j] s).2.1.1 ≤ s.2.1.1 + s.2.1.2 + s.1.2 ∧
      ((step adj)^[j] s).2.1.2 ≤ s.2.1.1 + s.2.1.2 + s.1.2 ∧
      ((step adj)^[j] s).2.2.1 ≤ s.2.2.1 + j := by
  induction j with
  | zero => simp only [Function.iterate_zero, id_eq]; omega
  | succ j ih =>
    have hN : ((step adj)^[j] s).1.2 ≤ s.2.1.1 + s.2.1.2 + s.1.2 := by
      rw [iterate_parameter]
      omega
    have hb := step_bounds adj ((step adj)^[j] s) _ ih.1 ih.2.1 hN
    rw [Function.iterate_succ_apply']
    exact ⟨hb.1, hb.2.1, by omega⟩

theorem encoding_length (ep : FinEncoding P) (s : State P) :
    ((stateEncoding ep).encode s).length =
      (ep.encode s.1.1).length + s.1.2 + s.2.1.1 + s.2.1.2 + s.2.2.1 + 6 := by
  have hu (n : ℕ) : (unaryEncodeNat n).length = n := unary_decode_encode_nat n
  have hb (b : Bool) : (finEncodingBoolBool.encode b).length = 1 := by cases b <;> rfl
  simp [stateEncoding, pairEncoding, unaryFinEncodingNat, hu, hb]
  omega

noncomputable def stateBound : Polynomial ℕ := Polynomial.C 5 * Polynomial.X + Polynomial.C 10

theorem iterate_encoding_bound (ep : FinEncoding P) (adj : P × (ℕ × ℕ) → Bool)
    (s : State P) (n j : ℕ) (hj : j ≤ n) :
    ((stateEncoding ep).encode ((step adj)^[j] s)).length ≤
      stateBound.eval (Iterate.inputWord (ea := stateEncoding ep) s n).length := by
  letI : Inhabited (stateEncoding ep).Γ := ⟨PairSymbol.sep⟩
  have hb := iterate_bounds adj s j
  have hp := iterate_parameter adj s j
  have hlen := encoding_length ep s
  have hin := Iterate.inputWord_length (ea := stateEncoding ep) s n
  rw [encoding_length, hp]
  simp only [stateBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

end ProteinFolding.Tetrahedral.ReductionTM2.BoundedWalk

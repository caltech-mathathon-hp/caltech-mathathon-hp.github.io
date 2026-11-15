import ProteinFolding.Common.TM2BoundedSearchRound
import ProteinFolding.Common.TM2BoundedSearchCleanup
import ProteinFolding.Common.TM2PolynomialTime
import Mathlib.Tactic.Linarith

/-! Complete bounded-search execution and polynomial step bound. Every test
is an execution of the supplied actual machine, while the unary bound controls
the number of repetitions and bounds every intermediate argument length. -/

namespace ProteinFolding.TM2BoundedSearch

open Computability Turing TM2
noncomputable section

variable {A : Type} {ea : FinEncoding A} {test : A × ℕ → Bool}
variable (hp : TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) finEncodingBoolBool test)

def loopSteps (x : A) : ℕ → ℕ → ℕ
  | j, 0 => (inputWord (ea := ea) x j).length + j + 3
  | j, r + 1 => roundSteps hp x j +
    if test (x, j) then (r + 1) + (inputWord (ea := ea) x j).length + j + 3
    else loopSteps x (j + 1) r

theorem loop_run (x : A) (j r : ℕ) :
    run hp (loopSteps hp x j r)
      (cfg hp (.inr .loop) (emptyStacks hp) (loopData x j r)) =
      some (halted hp (unaryEncodeNat (searchFrom test x j r))) := by
  induction r generalizing j with
  | zero =>
    have hzero : step (program hp) (cfg hp (.inr .loop) (emptyStacks hp) (loopData x j 0)) =
        some (cfg hp (.inr .drainBuffer) (emptyStacks hp) (loopData x j 0)) := by
      simpa only [loopData] using loop_zero hp (emptyStacks hp) (loopData x j 0)
    rw [loopSteps, show (inputWord (ea := ea) x j).length + j + 3 =
      ((inputWord (ea := ea) x j).reverse.length + j + 2) + 1 by simp,
      run_step hp hzero]
    simpa only [loopData, List.length_reverse, searchFrom] using
      cleanup_buffer_run hp (inputWord (ea := ea) x j).reverse j
  | succ r ih =>
    cases ht : test (x, j)
    · simp only [loopSteps, searchFrom, ht, Bool.false_eq_true, if_false]
      rw [run_add hp (round_false hp x j r ht)]
      exact ih (j + 1)
    · simp only [loopSteps, searchFrom, ht, if_true]
      rw [run_add hp (round_true hp x j r ht)]
      simpa only [loopData, List.length_reverse] using
        cleanup_run hp (inputWord (ea := ea) x j).reverse j (r + 1)

theorem roundSteps_bound (x : A) (j L : ℕ)
    (hlen : (inputWord (ea := ea) x j).length ≤ L) :
    roundSteps hp x j ≤ (savedPredicate hp).time.eval L + 2 * L + 4 := by
  have hs := ((savedPredicate hp).outputsFun (x, j)).steps_le_m
  have hm := TM2PolynomialTime.eval_monotone (savedPredicate hp).time hlen
  dsimp only at hm
  change ((savedPredicate hp).outputsFun (x, j)).steps ≤
    (savedPredicate hp).time.eval (inputWord (ea := ea) x j).length at hs
  dsimp only [roundSteps]
  omega

theorem loopSteps_bound (x : A) (j r L : ℕ)
    (hlen : (ea.encode x).length + j + r + 1 ≤ L) :
    loopSteps hp x j r ≤
      r * ((savedPredicate hp).time.eval L + 2 * L + 4) + 3 * L + 5 := by
  induction r generalizing j with
  | zero =>
    rw [loopSteps, inputWord_length]
    simp only [Nat.zero_mul, Nat.zero_add]
    omega
  | succ r ih =>
    have hj : (inputWord (ea := ea) x j).length ≤ L := by rw [inputWord_length]; omega
    have hr := roundSteps_bound hp x j L hj
    cases ht : test (x, j)
    · simp only [loopSteps, ht, Bool.false_eq_true, if_false]
      have hi := ih (j + 1) (by omega)
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    · simp only [loopSteps, ht, if_true]
      have hc : (r + 1) + (inputWord (ea := ea) x j).length + j + 3 ≤ 3 * L + 5 := by
        rw [inputWord_length]
        omega
      have hm := Nat.mul_le_mul_right ((savedPredicate hp).time.eval L + 2 * L + 4)
        (by omega : 1 ≤ r + 1)
      simp only [Nat.one_mul] at hm
      omega

def searchTime (x : A) (k : ℕ) : ℕ := (ea.encode x).length + k + 2 + loopSteps hp x 0 k

theorem program_run (x : A) (k : ℕ) :
    run hp (searchTime hp x k)
      (cfg hp (.inr .scanX) (emptyStacks hp)
        ⟨(pairEncoding ea unaryFinEncodingNat).encode (x, k), [], 0, 0, []⟩) =
      some (halted hp (unaryEncodeNat (boundedSearch test (x, k)))) := by
  rw [searchTime, run_add hp (input_run hp x k)]
  exact loop_run hp x 0 k

theorem searchTime_bound (x : A) (k : ℕ) :
    let L := ((pairEncoding ea unaryFinEncodingNat).encode (x, k)).length
    searchTime hp x k ≤ L * (savedPredicate hp).time.eval L + 2 * L ^ 2 + 10 * L + 10 := by
  let L := ((pairEncoding ea unaryFinEncodingNat).encode (x, k)).length
  have hL : L = (ea.encode x).length + k + 1 := inputWord_length x k
  have hl := loopSteps_bound hp x 0 k L (by omega)
  have hm := Nat.mul_le_mul_right ((savedPredicate hp).time.eval L + 2 * L + 4)
    (by omega : k ≤ L)
  change searchTime hp x k ≤ L * (savedPredicate hp).time.eval L + 2 * L ^ 2 + 10 * L + 10
  dsimp only [searchTime]
  nlinarith

end
end ProteinFolding.TM2BoundedSearch

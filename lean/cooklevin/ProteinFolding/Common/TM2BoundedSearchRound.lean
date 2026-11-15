import ProteinFolding.Common.TM2BoundedSearchInput
import ProteinFolding.Common.TM2BoundedSearchPrepare
import ProteinFolding.Common.TM2BoundedSearchOutput

/-! One complete bounded-search round. The actual predicate is evaluated on
(x,j), its preserved input is recovered, and the remaining/current counters
are updated only after a false result. -/

namespace ProteinFolding.TM2BoundedSearch

open Computability Turing TM2
noncomputable section

variable {A : Type} {ea : FinEncoding A} {test : A × ℕ → Bool}
variable (hp : TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) finEncodingBoolBool test)

theorem loop_positive (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea)) (r : ℕ) :
    step (program hp) (cfg hp (.inr .loop) S {d with remaining := r + 1}) =
      some (cfg hp (.inr .prepare) S {d with remaining := r + 1}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, auxContents, List.replicate_succ]

theorem loop_zero (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea)) :
    step (program hp) (cfg hp (.inr .loop) S {d with remaining := 0}) =
      some (cfg hp (.inr .drainBuffer) S {d with remaining := 0}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, auxContents]

theorem unary_succ_append (j : ℕ) : unaryEncodeNat (j + 1) = unaryEncodeNat j ++ [true] := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [unaryEncodeNat, List.cons_append] using congrArg (true :: ·) ih

theorem inputWord_succ (x : A) (j : ℕ) :
    inputWord (ea := ea) x (j + 1) = inputWord (ea := ea) x j ++ [.right true] := by
  simp [inputWord, pairEncoding, unaryFinEncodingNat, unary_succ_append, List.map_append, List.append_assoc]

theorem inputWord_reverse_succ (x : A) (j : ℕ) :
    (inputWord (ea := ea) x (j + 1)).reverse = .right true :: (inputWord (ea := ea) x j).reverse := by
  rw [inputWord_succ, List.reverse_append]
  rfl

theorem inputWord_length (x : A) (j : ℕ) :
    (inputWord (ea := ea) x j).length = (ea.encode x).length + j + 1 := by
  have hu : (unaryEncodeNat j).length = j := unary_decode_encode_nat j
  simp [inputWord, pairEncoding, unaryFinEncodingNat, hu]
  omega

theorem prepare_call_run (x : A) (j r : ℕ) :
    run hp ((inputWord (ea := ea) x j).length + 1)
      (cfg hp (.inr .prepare) (emptyStacks hp) (loopData x j r)) =
      some (cfg hp (.inl (savedPredicate hp).tm.main)
        (oneStack hp (savedPredicate hp).tm.k₀ (callInput hp x j))
        {(loopData x j r) with buffer := []}) := by
  have h := prepare_run hp (loopData x j r) (inputWord (ea := ea) x j).reverse []
  simpa only [List.length_reverse, oneStack_empty, List.map_reverse, List.reverse_reverse,
    List.append_nil, loopData, callInput] using h

def roundSteps (x : A) (j : ℕ) : ℕ :=
  2 * (inputWord (ea := ea) x j).length + ((savedPredicate hp).outputsFun (x, j)).steps + 4

theorem round_to_readBool (x : A) (j r : ℕ) :
    run hp (roundSteps hp x j - 1)
      (cfg hp (.inr .loop) (emptyStacks hp) (loopData x j (r + 1))) =
      some (cfg hp (.inr .readBool)
        (oneStack hp (savedPredicate hp).tm.k₁ [outputBool hp (test (x, j))])
        (loopData x j (r + 1))) := by
  rw [show roundSteps hp x j - 1 =
      (((inputWord (ea := ea) x j).length + 1) +
        (((savedPredicate hp).outputsFun (x, j)).steps + ((inputWord (ea := ea) x j).length + 1))) + 1 by
      dsimp [roundSteps]; omega]
  have hloop : step (program hp)
      (cfg hp (.inr .loop) (emptyStacks hp) (loopData x j (r + 1))) =
      some (cfg hp (.inr .prepare) (emptyStacks hp) (loopData x j (r + 1))) := by
    simpa only [loopData] using loop_positive hp (emptyStacks hp) (loopData x j r) r
  rw [run_step hp hloop]
  rw [run_add hp (prepare_call_run hp x j (r + 1))]
  rw [run_add hp (predicate_run hp x j {(loopData x j (r + 1)) with buffer := []})]
  simpa only [loopData, List.append_nil] using
    readWord_run hp {(loopData x j (r + 1)) with buffer := []}
      (inputWord (ea := ea) x j) (test (x, j))

theorem round_false (x : A) (j r : ℕ) (ht : test (x, j) = false) :
    run hp (roundSteps hp x j)
      (cfg hp (.inr .loop) (emptyStacks hp) (loopData x j (r + 1))) =
      some (cfg hp (.inr .loop) (emptyStacks hp) (loopData x (j + 1) r)) := by
  rw [show roundSteps hp x j = (roundSteps hp x j - 1) + 1 by rfl,
    run_add hp (round_to_readBool hp x j r)]
  rw [ht]
  simpa only [run, Function.iterate_one, Option.bind_some, loopData, inputWord_reverse_succ] using
    readBool_false hp (loopData x j r) r

theorem round_true (x : A) (j r : ℕ) (ht : test (x, j) = true) :
    run hp (roundSteps hp x j)
      (cfg hp (.inr .loop) (emptyStacks hp) (loopData x j (r + 1))) =
      some (cfg hp (.inr .drainRemaining) (emptyStacks hp) (loopData x j (r + 1))) := by
  rw [show roundSteps hp x j = (roundSteps hp x j - 1) + 1 by rfl,
    run_add hp (round_to_readBool hp x j r)]
  rw [ht]
  simpa only [run, Function.iterate_one, Option.bind_some] using
    readBool_true hp (loopData x j (r + 1))

end
end ProteinFolding.TM2BoundedSearch

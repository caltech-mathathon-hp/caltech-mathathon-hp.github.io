import ProteinFolding.Tetrahedral.ReductionTM2IterateRound

namespace ProteinFolding.Tetrahedral.ReductionTM2.Iterate

open Computability Turing TM2
noncomputable section
variable {A : Type} {ea : FinEncoding A} {f : A → A}
variable (h : TM2ComputableInPolyTime ea ea f) [Inhabited ea.Γ]

def loopSteps : A → ℕ → ℕ
  | a, 0 => (ea.encode a).length + 3
  | a, n + 1 => roundSteps h a + loopSteps (f a) n

theorem loop_run (a : A) (n : ℕ) :
    run h (loopSteps h a n) (cfg h (.inr .loop) (emptyStacks h) (loopData (ea := ea) a n)) =
      some (halted h (ea.encode (f^[n] a))) := by
  induction n generalizing a with
  | zero => exact finish_loop_run h a
  | succ n ih =>
    rw [loopSteps, run_add h (round_run h a n), ih]
    rw [Function.iterate_succ_apply]

theorem roundSteps_bound (a : A) (b : ℕ)
    (ha : (ea.encode a).length ≤ b) (hf : (ea.encode (f a)).length ≤ b) :
    roundSteps h a ≤ h.time.eval b + 2 * b + 3 := by
  have hc := (h.outputsFun a).steps_le_m
  have ht := TM2PolynomialTime.eval_monotone h.time ha
  dsimp only at ht
  change (h.outputsFun a).steps ≤ h.time.eval (ea.encode a).length at hc
  unfold roundSteps
  omega

theorem loopSteps_bound (a : A) (n b : ℕ)
    (hsize : ∀ j ≤ n, (ea.encode (f^[j] a)).length ≤ b) :
    loopSteps h a n ≤ n * (h.time.eval b + 2 * b + 3) + b + 3 := by
  induction n generalizing a with
  | zero =>
    have ha := hsize 0 (by omega)
    change (ea.encode a).length ≤ b at ha
    simp only [loopSteps, Nat.zero_mul, Nat.zero_add]
    omega
  | succ n ih =>
    have ha := hsize 0 (by omega)
    change (ea.encode a).length ≤ b at ha
    have hf : (ea.encode (f a)).length ≤ b := by
      simpa only [Function.iterate_one] using hsize 1 (by omega)
    have hs : ∀ j ≤ n, (ea.encode (f^[j] (f a))).length ≤ b := by
      intro j hj
      simpa only [Function.iterate_succ_apply] using hsize (j + 1) (by omega)
    have hr := roundSteps_bound h a b ha hf
    have hi := ih (f a) hs
    rw [loopSteps]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

def inputWord (a : A) (n : ℕ) : List (InputSymbol (ea := ea)) :=
  (pairEncoding ea unaryFinEncodingNat).encode (a, n)

theorem inputWord_length (a : A) (n : ℕ) :
    (inputWord (ea := ea) a n).length = (ea.encode a).length + n + 1 := by
  have hu : (unaryEncodeNat n).length = n := unary_decode_encode_nat n
  simp [inputWord, pairEncoding, unaryFinEncodingNat, hu]
  omega

def totalSteps (a : A) (n : ℕ) : ℕ := (ea.encode a).length + n + 2 + loopSteps h a n

theorem program_run (a : A) (n : ℕ) :
    run h (totalSteps h a n)
      (cfg h (.inr .readState) (emptyStacks h) ⟨inputWord (ea := ea) a n, [], 0, []⟩) =
      some (halted h (ea.encode (f^[n] a))) := by
  unfold inputWord
  rw [totalSteps, run_add h (input_run h a n)]
  exact loop_run h a n

theorem totalSteps_bound (a : A) (n b : ℕ)
    (hsize : ∀ j ≤ n, (ea.encode (f^[j] a)).length ≤ b) :
    totalSteps h a n ≤ (inputWord (ea := ea) a n).length * (h.time.eval b + 2 * b + 3) +
      (inputWord (ea := ea) a n).length + b + 4 := by
  have hl := inputWord_length (ea := ea) a n
  have hi := loopSteps_bound h a n b hsize
  have hn : n ≤ (inputWord (ea := ea) a n).length := by omega
  have hm := Nat.mul_le_mul_right (h.time.eval b + 2 * b + 3) hn
  unfold totalSteps
  omega

end
end ProteinFolding.Tetrahedral.ReductionTM2.Iterate

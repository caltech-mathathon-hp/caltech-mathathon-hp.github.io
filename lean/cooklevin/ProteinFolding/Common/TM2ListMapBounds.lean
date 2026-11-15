import ProteinFolding.Common.TM2ListMapLoop
import Mathlib.Tactic.Linarith

/-! Polynomial runtime for the actual parameterized record loop. Child calls
use their actual timed witnesses and the proved TM2 output-size polynomial. -/

namespace ProteinFolding.TM2ListMap

open Computability Turing Polynomial TM2PolynomialTime

variable {P A B : Type} {ep : FinEncoding P} {ea : FinEncoding A}
  {f : P × A → List B} [Fintype B]
  (h : TM2ComputableInPolyTime (pairEncoding ep ea) (wordEncoding B) f)

def codeLengthSum (ea : FinEncoding A) (xs : List A) : ℕ :=
  (xs.map (fun a => (ea.encode a).length)).sum

theorem encodeFields_length (xs : List A) :
    (encodeFields ea xs).length = codeLengthSum ea xs + xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [encodeFields, List.length_append, List.length_map, List.length_cons,
      codeLengthSum, List.map_cons, List.sum_cons] at *
    omega

theorem inputWord_length (p : P) (xs : List A) :
    (inputWord (ep := ep) (ea := ea) p xs).length =
      (ep.encode p).length + codeLengthSum ea xs + xs.length + 1 := by
  simp only [inputWord, List.length_append, List.length_map, List.length_cons,
    rawRecords, encodeFields_length]
  omega

theorem encoding_word (p : P) (xs : List A) :
    (pairEncoding ep (listEncoding ea)).encode (p, xs) = inputWord (ep := ep) (ea := ea) p xs := rfl

theorem codeLength_mem (a : A) (xs : List A) (ha : a ∈ xs) :
    (ea.encode a).length ≤ codeLengthSum ea xs := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [codeLengthSum]
    · have ht := ih ha
      simp only [codeLengthSum, List.map_cons, List.sum_cons] at *
      omega

theorem child_input_length_le (p : P) (a : A) (xs : List A) (ha : a ∈ xs) :
    ((pairEncoding ep ea).encode (p, a)).length ≤ (inputWord (ep := ep) (ea := ea) p xs).length := by
  have hm := codeLength_mem (ea := ea) a xs ha
  rw [inputWord_length]
  simp only [pairEncoding, List.length_append, List.length_map, List.length_cons]
  omega

theorem childSteps_bound (p : P) (a : A) (xs : List A) (ha : a ∈ xs) :
    childSteps h p a ≤ h.time.eval (inputWord (ep := ep) (ea := ea) p xs).length := by
  have ht : childSteps h p a ≤ h.time.eval ((pairEncoding ep ea).encode (p, a)).length :=
    (h.outputsFun (p, a)).steps_le_m
  exact ht.trans (eval_monotone h.time (child_input_length_le p a xs ha))

theorem child_output_bound (p : P) (a : A) (xs : List A) (ha : a ∈ xs) :
    (f (p, a)).length ≤ (outputBound h).eval (inputWord (ep := ep) (ea := ea) p xs).length := by
  have ho : (f (p, a)).length ≤ (outputBound h).eval ((pairEncoding ep ea).encode (p, a)).length :=
    outputBound_spec h (p, a)
  exact ho.trans (eval_monotone (outputBound h) (child_input_length_le p a xs ha))

theorem recordsTime_bound (p : P) (xs : List A) (T Q : ℕ)
    (ht : ∀ a ∈ xs, childSteps h p a ≤ T) (hq : ∀ a ∈ xs, (f (p, a)).length ≤ Q) :
    recordsTime h p xs + (flatOutput (f := f) p xs).length ≤
      2 * codeLengthSum ea xs + xs.length * (2 * (ep.encode p).length + 6 + T + 2 * Q) := by
  induction xs with
  | nil => simp [recordsTime, flatOutput, codeLengthSum]
  | cons a xs ih =>
    have ha := ht a (by simp)
    have hqa := hq a (by simp)
    have hi := ih (fun b hb => ht b (by simp [hb])) (fun b hb => hq b (by simp [hb]))
    simp only [recordsTime, recordTime, flatOutput, List.flatMap_cons, List.length_append,
      codeLengthSum, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

/-- Each child has polynomial time and output length in the whole input.
There are at most X records, and all transfers are charged explicitly. -/
noncomputable def mappingTime : Polynomial ℕ :=
  X * (h.time + C 2 * outputBound h + C 2 * X + C 6) + C 4 * X + C 5

theorem runningTime_bound (p : P) (xs : List A) :
    runningTime h p xs ≤ (mappingTime h).eval (inputWord (ep := ep) (ea := ea) p xs).length := by
  let L := (inputWord (ep := ep) (ea := ea) p xs).length
  have hc := recordsTime_bound h p xs (h.time.eval L) ((outputBound h).eval L)
    (fun a ha => childSteps_bound h p a xs ha) (fun a ha => child_output_bound h p a xs ha)
  have hlen : (ep.encode p).length + codeLengthSum ea xs + xs.length + 1 = L :=
    (inputWord_length p xs).symm
  have hp : (ep.encode p).length ≤ L := by omega
  have hs : codeLengthSum ea xs ≤ L := by omega
  have hx : xs.length ≤ L := by omega
  have hm := Nat.mul_le_mul hx (show
    2 * (ep.encode p).length + 6 + h.time.eval L + 2 * (outputBound h).eval L ≤
      2 * L + 6 + h.time.eval L + 2 * (outputBound h).eval L by omega)
  change runningTime h p xs ≤ (mappingTime h).eval L
  simp only [runningTime, mappingTime, eval_add, eval_mul, eval_C, eval_X]
  nlinarith

end ProteinFolding.TM2ListMap

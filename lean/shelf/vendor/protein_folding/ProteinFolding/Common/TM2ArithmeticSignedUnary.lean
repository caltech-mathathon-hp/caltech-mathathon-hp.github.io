import ProteinFolding.Common.TM2ArithmeticParsing

/-! A polynomial-time finite TM2 deciding m ≤ c, with sign/binary m and unary c.
The frozen encodings are used verbatim. Runtime is quadratic in encoded length,
including inputs whose binary magnitude is far larger than the unary counter. -/

namespace ProteinFolding.TM2Arithmetic.Comparator

open Computability Turing TM2 Polynomial

def signedUnaryEncoding : FinEncoding (ℤ × ℕ) :=
  pairEncoding signedEncoding unaryFinEncodingNat

def answer (x : ℤ × ℕ) : Bool := decide (x.1 ≤ (x.2 : ℤ))

noncomputable def comparisonTime : Polynomial ℕ := C 10 * (X + C 1) ^ 2 + C 10

theorem machine_init (i : List Sym) : initList machine i = cfg .sign initial i [] [] [] [] := by
  apply congrArg (fun S : ∀ k, List (Alphabet k) =>
    (⟨some Phase.sign, initial, S⟩ : Cfg Alphabet Phase Reg))
  funext k
  cases k <;> rfl

theorem machine_halt (b : Bool) : haltList machine [b] = doneCfg b := by
  apply congrArg (fun S : ∀ k, List (Alphabet k) =>
    (⟨none, initial, S⟩ : Cfg Alphabet Phase Reg))
  funext k
  cases k <;> rfl

theorem machine_outputs_raw (negative : Bool) (w : List Bool) (c : ℕ) :
    Nonempty (TM2OutputsInTime machine (inputWord negative w c)
      (some [if negative then true else decide (bitValue w ≤ c)])
      (10 * ((inputWord negative w c).length + 1) ^ 2 + 10)) := by
  obtain ⟨t, ht, hrun⟩ := program_run negative w c
  refine ⟨{ steps := t, evals_in_steps := ?_, steps_le_m := ?_ }⟩
  · change tick^[t] (some (initList machine (inputWord negative w c))) =
      some (haltList machine [if negative then true else decide (bitValue w ≤ c)])
    rw [machine_init, machine_halt]
    exact hrun
  · simpa only [inputWord_length, Nat.add_assoc] using ht

theorem machine_outputs (m : ℤ) (c : ℕ) :
    Nonempty (TM2OutputsInTime machine (signedUnaryEncoding.encode (m, c))
      (some [answer (m, c)]) (comparisonTime.eval (signedUnaryEncoding.encode (m, c)).length)) := by
  cases m with
  | ofNat n =>
    have henc : signedUnaryEncoding.encode (Int.ofNat n, c) = inputWord false (encodeNat n) c := rfl
    have hanswer : decide (bitValue (encodeNat n) ≤ c) = answer (Int.ofNat n, c) := by
      simp [answer, bitValue_encodeNat]
    simpa only [henc, Bool.false_eq_true, if_false, hanswer, comparisonTime,
      eval_add, eval_mul, eval_C, eval_pow, eval_X] using machine_outputs_raw false (encodeNat n) c
  | negSucc n =>
    have henc : signedUnaryEncoding.encode (Int.negSucc n, c) =
        inputWord true (encodeNat (n + 1)) c := rfl
    have hle : Int.negSucc n ≤ (c : ℤ) := by omega
    have hanswer : answer (Int.negSucc n, c) = true := by simp [answer, hle]
    simpa only [henc, if_true, hanswer, comparisonTime,
      eval_add, eval_mul, eval_C, eval_pow, eval_X] using machine_outputs_raw true (encodeNat (n + 1)) c

noncomputable def signedUnaryComputable :
    TM2ComputableInPolyTime signedUnaryEncoding finEncodingBoolBool answer where
  tm := machine
  inputAlphabet := Equiv.refl Sym
  outputAlphabet := Equiv.refl Bool
  time := comparisonTime
  outputsFun x := by
    rcases x with ⟨m, c⟩
    have h := Classical.choice (machine_outputs m c)
    simpa [Equiv.refl, finEncodingBoolBool, encodeBool] using h

theorem signedUnary_polyTimeDecidable :
    PolyTimeDecidable signedUnaryEncoding (fun x => x.1 ≤ (x.2 : ℤ)) :=
  ⟨answer, ⟨signedUnaryComputable⟩, fun x => by simp [answer]⟩

end ProteinFolding.TM2Arithmetic.Comparator

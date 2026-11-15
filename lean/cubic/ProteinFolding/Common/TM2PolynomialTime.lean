import ProteinFolding.Common.TM2Bounds

/-! Polynomial arithmetic for sequential composition. These lemmas do not
assume a machine-composition theorem: the assembly lemma requires an actual
machine with a proved timed-output property. -/

namespace ProteinFolding.TM2PolynomialTime

open Computability Turing Polynomial TM2Bounds

theorem eval_monotone (p : Polynomial ℕ) : Monotone p.eval := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro a b hab
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add (hp hab) (hq hab)
  | monomial n c =>
    intro a b hab
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)

noncomputable def outputBound {A B : Type} {ea : FinEncoding A} {eb : FinEncoding B}
    {f : A → B} (h : TM2ComputableInPolyTime ea eb f) : Polynomial ℕ :=
  X + h.time * C (machinePushBound h.tm)

theorem outputBound_spec {A B : Type} {ea : FinEncoding A} {eb : FinEncoding B}
    {f : A → B} (h : TM2ComputableInPolyTime ea eb f) (a : A) :
    (eb.encode (f a)).length ≤ (outputBound h).eval (ea.encode a).length := by
  simpa only [outputBound, eval_add, eval_X, eval_mul, eval_C] using
    polytime_encoded_output_length h a

noncomputable def compositionTime {A B D : Type} {ea : FinEncoding A} {eb : FinEncoding B}
    {ed : FinEncoding D} {f : A → B} {g : B → D}
    (hf : TM2ComputableInPolyTime ea eb f) (hg : TM2ComputableInPolyTime eb ed g) :
    Polynomial ℕ :=
  hf.time + hg.time.comp (outputBound hf) + C 2 * outputBound hf + C 2

/-- Package a concrete sequential machine after its timed-output simulation
has been proved. The runtime includes two linear stack-transfer passes. -/
noncomputable def assembleComposition {A B D : Type} {ea : FinEncoding A} {eb : FinEncoding B}
    {ed : FinEncoding D} {f : A → B} {g : B → D}
    (hf : TM2ComputableInPolyTime ea eb f) (hg : TM2ComputableInPolyTime eb ed g)
    (machine : TM2ComputableAux ea.Γ ed.Γ)
    (houtput : ∀ a,
      TM2OutputsInTime machine.tm
        ((ea.encode a).map machine.inputAlphabet.symm)
        (some ((ed.encode (g (f a))).map machine.outputAlphabet.symm))
        (hf.time.eval (ea.encode a).length + hg.time.eval (eb.encode (f a)).length +
          2 * (eb.encode (f a)).length + 2)) :
    TM2ComputableInPolyTime ea ed (g ∘ f) where
  toTM2ComputableAux := machine
  time := compositionTime hf hg
  outputsFun a := by
    have h := houtput a
    refine { h with steps_le_m := ?_ }
    have hlen := outputBound_spec hf a
    have htime := eval_monotone hg.time hlen
    dsimp only at htime
    have hsteps := h.steps_le_m
    simp only [compositionTime, eval_add, eval_comp, eval_mul, eval_C]
    omega

end ProteinFolding.TM2PolynomialTime

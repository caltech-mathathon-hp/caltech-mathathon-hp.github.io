import ProteinFolding.Tetrahedral.ReductionTM2IterateLoop

/-! Polynomial-time bounded state iteration by the actual finite controller.
The size hypothesis concerns explicit intermediate encodings, not execution
time or the computability of any graph operation. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Iterate

open Computability Turing TM2
noncomputable section
variable {A : Type} {ea : FinEncoding A} {f : A → A}
variable (h : TM2ComputableInPolyTime ea ea f) [Inhabited ea.Γ]

def machine : FinTM2 := by
  letI := h.tm.kFin
  letI := h.tm.ΛFin
  letI := h.tm.σFin
  letI := ea.ΓFin
  exact {
    K := Stack h
    k₀ := .inr .input
    k₁ := .inr .output
    Γ := Alphabet h
    Λ := Label h
    main := .inr .readState
    σ := State h
    initialState := initialState h
    Γk₀Fin := inferInstanceAs (Fintype (InputSymbol (ea := ea)))
    m := program h }

def timePolynomial (B : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X * (h.time.comp B + Polynomial.C 2 * B + Polynomial.C 3) +
    Polynomial.X + B + Polynomial.C 4

def machine_outputs (B : Polynomial ℕ) (a : A) (n : ℕ)
    (hsize : ∀ j ≤ n, (ea.encode (f^[j] a)).length ≤ B.eval (inputWord (ea := ea) a n).length) :
    TM2OutputsInTime (machine h) (inputWord (ea := ea) a n) (some (ea.encode (f^[n] a)))
      ((timePolynomial h B).eval (inputWord (ea := ea) a n).length) := by
  have hi : initList (machine h) (inputWord (ea := ea) a n) =
      cfg h (.inr .readState) (emptyStacks h) ⟨inputWord (ea := ea) a n, [], 0, []⟩ := by
    apply congrArg (fun S => (⟨some (.inr .readState), initialState h, S⟩ : Cfg (Alphabet h) (Label h) (State h)))
    funext k
    cases k with
    | inl k => rfl
    | inr k => cases k <;> rfl
  have ho : haltList (machine h) (ea.encode (f^[n] a)) = halted h (ea.encode (f^[n] a)) := by
    apply congrArg (fun S => (⟨none, initialState h, S⟩ : Cfg (Alphabet h) (Label h) (State h)))
    funext k
    cases k with
    | inl k => rfl
    | inr k => cases k <;> rfl
  refine {
    steps := totalSteps h a n
    evals_in_steps := ?_
    steps_le_m := ?_ }
  · change run h _ (initList (machine h) _) = some (haltList (machine h) _)
    rw [hi, ho]
    exact program_run h a n
  · simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_comp] using totalSteps_bound h a n
        (B.eval (inputWord (ea := ea) a n).length) hsize

/-- Iterate a supplied actual transition machine a unary number of times.
Polynomial intermediate-state growth suffices for a polynomial total runtime,
with every controller transfer and child call included in the checked bound. -/
def computable (B : Polynomial ℕ)
    (hsize : ∀ a n j, j ≤ n →
      (ea.encode (f^[j] a)).length ≤ B.eval (inputWord (ea := ea) a n).length) :
    TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) ea (fun x : A × ℕ => f^[x.2] x.1) where
  tm := machine h
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial h B
  outputsFun x := by
    obtain ⟨a, n⟩ := x
    change TM2OutputsInTime (machine h)
      (List.map id ((pairEncoding ea unaryFinEncodingNat).encode (a, n)))
      (some (List.map id (ea.encode (f^[n] a))))
      ((timePolynomial h B).eval ((pairEncoding ea unaryFinEncodingNat).encode (a, n)).length)
    simpa only [List.map_id, inputWord] using machine_outputs h B a n (hsize a n)

end
end ProteinFolding.Tetrahedral.ReductionTM2.Iterate

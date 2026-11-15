import ProteinFolding.Common.TM2BoundedSearchLoop

/-! Polynomial-time bounded least-index search in mathlib's actual TM2 model.
The only constructor input is an actual polynomial-time predicate machine.
The controller preserves encoded arguments, bounds every tested index by the
unary input bound, and empties all work stacks before returning its unary answer.
No nonempty input-alphabet assumption is needed. -/

namespace ProteinFolding.TM2BoundedSearch

open Computability Turing TM2
noncomputable section

variable {A : Type} {ea : FinEncoding A} {test : A × ℕ → Bool}
variable (hp : TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) finEncodingBoolBool test)

def machine : FinTM2 := by
  letI := (savedPredicate hp).tm.kFin
  letI := (savedPredicate hp).tm.ΛFin
  letI := (savedPredicate hp).tm.σFin
  letI := ea.ΓFin
  exact
    { K := Stack hp
      k₀ := .inr .input
      k₁ := .inr .output
      Γ := Alphabet hp
      Λ := Label hp
      main := .inr .scanX
      σ := State hp
      initialState := initialState hp
      Γk₀Fin := inferInstanceAs (Fintype (InputSymbol (ea := ea)))
      m := program hp }

def machine_outputs (x : A) (k : ℕ) :
    let L := ((pairEncoding ea unaryFinEncodingNat).encode (x, k)).length
    TM2OutputsInTime (machine hp) ((pairEncoding ea unaryFinEncodingNat).encode (x, k))
      (some (unaryEncodeNat (boundedSearch test (x, k))))
      (L * (savedPredicate hp).time.eval L + 2 * L ^ 2 + 10 * L + 10) := by
  have hi : initList (machine hp) ((pairEncoding ea unaryFinEncodingNat).encode (x, k)) =
      cfg hp (.inr .scanX) (emptyStacks hp)
        ⟨(pairEncoding ea unaryFinEncodingNat).encode (x, k), [], 0, 0, []⟩ := by
    apply congrArg (fun S => (⟨some (.inr .scanX), initialState hp, S⟩ :
      Cfg (Alphabet hp) (Label hp) (State hp)))
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i <;> rfl
  have ho : haltList (machine hp) (unaryEncodeNat (boundedSearch test (x, k))) =
      halted hp (unaryEncodeNat (boundedSearch test (x, k))) := by
    apply congrArg (fun S => (⟨none, initialState hp, S⟩ : Cfg (Alphabet hp) (Label hp) (State hp)))
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i <;> rfl
  refine
    { steps := searchTime hp x k
      evals_in_steps := ?_
      steps_le_m := searchTime_bound hp x k }
  change run hp _ (initList (machine hp) _) = some (haltList (machine hp) _)
  rw [hi, ho]
  exact program_run hp x k

/-- Given actual polynomial-time predicate data, compute its least successful
index below a unary bound, returning the bound itself if no index succeeds. -/
def boundedSearchComputable :
    TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) unaryFinEncodingNat (boundedSearch test) where
  tm := machine hp
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X * (savedPredicate hp).time + Polynomial.C 2 * Polynomial.X ^ 2 +
    Polynomial.C 10 * Polynomial.X + Polynomial.C 10
  outputsFun p := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime (machine hp)
      (List.map id ((pairEncoding ea unaryFinEncodingNat).encode p))
      (some (List.map id (unaryEncodeNat (boundedSearch test p))))
      (((pairEncoding ea unaryFinEncodingNat).encode p).length *
        (savedPredicate hp).time.eval ((pairEncoding ea unaryFinEncodingNat).encode p).length +
        2 * ((pairEncoding ea unaryFinEncodingNat).encode p).length ^ 2 +
        10 * ((pairEncoding ea unaryFinEncodingNat).encode p).length + 10)
    simpa only [List.map_id] using machine_outputs hp p.1 p.2

end
end ProteinFolding.TM2BoundedSearch

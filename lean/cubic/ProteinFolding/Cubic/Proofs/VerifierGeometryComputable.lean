import ProteinFolding.Cubic.Proofs.VerifierGeometryOuter
import ProteinFolding.Cubic.Proofs.VerifierGeometryEmit
import ProteinFolding.Cubic.Proofs.VerifierHP

/-! The complete geometric verifier as a mathlib polynomial-time machine.
The quadratic bound includes copying every suffix, all endpoint inspections,
counter cleanup, and serialization of the unary score. It holds on every word,
including malformed decoded records. -/

namespace ProteinFolding.CubicVerifier.GeometryMachine

open Computability Turing TM2

theorem geometryEncoding_encode (valid : Bool) (b : ℕ) :
    CubicHPVerifier.geometryEncoding.encode (valid, b) =
      .left valid :: .sep :: List.replicate b (.right true) := by
  have hu : unaryEncodeNat b = List.replicate b true := by
    induction b with
    | zero => rfl
    | succ b ih => simp [unaryEncodeNat, List.replicate_succ, ih]
  simp [CubicHPVerifier.geometryEncoding, pairEncoding, finEncodingBoolBool,
    encodeBool, unaryFinEncodingNat, hu]

theorem program_run (w : List Letter) :
    run (coreTime w + bondCountRecords w + 2)
      (cfg .outer initialContext [] (fun _ => 0) 0 w [] [] []) =
      some (halted (CubicHPVerifier.geometryEncoding.encode (CubicHPVerifier.geometryData w))) := by
  let result := coreResult initialContext 0 w
  have hspec := coreResult_spec w initialContext 0
  have hv : result.1.valid = geometryValid w := congrArg Prod.fst hspec
  have hb : result.2 = bondCountRecords w := congrArg Prod.snd hspec
  rw [show coreTime w + bondCountRecords w + 2 = coreTime w + (result.2 + 2) by omega]
  rw [run_add (outer_run w initialContext 0)]
  change run (result.2 + 2) (cfg .outer result.1 [] (fun _ => 0) result.2 [] [] [] []) = _
  rw [show result.2 + 2 = (result.2 + 1) + 1 by omega,
    run_step (outer_step_nil result.1 result.2), emit_run]
  simp only [List.append_nil, hv, hb, CubicHPVerifier.geometryData, geometryEncoding_encode]

def machine : FinTM2 where
  K := Stack
  k₀ := remaining
  k₁ := output
  Γ := Alphabet
  Λ := Phase
  main := .outer
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstanceAs (Fintype Letter)
  m := program

theorem initList_eq (w : List Letter) :
    initList machine w = cfg .outer initialContext [] (fun _ => 0) 0 w [] [] [] := by
  apply congrArg (fun S => (⟨some .outer, initialState, S⟩ : Cfg Alphabet Phase State))
  funext k
  rcases k with ((k | k) | k)
  · cases k <;> rfl
  · cases k; rfl
  · cases k <;> rfl

theorem haltList_eq (o : List (PairSymbol Bool Bool)) : haltList machine o = halted o := by
  apply congrArg (fun S => (⟨none, initialState, S⟩ : Cfg Alphabet Phase State))
  funext k
  rcases k with ((k | k) | k)
  · cases k <;> rfl
  · cases k; rfl
  · cases k <;> rfl

def machine_outputs (w : List Letter) : TM2OutputsInTime machine w
    (some (CubicHPVerifier.geometryEncoding.encode (CubicHPVerifier.geometryData w)))
    (5 * w.length ^ 2 + 16 * w.length + 2) := by
  refine
    { steps := coreTime w + bondCountRecords w + 2
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change run _ (initList machine w) = some (haltList machine _)
    rw [initList_eq, haltList_eq]
    exact program_run w
  · have ht := coreTime_bound w
    have hb := bondCountRecords_le w
    omega

/-- An actual finite TM2 witness, with the natural polynomial `5*X²+16*X+2`.
No geometry, composition, or verifier hypothesis remains. -/
noncomputable def geometryComputable : TM2ComputableInPolyTime (wordEncoding Letter)
    CubicHPVerifier.geometryEncoding CubicHPVerifier.geometryData where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 5 * Polynomial.X ^ 2 + Polynomial.C 16 * Polynomial.X + Polynomial.C 2
  outputsFun w := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime machine (List.map id w)
      (some (List.map id (CubicHPVerifier.geometryEncoding.encode (CubicHPVerifier.geometryData w))))
      (5 * w.length ^ 2 + 16 * w.length + 2)
    simpa only [List.map_id] using machine_outputs w

end ProteinFolding.CubicVerifier.GeometryMachine

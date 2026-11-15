import ProteinFolding.Common.TM2FanoutLeft
import ProteinFolding.Common.TM2PairSwap

/-! Independent polynomial-time computations on pair fields, and pairing two
computations on the same input. The left-field simulator preserves the passive
encoded word. Swapping fields then supplies the right-field construction. -/

namespace ProteinFolding.TM2ProductMap

open Computability Turing Polynomial TM2PolynomialTime

variable {A B C D : Type} {ea : FinEncoding A} {eb : FinEncoding B}
  {ec : FinEncoding C} {ed : FinEncoding D} {f : A → C} {g : B → D}

noncomputable def leftMapTime (h : TM2ComputableInPolyTime ea ec f) : Polynomial ℕ :=
  h.time + Polynomial.C 2 * X + Polynomial.C 2 * outputBound h + Polynomial.C 6

noncomputable def leftMapComputable (h : TM2ComputableInPolyTime ea ec f) (eb : FinEncoding B) :
    TM2ComputableInPolyTime (pairEncoding ea eb) (pairEncoding ec eb)
      (fun p => (f p.1, p.2)) where
  tm := TM2FanoutLeft.machine h eb (TM2CompositionPoly.alphabetSeed (h.tm.Γ h.tm.k₀))
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := leftMapTime h
  outputsFun p := by
    change TM2OutputsInTime
      (TM2FanoutLeft.machine h eb (TM2CompositionPoly.alphabetSeed (h.tm.Γ h.tm.k₀)))
      (List.map id ((pairEncoding ea eb).encode p))
      (some (List.map id ((pairEncoding ec eb).encode (f p.1, p.2))))
      ((leftMapTime h).eval ((pairEncoding ea eb).encode p).length)
    simp only [List.map_id]
    let raw := TM2FanoutLeft.machine_outputsInTime h eb
      (TM2CompositionPoly.alphabetSeed (h.tm.Γ h.tm.k₀))
      (TM2CompositionPoly.alphabetSeed_none (h.tm.Γ h.tm.k₀)) p.1 (eb.encode p.2)
    refine { raw with steps_le_m := ?_ }
    have hlen : (ea.encode p.1).length ≤ ((pairEncoding ea eb).encode p).length := by
      simp [pairEncoding]
    have ht := eval_monotone h.time hlen
    have ho := outputBound_spec h p.1
    have hom := eval_monotone (outputBound h) hlen
    dsimp only at ht hom
    have hs : raw.steps ≤ h.time.eval (ea.encode p.1).length +
        2 * ((pairEncoding ea eb).encode p).length + 2 * (ec.encode (f p.1)).length + 6 :=
      raw.steps_le_m
    simp only [leftMapTime, eval_add, eval_mul, eval_C, eval_X]
    omega

noncomputable def rightMapComputable (ea : FinEncoding A)
    (h : TM2ComputableInPolyTime eb ed g) :
    TM2ComputableInPolyTime (pairEncoding ea eb) (pairEncoding ea ed)
      (fun p => (p.1, g p.2)) :=
  TM2CompositionPoly.compose
    (TM2CompositionPoly.compose (TM2PairSwap.swapComputable ea eb) (leftMapComputable h ea))
    (TM2PairSwap.swapComputable ed ea)

noncomputable def productMapComputable (hf : TM2ComputableInPolyTime ea ec f)
    (hg : TM2ComputableInPolyTime eb ed g) :
    TM2ComputableInPolyTime (pairEncoding ea eb) (pairEncoding ec ed)
      (fun p => (f p.1, g p.2)) :=
  TM2CompositionPoly.compose (leftMapComputable hf eb) (rightMapComputable ec hg)

noncomputable def pairComputable {X Y Z : Type}
    {ex : FinEncoding X} {ey : FinEncoding Y} {ez : FinEncoding Z}
    {f : X → Y} {g : X → Z}
    (hf : TM2ComputableInPolyTime ex ey f) (hg : TM2ComputableInPolyTime ex ez g) :
    TM2ComputableInPolyTime ex (pairEncoding ey ez) (fun x => (f x, g x)) :=
  TM2CompositionPoly.compose (TM2Fanout.diagonalComputable ex) (productMapComputable hf hg)

end ProteinFolding.TM2ProductMap

import ProteinFolding.Common.TM2WordTemplates
import ProteinFolding.Common.TM2ProductMap

/-! Polynomial-time conditional output selection. Both candidate output words
and the Boolean selector are computed by actual machines; the dynamic-template
machine then selects one encoded word. This works for every finite encoding,
including an empty output alphabet. -/

namespace ProteinFolding.TM2Conditional

open Computability Turing TM2CompositionPoly TM2ProductMap

variable {A B : Type} {ea : FinEncoding A} {eb : FinEncoding B}
  {p : A → Bool} {f g : A → B}

noncomputable def encodeComputable (hf : TM2ComputableInPolyTime ea eb f) :
    TM2ComputableInPolyTime ea (wordEncoding eb.Γ) (fun x => eb.encode (f x)) :=
  { toTM2ComputableAux := hf.toTM2ComputableAux
    time := hf.time
    outputsFun := hf.outputsFun }

noncomputable def boolWordComputable (hp : TM2ComputableInPolyTime ea finEncodingBoolBool p) :
    TM2ComputableInPolyTime ea (wordEncoding Bool) (fun x => [p x]) :=
  { toTM2ComputableAux := hp.toTM2ComputableAux
    time := hp.time
    outputsFun := hp.outputsFun }

/-- A polynomial-time Boolean guard can select between polynomial-time maps.
No decidability or runtime hypothesis is hidden in the conditional. -/
noncomputable def iteComputable (hp : TM2ComputableInPolyTime ea finEncodingBoolBool p)
    (hf : TM2ComputableInPolyTime ea eb f) (hg : TM2ComputableInPolyTime ea eb g) :
    TM2ComputableInPolyTime ea eb (fun x => if p x then f x else g x) := by
  let hpair := pairComputable (pairComputable (encodeComputable hf) (encodeComputable hg))
    (boolWordComputable hp)
  let h := compose hpair (TM2WordTemplates.computable eb.Γ)
  have he (x : A) :
      TM2WordTemplates.substitute ((eb.encode (f x), eb.encode (g x)), [p x]) =
        eb.encode (if p x then f x else g x) := by
    cases p x <;> simp [TM2WordTemplates.substitute, TM2WordTemplates.words]
  refine
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := ?_ }
  intro x
  have hout := h.outputsFun x
  simpa only [Function.comp_def, he, wordEncoding, id_eq] using hout

end ProteinFolding.TM2Conditional

import ProteinFolding.Tetrahedral.ReductionTM2Words
import ProteinFolding.Common.TM2EncodingWords

namespace ProteinFolding.Tetrahedral.ReductionTM2

open Computability Turing TM2CompositionPoly TM2ProductMap

theorem encodeFields_append {A : Type} (e : FinEncoding A) (xs ys : List A) :
    TM2ListMap.encodeFields e (xs ++ ys) = TM2ListMap.encodeFields e xs ++ TM2ListMap.encodeFields e ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, TM2ListMap.encodeFields, ih, List.append_assoc, List.cons_append]

/-- Typed list concatenation uses the actual linear word concatenator on
the terminator encoding; it does not decode or re-encode by oracle. -/
noncomputable def listAppendComputable {A : Type} (e : FinEncoding A) :
    TM2ComputableInPolyTime (pairEncoding (TM2ListMap.listEncoding e) (TM2ListMap.listEncoding e))
      (TM2ListMap.listEncoding e) (fun p => p.1 ++ p.2) := by
  let h := TM2PairProjections.concatComputable (Option e.Γ)
  exact {
    toTM2ComputableAux := h.toTM2ComputableAux
    time := h.time
    outputsFun := fun p => by
      have hout := h.outputsFun ((TM2ListMap.listEncoding e).encode p.1, (TM2ListMap.listEncoding e).encode p.2)
      simpa only [pairEncoding, wordEncoding, TM2ListMap.listEncoding, id_eq, encodeFields_append] using hout }

noncomputable def listConcat {A X : Type} {e : FinEncoding A} {ex : FinEncoding X}
    {f g : X → List A} (hf : TM2ComputableInPolyTime ex (TM2ListMap.listEncoding e) f)
    (hg : TM2ComputableInPolyTime ex (TM2ListMap.listEncoding e) g) :
    TM2ComputableInPolyTime ex (TM2ListMap.listEncoding e) (fun x => f x ++ g x) :=
  compose (pairComputable hf hg) (listAppendComputable e)

noncomputable def singletonComputable {A : Type} (e : FinEncoding A) :
    TM2ComputableInPolyTime e (TM2ListMap.listEncoding e) (fun a => [a]) := by
  let hs := compose (TM2EncodingWords.encodeComputable e) (TM2WordMap.mapComputable (some : e.Γ → Option e.Γ))
  let hn := TM2Constants.constantComputable e (wordEncoding (Option e.Γ)) [none]
  let h := compose (pairComputable hs hn) (TM2PairProjections.concatComputable (Option e.Γ))
  exact {
    toTM2ComputableAux := h.toTM2ComputableAux
    time := h.time
    outputsFun := fun a => by
      simpa only [Function.comp_def, wordEncoding, id_eq, TM2ListMap.listEncoding,
        TM2ListMap.encodeFields, List.append_nil] using h.outputsFun a }

/-- Convert the existing source's terminated Boolean unary item fields into
the generic explicit list encoding by one checked alphabet map. -/
noncomputable def sourceItemsComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding (TM2ListMap.listEncoding unaryFinEncodingNat) Packing.Instance.sizes := by
  let h := compose (compose Packing.sizesComputable (TM2EncodingWords.encodeComputable Packing.itemEncoding))
    (TM2WordMap.mapComputable TM2UnaryRange.rangeLetter)
  exact {
    toTM2ComputableAux := h.toTM2ComputableAux
    time := h.time
    outputsFun := fun I => by
      simpa only [Function.comp_def, wordEncoding, id_eq, TM2UnaryRange.rangeLetter_list] using h.outputsFun I }

end ProteinFolding.Tetrahedral.ReductionTM2

import ProteinFolding.Tetrahedral.ReductionTM2Lists

namespace ProteinFolding.Tetrahedral.ReductionTM2

open Computability Turing TM2CompositionPoly

theorem encodeFields_flatMap {A B : Type} (e : FinEncoding B) (f : A → List B) (xs : List A) :
    TM2ListMap.encodeFields e (xs.flatMap f) =
      xs.flatMap (fun a => TM2ListMap.encodeFields e (f a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons, encodeFields_append, ih]

/-- The actual list-map controller also performs typed list-valued mapping.
The child emits explicit terminated records, which the controller concatenates. -/
noncomputable def listFlatMapComputable {P A B : Type} {ep : FinEncoding P} {ea : FinEncoding A}
    (eb : FinEncoding B) {f : P × A → List B}
    (hf : TM2ComputableInPolyTime (pairEncoding ep ea) (TM2ListMap.listEncoding eb) f) :
    TM2ComputableInPolyTime (pairEncoding ep (TM2ListMap.listEncoding ea)) (TM2ListMap.listEncoding eb)
      (fun x : P × List A => x.2.flatMap (fun a => f (x.1, a))) := by
  let he : TM2ComputableInPolyTime (pairEncoding ep ea) (wordEncoding (Option eb.Γ))
      (fun x => (TM2ListMap.listEncoding eb).encode (f x)) :=
    { toTM2ComputableAux := hf.toTM2ComputableAux
      time := hf.time
      outputsFun := hf.outputsFun }
  let h := TM2ListMap.flatMapComputable he
  exact {
    toTM2ComputableAux := h.toTM2ComputableAux
    time := h.time
    outputsFun := fun x => by
      have hout := h.outputsFun x
      simpa only [TM2ListMap.mappedFunction, TM2ListMap.listEncoding, wordEncoding,
        id_eq, encodeFields_flatMap] using hout }

end ProteinFolding.Tetrahedral.ReductionTM2

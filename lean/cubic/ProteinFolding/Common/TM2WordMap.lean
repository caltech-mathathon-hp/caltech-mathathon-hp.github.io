import ProteinFolding.Common.TM2PairProjections

/-! Polynomial-time word maps between finite alphabets. The construction is a
specialization of the proved finite filter-map machine: scanning/reversing and
then reversing the retained output restores the original order. Empty alphabets
are handled by that constructor, without a nonemptiness hypothesis here. -/

namespace ProteinFolding.TM2WordMap

open Computability Turing

noncomputable def mapComputable {A B : Type} [Fintype A] [Fintype B] (f : A → B) :
    TM2ComputableInPolyTime (wordEncoding A) (wordEncoding B) (List.map f) :=
  let h := TM2PairProjections.filterMapComputable A B (fun a => some (f a))
  { toTM2ComputableAux := h.toTM2ComputableAux
    time := h.time
    outputsFun := fun w => by
      simpa only [List.filterMap_eq_map'] using h.outputsFun w }

theorem mapComputable_time {A B : Type} [Fintype A] [Fintype B] (f : A → B) :
    (mapComputable f).time = Polynomial.C 2 * Polynomial.X + Polynomial.C 3 := rfl

example : Nonempty (TM2ComputableInPolyTime (wordEncoding Bool) (wordEncoding Bool)
    (List.map Bool.not)) := ⟨mapComputable Bool.not⟩

example : Nonempty (TM2ComputableInPolyTime (wordEncoding Empty) (wordEncoding Bool)
    (List.map (fun x : Empty => x.elim))) := ⟨mapComputable (fun x : Empty => x.elim)⟩

example : Nonempty (TM2ComputableInPolyTime (wordEncoding Empty) (wordEncoding Empty)
    (List.map (id : Empty → Empty))) := ⟨mapComputable id⟩

end ProteinFolding.TM2WordMap

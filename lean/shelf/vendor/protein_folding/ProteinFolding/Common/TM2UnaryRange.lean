import ProteinFolding.Cubic.Proofs.PackingRangeComputable
import ProteinFolding.Common.TM2ListMap
import ProteinFolding.Common.TM2EncodingWords

/-! The actual finite-range generator in the generic terminator list encoding. -/

namespace ProteinFolding.TM2UnaryRange

open Computability Turing TM2CompositionPoly

def rangeLetter (b : Bool) : Option Bool := if b then some true else none

theorem rangeLetter_unary (n : ℕ) :
    (unaryEncodeNat n).map rangeLetter = (unaryEncodeNat n).map some := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [unaryEncodeNat, List.map_cons, rangeLetter, ↓reduceIte] using congrArg (some true :: ·) ih

theorem rangeLetter_list (xs : List ℕ) :
    (Packing.itemEncoding.encode xs).map rangeLetter =
      (TM2ListMap.listEncoding unaryFinEncodingNat).encode xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa only [Packing.itemEncoding, SAT.encTerminated, List.flatMap_cons,
      List.map_append, List.map_cons, List.map_nil, rangeLetter, ↓reduceIte,
      TM2ListMap.listEncoding, TM2ListMap.encodeFields, unaryFinEncodingNat,
      rangeLetter_unary, List.append_assoc] using
      congrArg ((unaryEncodeNat a).map some ++ none :: ·) ih

/-- Produce the explicit list `0,...,n-1`, with unary records and one delimiter
per record, by the proved finite TM2 range machine and a linear alphabet map. -/
noncomputable def rangeComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat (TM2ListMap.listEncoding unaryFinEncodingNat) List.range := by
  let h := compose
    (compose PackingRange.rangeComputable (TM2EncodingWords.encodeComputable Packing.itemEncoding))
    (TM2WordMap.mapComputable rangeLetter)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun n => by
        simpa only [wordEncoding, Function.comp_def, id_eq, rangeLetter_list] using h.outputsFun n }

end ProteinFolding.TM2UnaryRange

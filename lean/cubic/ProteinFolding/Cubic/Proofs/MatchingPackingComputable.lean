import ProteinFolding.Cubic.Proofs.MatchingPackingGenerate

/-! The matching-to-modified-packing reduction as an actual polynomial-time
TM2. This closes the machine obligation of the bounded numerical reduction;
it does not assume that matching or packing is NP-hard. -/

namespace ProteinFolding.MatchingPacking

open Computability Turing ThreeDimensionalMatching NumericPacking
open TM2CompositionPoly TM2ProductMap TM2PairProjections
open Generate

section Append
variable {A : Type} {ea : FinEncoding A} {u v : A → List Bool}
noncomputable def appendWords (hu : TM2ComputableInPolyTime ea (wordEncoding Bool) u)
    (hv : TM2ComputableInPolyTime ea (wordEncoding Bool) v) :
    TM2ComputableInPolyTime ea (wordEncoding Bool) (fun a => u a ++ v a) :=
  compose (pairComputable hu hv) (concatComputable Bool)
end Append

noncomputable def sortedItemsWordComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding (wordEncoding Bool)
      (fun I => Packing.itemEncoding.encode (Packing.scale 2 (sortedRawInstance I)).sizes) := by
  let hx := appendWords (realBlockComputable (make := fun n i => xToken n i true) (Values.xComputable true))
    (dummyBlockComputable xCoordinatesComputable (make := fun n i => xToken n i false) (Values.xComputable false))
  let hy := appendWords (realBlockComputable (make := fun n i => yToken n i true) (Values.yComputable true))
    (dummyBlockComputable yCoordinatesComputable (make := fun n i => yToken n i false) (Values.yComputable false))
  let hz := appendWords (realBlockComputable (make := fun n i => zToken n i true) (Values.zComputable true))
    (dummyBlockComputable zCoordinatesComputable (make := fun n i => zToken n i false) (Values.zComputable false))
  let h := appendWords (appendWords (appendWords selectorBlockComputable hx) hy) hz
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => by
        simpa only [Function.comp_def, Packing.scale, sortedRawInstance, sortedTokens,
          sortedCoordinateTokens, List.map_append, List.map_map, Token.value,
          selectorToken, item_code_append, wordEncoding, id_eq] using h.outputsFun I }

def keepTerminator : Option tripleFieldsEncoding.Γ → Option Bool
  | none => some true
  | some _ => none

theorem keepTerminator_some (w : List tripleFieldsEncoding.Γ) :
    (w.map some).filterMap keepTerminator = [] := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [keepTerminator, ih]

theorem keepTerminator_records (ts : List Triple) :
    ((TM2ListMap.listEncoding tripleFieldsEncoding).encode ts).filterMap keepTerminator =
      unaryEncodeNat ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change ((tripleFieldsEncoding.encode t).map some ++ none :: TM2ListMap.encodeFields tripleFieldsEncoding ts).filterMap
      keepTerminator = unaryEncodeNat (ts.length + 1)
    rw [List.filterMap_append, keepTerminator_some]
    simpa only [keepTerminator, List.filterMap_cons, unaryEncodeNat, List.nil_append] using congrArg (true :: ·) ih

noncomputable def triplesLengthComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding unaryFinEncodingNat
      (fun I => I.triples.length) := by
  let h := compose (Packing.toCode Input.triplesListComputable)
    (filterMapComputable (Option tripleFieldsEncoding.Γ) Bool keepTerminator)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => by
        simpa only [Function.comp_def, keepTerminator_records, wordEncoding, id_eq, unaryFinEncodingNat] using h.outputsFun I }

noncomputable def sortedRawDoubledComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding Packing.instanceEncoding
      (fun I => Packing.scale 2 (sortedRawInstance I)) := by
  let hs := Packing.ofCode (eb := Packing.itemEncoding)
    (f := fun I => (Packing.scale 2 (sortedRawInstance I)).sizes) sortedItemsWordComputable
  let hc := Values.mul (Values.constant 2) (compose Input.sizeComputable Values.capacityComputable)
  let h := pairComputable hs (pairComputable hc triplesLengthComputable)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => h.outputsFun I }

noncomputable def sizeZeroComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding finEncodingBoolBool
      (fun I => decide (I.size = 0)) := by
  let hp := compose Input.sizeComputable TM2UnaryComparison.positiveComputable
  let h := compose hp TM2Boolean.notComputable
  have he (I : ThreeDimensionalMatching.Instance) : (!(decide (0 < I.size))) = decide (I.size = 0) := by
    cases I.size <;> simp
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => by simpa only [Function.comp_def, he] using h.outputsFun I }

/-- Actual polynomial-time witness for the sorted dummy-order reduction. Its
unary output is economical, and the numerical exponent is fixed at six. -/
noncomputable def sortedToModifiedComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding Packing.instanceEncoding sortedToModified := by
  let hy := TM2Constants.constantComputable ThreeDimensionalMatching.instanceEncoding Packing.instanceEncoding yesPacking
  let hn := TM2Constants.constantComputable ThreeDimensionalMatching.instanceEncoding Packing.instanceEncoding noPacking
  let hi := TM2Conditional.iteComputable sizeZeroComputable hy sortedRawDoubledComputable
  let h := TM2Conditional.iteComputable Input.wellFormedComputable hi hn
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => by
        simpa only [sortedToModified, decide_eq_true_eq] using h.outputsFun I }

/-- Correctness and a fully constructed finite-machine polynomial-time witness
for strong unary modified packing, with no source-hardness assumption. -/
theorem matching_karpReduces_modified :
    KarpReduces ThreeDimensionalMatching.instanceEncoding Packing.instanceEncoding
      ThreeDimensionalMatching.Accepts Packing.ModifiedAccepts :=
  ⟨sortedToModified, ⟨sortedToModifiedComputable⟩, sortedToModified_correct⟩

end ProteinFolding.MatchingPacking

import ProteinFolding.Cubic.Proofs.MatchingPackingValues
import ProteinFolding.Cubic.Proofs.MatchingPackingInputComputable
import ProteinFolding.Cubic.Proofs.MatchingPackingSorted
import ProteinFolding.Cubic.Proofs.PackingRangeComputable
import ProteinFolding.Cubic.Proofs.PackingCountComputable
import ProteinFolding.Common.TM2WordRepeat

/-! Actual polynomial-time generation of the numerical packing items. Shared
parameters are retained by the explicit finite list-mapping machine. Dummy
items are emitted in vertex order, with multiplicities counted by a finite
machine; the sorted construction is already proved equivalent to the original.
-/

namespace ProteinFolding.MatchingPacking.Generate

open Computability Turing ThreeDimensionalMatching NumericPacking
open TM2CompositionPoly TM2ProductMap TM2PairProjections

def natListEncoding : FinEncoding (List ℕ) := TM2ListMap.listEncoding unaryFinEncodingNat

def tagUnary : Bool → Option Bool := fun b => if b then some true else none
def untagUnary : Option Bool → Bool := fun b => b.getD false

theorem tag_unary (n : ℕ) : (unaryEncodeNat n).map tagUnary = (unaryEncodeNat n).map some := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, tagUnary, ih]

theorem untag_unary (n : ℕ) : ((unaryEncodeNat n).map some).map untagUnary = unaryEncodeNat n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, untagUnary, ih]

theorem tag_items (xs : List ℕ) :
    (Packing.itemEncoding.encode xs).map tagUnary = natListEncoding.encode xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa [Packing.itemEncoding, SAT.encTerminated, natListEncoding,
      TM2ListMap.listEncoding, TM2ListMap.encodeFields, List.map_append,
      unaryFinEncodingNat, tag_unary, tagUnary, List.append_assoc] using
      congrArg ((unaryEncodeNat a).map some ++ none :: ·) ih

theorem untag_items (xs : List ℕ) :
    (natListEncoding.encode xs).map untagUnary = Packing.itemEncoding.encode xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa [Packing.itemEncoding, SAT.encTerminated, natListEncoding,
      TM2ListMap.listEncoding, TM2ListMap.encodeFields, List.map_append,
      unaryFinEncodingNat, untagUnary, Function.comp_def, List.append_assoc] using
      congrArg ((unaryEncodeNat a) ++ false :: ·) ih

noncomputable def toNatListComputable :
    TM2ComputableInPolyTime Packing.itemEncoding natListEncoding (id : List ℕ → List ℕ) := by
  let h := compose (Packing.toCode (idComputableInPolyTime Packing.itemEncoding))
    (TM2WordMap.mapComputable tagUnary)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun xs => by simpa only [Function.comp_def, tag_items, wordEncoding, id_eq] using h.outputsFun xs }

noncomputable def fromNatListComputable :
    TM2ComputableInPolyTime natListEncoding Packing.itemEncoding (id : List ℕ → List ℕ) := by
  let h := compose (Packing.toCode (idComputableInPolyTime natListEncoding))
    (TM2WordMap.mapComputable untagUnary)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun xs => by simpa only [Function.comp_def, untag_items, wordEncoding, id_eq] using h.outputsFun xs }

noncomputable def rangeListComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat natListEncoding List.range :=
  compose PackingRange.rangeComputable toNatListComputable

noncomputable def coordinatesComputable {proj : Triple → ℕ}
    (hp : TM2ComputableInPolyTime tripleFieldsEncoding unaryFinEncodingNat proj) :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding Packing.itemEncoding
      (fun I => I.triples.map proj) := by
  let hchild := compose (sndComputable unaryFinEncodingNat tripleFieldsEncoding) hp
  let hm := TM2ListMap.mapComputable unaryFinEncodingNat hchild
  exact compose (g := (id : List ℕ → List ℕ))
    (compose (g := fun px : ℕ × List Triple => px.2.map proj)
      (pairComputable Input.sizeComputable Input.triplesListComputable) hm)
    fromNatListComputable

noncomputable def xCoordinatesComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding Packing.itemEncoding xCoordinates :=
  coordinatesComputable (fstComputable unaryFinEncodingNat (pairEncoding unaryFinEncodingNat unaryFinEncodingNat))

noncomputable def yCoordinatesComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding Packing.itemEncoding yCoordinates :=
  coordinatesComputable (compose (sndComputable unaryFinEncodingNat (pairEncoding unaryFinEncodingNat unaryFinEncodingNat))
    (fstComputable unaryFinEncodingNat unaryFinEncodingNat))

noncomputable def zCoordinatesComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding Packing.itemEncoding zCoordinates :=
  coordinatesComputable (compose (sndComputable unaryFinEncodingNat (pairEncoding unaryFinEncodingNat unaryFinEncodingNat))
    (sndComputable unaryFinEncodingNat unaryFinEncodingNat))

theorem item_code_append (xs ys : List ℕ) :
    Packing.itemEncoding.encode (xs ++ ys) = Packing.itemEncoding.encode xs ++ Packing.itemEncoding.encode ys := by
  simp only [Packing.itemEncoding, SAT.encTerminated, List.flatMap_append]

theorem item_code_map {A : Type} (f : A → ℕ) (xs : List A) :
    xs.flatMap (fun a => Packing.itemEncoding.encode [f a]) = Packing.itemEncoding.encode (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.flatMap_cons, ih, ← item_code_append]
    rfl

theorem item_code_flatMap {A : Type} (f : A → List ℕ) (xs : List A) :
    xs.flatMap (fun a => Packing.itemEncoding.encode (f a)) = Packing.itemEncoding.encode (xs.flatMap f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.flatMap_cons, List.flatMap_cons, item_code_append, ih]

theorem repeated_item_code (a k : ℕ) :
    TM2WordRepeat.wordRepeat (Packing.itemEncoding.encode [a]) k =
      Packing.itemEncoding.encode (List.replicate k a) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [TM2WordRepeat.wordRepeat, ih, List.replicate_succ', item_code_append]

noncomputable def selectorBlockComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding (wordEncoding Bool)
      (fun I => Packing.itemEncoding.encode (I.triples.map (fun t => 2 * selector I.size t.1 t.2.1 t.2.2))) := by
  let hm := TM2ListMap.flatMapComputable (Values.doubledItemComputable Values.selectorComputable)
  let h := compose (pairComputable Input.sizeComputable Input.triplesListComputable) hm
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => by
        simpa only [Function.comp_def, TM2ListMap.mappedFunction, wordEncoding, id_eq,
          item_code_map (fun t : Triple => 2 * selector I.size t.1 t.2.1 t.2.2) I.triples] using h.outputsFun I }

noncomputable def realBlockComputable {make : ℕ → ℕ → ℕ}
    (hv : TM2ComputableInPolyTime Values.pairEncodingNat unaryFinEncodingNat
      (fun ni : ℕ × ℕ => make ni.1 ni.2)) :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding (wordEncoding Bool)
      (fun I => Packing.itemEncoding.encode ((List.range I.size).map (fun i => 2 * make I.size i))) := by
  let hr := compose Input.sizeComputable rangeListComputable
  let hm := TM2ListMap.flatMapComputable (Values.doubledItemComputable hv)
  let h := compose (pairComputable Input.sizeComputable hr) hm
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => by
        simpa only [Function.comp_def, TM2ListMap.mappedFunction, wordEncoding, id_eq,
          item_code_map (fun i => 2 * make I.size i) (List.range I.size)] using h.outputsFun I }

def dummyParameterEncoding : FinEncoding (ℕ × List ℕ) := pairEncoding unaryFinEncodingNat Packing.itemEncoding
def dummyChildEncoding : FinEncoding ((ℕ × List ℕ) × ℕ) := pairEncoding dummyParameterEncoding unaryFinEncodingNat

noncomputable def dummyChildComputable {make : ℕ → ℕ → ℕ}
    (hv : TM2ComputableInPolyTime Values.pairEncodingNat unaryFinEncodingNat
      (fun ni : ℕ × ℕ => make ni.1 ni.2)) :
    TM2ComputableInPolyTime dummyChildEncoding (wordEncoding Bool)
      (fun pi => Packing.itemEncoding.encode
        (List.replicate (pi.1.2.count pi.2 - 1) (2 * make pi.1.1 pi.2))) := by
  let hp := fstComputable dummyParameterEncoding unaryFinEncodingNat
  let hi := sndComputable dummyParameterEncoding unaryFinEncodingNat
  let hn := compose hp (fstComputable unaryFinEncodingNat Packing.itemEncoding)
  let hxs := compose hp (sndComputable unaryFinEncodingNat Packing.itemEncoding)
  let hval := compose (pairComputable hn hi) hv
  let hcode := Values.doubledItemComputable hval
  let hcount := compose (pairComputable hxs hi) PackingCount.countComputable
  let hmult := Values.sub hcount (Values.constant 1)
  let h := compose (pairComputable hcode hmult) (TM2WordRepeat.computable Bool)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun pi => by
        simpa only [Function.comp_def, wordEncoding, id_eq,
          repeated_item_code (2 * make pi.1.1 pi.2) (pi.1.2.count pi.2 - 1)] using h.outputsFun pi }

noncomputable def dummyBlockComputable {coords : ThreeDimensionalMatching.Instance → List ℕ}
    (hc : TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding Packing.itemEncoding coords)
    {make : ℕ → ℕ → ℕ}
    (hv : TM2ComputableInPolyTime Values.pairEncodingNat unaryFinEncodingNat
      (fun ni : ℕ × ℕ => make ni.1 ni.2)) :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding (wordEncoding Bool)
      (fun I => Packing.itemEncoding.encode ((sortedDummies I.size (coords I)).map (fun i => 2 * make I.size i))) := by
  let hr := compose Input.sizeComputable rangeListComputable
  let hp := pairComputable Input.sizeComputable hc
  let hm := TM2ListMap.flatMapComputable (dummyChildComputable hv)
  let h := compose (pairComputable hp hr) hm
  have he (I : ThreeDimensionalMatching.Instance) :
      (List.range I.size).flatMap (fun i => Packing.itemEncoding.encode
        (List.replicate ((coords I).count i - 1) (2 * make I.size i))) =
      Packing.itemEncoding.encode ((sortedDummies I.size (coords I)).map (fun i => 2 * make I.size i)) := by
    rw [item_code_flatMap]
    simp only [sortedDummies, List.map_flatMap, List.map_replicate]
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => by
        simpa only [Function.comp_def, TM2ListMap.mappedFunction, wordEncoding, id_eq, he] using h.outputsFun I }

end ProteinFolding.MatchingPacking.Generate

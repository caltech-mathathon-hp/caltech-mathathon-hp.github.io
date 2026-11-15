import ProteinFolding.Cubic.Proofs.MatchingPackingReduction
import ProteinFolding.Common.TM2ListMap
import ProteinFolding.Common.TM2UnaryComparison
import ProteinFolding.Common.TM2Conditional

/-! Actual metadata extraction and coordinate validity checks for raw matching
inputs. A finite child machine checks the three unary coordinates against the
shared unary universe size; the explicit list mapper and Boolean fold check
every triple. Malformed raw instances require no unproved preprocessing. -/

namespace ProteinFolding.MatchingPacking.Input

open Computability Turing ThreeDimensionalMatching
open TM2CompositionPoly TM2ProductMap TM2PairProjections

noncomputable def fieldsComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding fieldsEncoding
      (fun I : ThreeDimensionalMatching.Instance => (I.size, I.triples)) := by
  let h := idComputableInPolyTime fieldsEncoding
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => h.outputsFun (I.size, I.triples) }

noncomputable def sizeComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding unaryFinEncodingNat
      ThreeDimensionalMatching.Instance.size :=
  compose (g := fun p : ℕ × List Triple => p.1) fieldsComputable
    (fstComputable unaryFinEncodingNat triplesEncoding)

noncomputable def triplesComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding triplesEncoding
      ThreeDimensionalMatching.Instance.triples :=
  compose (g := fun p : ℕ × List Triple => p.2) fieldsComputable
    (sndComputable unaryFinEncodingNat triplesEncoding)

theorem triples_record_code (ts : List Triple) :
    triplesEncoding.encode ts = (TM2ListMap.listEncoding tripleFieldsEncoding).encode ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [triplesEncoding, SAT.encTerminated, List.flatMap_cons, encodeTriple,
      TM2ListMap.listEncoding, TM2ListMap.encodeFields] at *
    simpa only [List.append_assoc, List.singleton_append] using congrArg
      (fun w => (tripleFieldsEncoding.encode t).map some ++ none :: w) ih

noncomputable def triplesListComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding
      (TM2ListMap.listEncoding tripleFieldsEncoding) ThreeDimensionalMatching.Instance.triples :=
  { toTM2ComputableAux := triplesComputable.toTM2ComputableAux
    time := triplesComputable.time
    outputsFun := fun I => by simpa only [triples_record_code] using triplesComputable.outputsFun I }

def tripleValid (n : ℕ) (t : Triple) : Prop := t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n

instance (n : ℕ) (t : Triple) : Decidable (tripleValid n t) :=
  inferInstanceAs (Decidable (t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n))

def childEncoding : FinEncoding (ℕ × Triple) := pairEncoding unaryFinEncodingNat tripleFieldsEncoding

noncomputable def tripleValidComputable :
    TM2ComputableInPolyTime childEncoding finEncodingBoolBool
      (fun p : ℕ × Triple => decide (tripleValid p.1 p.2)) := by
  let hn := fstComputable unaryFinEncodingNat tripleFieldsEncoding
  let ht := sndComputable unaryFinEncodingNat tripleFieldsEncoding
  let hx := compose ht (fstComputable unaryFinEncodingNat (pairEncoding unaryFinEncodingNat unaryFinEncodingNat))
  let hyz := compose ht (sndComputable unaryFinEncodingNat (pairEncoding unaryFinEncodingNat unaryFinEncodingNat))
  let hy := compose hyz (fstComputable unaryFinEncodingNat unaryFinEncodingNat)
  let hz := compose hyz (sndComputable unaryFinEncodingNat unaryFinEncodingNat)
  let hcx := compose (pairComputable hn hx) TM2UnaryComparison.lessBoundComputable
  let hcy := compose (pairComputable hn hy) TM2UnaryComparison.lessBoundComputable
  let hcz := compose (pairComputable hn hz) TM2UnaryComparison.lessBoundComputable
  let hrest := compose (pairComputable hcy hcz) TM2Boolean.andComputable
  let h := compose (pairComputable hcx hrest) TM2Boolean.andComputable
  simpa only [Function.comp_def, tripleValid, Bool.decide_and] using h

theorem flatMap_checks (n : ℕ) (ts : List Triple) :
    ts.flatMap (fun t => [decide (tripleValid n t)]) = ts.map (fun t => decide (tripleValid n t)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.flatMap_cons, List.singleton_append, List.map_cons, ih]

theorem fold_checks (n : ℕ) (ts : List Triple) (valid : Bool) :
    (ts.map (fun t => decide (tripleValid n t))).foldl Bool.and valid =
      (valid && decide (∀ t ∈ ts, tripleValid n t)) := by
  induction ts generalizing valid with
  | nil => simp
  | cons t ts ih =>
    rw [List.map_cons, List.foldl_cons, ih]
    simp only [List.forall_mem_cons, Bool.decide_and, Bool.and_assoc]

/-- All three bounds of every raw triple are checked by actual finite machines. -/
noncomputable def wellFormedComputable :
    TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding finEncodingBoolBool
      (fun I : ThreeDimensionalMatching.Instance => decide (WellFormed I)) := by
  let hinput := pairComputable sizeComputable triplesListComputable
  let hrecords := compose hinput
    (TM2ListMap.flatMapComputable (TM2Conditional.boolWordComputable tripleValidComputable))
  let h := compose hrecords (TM2WordFold.computable Bool Bool Bool.and id true)
  change TM2ComputableInPolyTime ThreeDimensionalMatching.instanceEncoding finEncodingBoolBool
    (fun I : ThreeDimensionalMatching.Instance =>
      (I.triples.flatMap (fun t => [decide (tripleValid I.size t)])).foldl Bool.and true) at h
  have he : (fun I : ThreeDimensionalMatching.Instance =>
      (I.triples.flatMap (fun t => [decide (tripleValid I.size t)])).foldl Bool.and true) =
      (fun I : ThreeDimensionalMatching.Instance => decide (WellFormed I)) := by
    funext I
    rw [flatMap_checks, fold_checks]
    simp only [Bool.true_and]
    rfl
  rw [he] at h
  exact h

end ProteinFolding.MatchingPacking.Input

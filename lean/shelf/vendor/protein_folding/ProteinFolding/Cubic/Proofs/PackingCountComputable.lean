import ProteinFolding.Cubic.Proofs.PackingRangeComputable
import ProteinFolding.Cubic.Proofs.PackingBalanceComputable
import ProteinFolding.Common.TM2Conditional
import ProteinFolding.Common.TM2WordMap
import ProteinFolding.Square.TM2CrossMatches

/-! Counting occurrences in unary-encoded numerical lists. This reuses the
generic finite-word record-comparison machine located in the Square directory,
specialized to the one-letter alphabet Unit. No square-lattice mathematical
result is used, and no Square source is modified. Canonical unary records
convert by one finite-alphabet symbol map. -/

namespace ProteinFolding.PackingCount

open Computability Turing TM2CompositionPoly TM2ProductMap TM2PairProjections

def unitWords (xs : List ℕ) : List (List Unit) := xs.map (fun n => List.replicate n ())

def recordEncoding : FinEncoding (List (List Unit)) := Square.listEncoding (wordEncoding Unit)

def tag : Bool → Option Unit
  | true => some ()
  | false => none

theorem unary_tag (n : ℕ) :
    (unaryEncodeNat n).map tag = (List.replicate n ()).map some := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, List.replicate_succ, tag, ih]

theorem items_tag (xs : List ℕ) :
    (Packing.itemEncoding.encode xs).map tag = recordEncoding.encode (unitWords xs) := by
  induction xs with
  | nil => rfl
  | cons n xs ih =>
    simp only [Packing.itemEncoding, SAT.encTerminated, List.flatMap_cons, List.map_append,
      List.map_cons, List.map_nil, tag, unary_tag] at *
    simpa only [recordEncoding, Square.listEncoding, Square.encodeFields, unitWords,
      List.map_cons, wordEncoding, id_eq, List.append_assoc] using congrArg
      (fun w => (List.replicate n ()).map some ++ none :: w) ih

noncomputable def recordsComputable :
    TM2ComputableInPolyTime Packing.itemEncoding recordEncoding unitWords := by
  let h := compose (TM2Conditional.encodeComputable (idComputableInPolyTime Packing.itemEncoding))
    (TM2WordMap.mapComputable tag)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun xs => by
        simpa only [Function.comp_def, items_tag, wordEncoding, id_eq] using h.outputsFun xs }

theorem unary_constant_map (n : ℕ) :
    (unaryEncodeNat n).map (fun _ => some ()) = List.replicate n (some ()) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryEncodeNat, List.replicate_succ, ih]

noncomputable def singletonComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat recordEncoding (fun n => [List.replicate n ()]) := by
  let hu := compose (TM2Conditional.encodeComputable (idComputableInPolyTime unaryFinEncodingNat))
    (TM2WordMap.mapComputable (fun _ : Bool => some ()))
  let ht := compose (pairComputable hu
    (TM2Constants.constantComputable unaryFinEncodingNat (wordEncoding (Option Unit)) [none]))
    (concatComputable (Option Unit))
  refine { toTM2ComputableAux := ht.toTM2ComputableAux, time := ht.time, outputsFun := ?_ }
  intro n
  have he : recordEncoding.encode [List.replicate n ()] =
      (unaryEncodeNat n).map (fun _ => some ()) ++ [none] := by
    simp [recordEncoding, Square.listEncoding, Square.encodeFields, wordEncoding, Packing.unary_length]
  have hout := ht.outputsFun n
  simpa only [Function.comp_def, wordEncoding, id_eq, unaryFinEncodingNat, he] using hout

theorem unit_replicate_eq (m n : ℕ) :
    List.replicate m () = List.replicate n () ↔ m = n := by
  constructor
  · intro h
    simpa only [List.length_replicate] using congrArg List.length h
  · rintro rfl
    rfl

theorem countMatches_unit (n : ℕ) (xs : List ℕ) :
    Square.CrossMatches.countMatches (List.replicate n ()) (unitWords xs) = xs.count n := by
  induction xs with
  | nil => rfl
  | cons m xs ih =>
    dsimp only [unitWords] at ih
    simp [unitWords, Square.CrossMatches.countMatches, ih,
      List.count_cons, Nat.add_comm]

noncomputable def inputRecordsComputable :
    TM2ComputableInPolyTime (pairEncoding Packing.itemEncoding unaryFinEncodingNat)
      (pairEncoding recordEncoding recordEncoding)
      (fun input : List ℕ × ℕ => ([List.replicate input.2 ()], unitWords input.1)) :=
  pairComputable
    (compose (sndComputable Packing.itemEncoding unaryFinEncodingNat) singletonComputable)
    (compose (fstComputable Packing.itemEncoding unaryFinEncodingNat) recordsComputable)

/-- An actual polynomial-time counter of equal unary records, preserving
duplicate item occurrences. The source and target encodings are unchanged. -/
noncomputable def countComputable :
    TM2ComputableInPolyTime (pairEncoding Packing.itemEncoding unaryFinEncodingNat)
      unaryFinEncodingNat (fun input : List ℕ × ℕ => input.1.count input.2) := by
  let hm := compose inputRecordsComputable (Square.CrossMatches.computable (A := Unit))
  let hb := compose hm (TM2WordMap.mapComputable (fun _ : Unit => true))
  refine { toTM2ComputableAux := hb.toTM2ComputableAux, time := hb.time, outputsFun := ?_ }
  intro input
  have he : (Square.CrossMatches.verifier ([List.replicate input.2 ()], unitWords input.1)).map
      (fun _ : Unit => true) = unaryEncodeNat (input.1.count input.2) := by
    simp [Square.CrossMatches.verifier, Square.CrossMatches.crossCount, countMatches_unit,
      PackingRange.unary_replicate]
  have hout := hb.outputsFun input
  simpa only [Function.comp_def, wordEncoding, id_eq, he, unaryFinEncodingNat] using hout

end ProteinFolding.PackingCount

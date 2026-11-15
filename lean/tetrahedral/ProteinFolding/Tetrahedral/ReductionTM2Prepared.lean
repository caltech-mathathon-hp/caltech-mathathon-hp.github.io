import ProteinFolding.Tetrahedral.ReductionTM2ZipComputable
import ProteinFolding.Tetrahedral.ReductionInputSize
import ProteinFolding.Common.TM2WordSubstitution

namespace ProteinFolding.Tetrahedral.ReductionTM2

open Computability Turing TM2CompositionPoly TM2ProductMap

def countEnd {A : Type} : Option A → List Bool
  | none => [true]
  | some _ => []

theorem countEnd_some {A : Type} (w : List A) : (w.map some).flatMap countEnd = [] := by
  induction w <;> simp [List.flatMap_cons, countEnd, *]

theorem countEnd_fields {A : Type} (e : FinEncoding A) (xs : List A) :
    (TM2ListMap.encodeFields e xs).flatMap countEnd = unaryEncodeNat xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [TM2ListMap.encodeFields, List.flatMap_append, countEnd_some,
      List.flatMap_cons, countEnd, List.nil_append, List.singleton_append, ih,
      List.length_cons, unaryEncodeNat]

/-- Count explicit record terminators by a finite alphabet substitution.
The resulting actual unary word is exactly the list length. -/
noncomputable def listLengthComputable {A : Type} (e : FinEncoding A) :
    TM2ComputableInPolyTime (TM2ListMap.listEncoding e) unaryFinEncodingNat List.length := by
  classical
  let hc := TM2WordSubstitution.flatMapComputable (countEnd : Option e.Γ → List Bool) 1 (by intro a; cases a <;> simp [countEnd])
  let h := compose (TM2EncodingWords.encodeComputable (TM2ListMap.listEncoding e)) hc
  exact {
    toTM2ComputableAux := h.toTM2ComputableAux
    time := h.time
    outputsFun := fun xs => by
      simpa only [Function.comp_def, wordEncoding, id_eq, TM2ListMap.listEncoding,
        countEnd_fields, unaryFinEncodingNat] using h.outputsFun xs }

abbrev WordInput := SourceBulkInput × List Bool
def wordInputEncoding := pairEncoding sourceBulkEncoding (wordEncoding Bool)

def preparedWord (x : WordInput) : Sequence :=
  let p : Parameters := (x.1.1.bins, x.1.1.capacity)
  let bodies := unitBodies (p, (x.1.1.sizes, x.1.2))
  assembleFlagged (Raw.baseLinkerLength p (2 * bodies.length), flagBodiesAt x.2 0 bodies)

/-- Compute the exact literal reduction word from the unary packing source,
the bulk-length list and the finite cap-parity list. Every numeric emitter,
list generation, parity zipper and linker/body assembly is an actual TM2. -/
noncomputable def preparedWordComputable :
    TM2ComputableInPolyTime wordInputEncoding sequenceEncoding preparedWord := by
  let hsource := TM2PairProjections.fstComputable sourceBulkEncoding (wordEncoding Bool)
  let hflags := TM2PairProjections.sndComputable sourceBulkEncoding (wordEncoding Bool)
  let hpacking := compose hsource (TM2PairProjections.fstComputable Packing.instanceEncoding naturalListEncoding)
  let hparams := compose (g := fun I : Packing.Instance => (I.bins, I.capacity)) hpacking sourceParametersComputable
  let hunits := compose (g := fun x : SourceBulkInput => unitBodies ((x.1.bins, x.1.capacity), (x.1.sizes, x.2)))
    hsource sourceBulkUnitsComputable
  let hlength := compose (g := List.length) hunits (listLengthComputable sequenceEncoding)
  let hwires := mul (natConstant wordInputEncoding 2) hlength
  let hL := compose (g := fun x : Parameters × ℕ => Raw.baseLinkerLength x.1 x.2)
    (pairComputable hparams hwires) baseLinkerLengthComputable
  let hzip := compose (g := fun x : List Sequence × List Bool => flagBodiesAt x.2 0 x.1)
    (pairComputable hunits hflags) Zip.zipComputable
  exact compose (g := assembleFlagged) (pairComputable hL hzip) assembleFlaggedComputable

theorem preparedWord_eq_prescribed (I : PackingSource.Instance) (hw : Packing.WellFormed I)
    (bulkLengths : List ℕ) (flags : List Bool) :
    preparedWord ((I, bulkLengths), flags) =
      (PackingSource.parameters I hw).prescribedReductionWord I.sizes bulkLengths flags := by
  let p := PackingSource.parameters I hw
  change assembleFlagged (Raw.baseLinkerLength (I.bins, I.capacity)
    (2 * (unitBodies ((I.bins, I.capacity), (I.sizes, bulkLengths))).length),
    flagBodiesAt flags 0 (unitBodies ((I.bins, I.capacity), (I.sizes, bulkLengths)))) = _
  have hu : unitBodies ((I.bins, I.capacity), (I.sizes, bulkLengths)) = p.reductionUnitBodies I.sizes bulkLengths :=
    unitBodies_parameters p I.sizes bulkLengths
  rw [hu]
  have hL : Raw.baseLinkerLength (I.bins, I.capacity) (2 * (p.reductionUnitBodies I.sizes bulkLengths).length) =
      p.baseLinkerLength (p.reductionWireCount I.sizes bulkLengths) := rfl
  rw [hL]
  exact assembleFlagged_prescribed p I.sizes bulkLengths flags

end ProteinFolding.Tetrahedral.ReductionTM2

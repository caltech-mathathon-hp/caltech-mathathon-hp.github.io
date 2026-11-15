import ProteinFolding.Tetrahedral.ReductionTM2Units
import ProteinFolding.Tetrahedral.ReductionWordLinkers
import ProteinFolding.Common.TM2Conditional

namespace ProteinFolding.Tetrahedral.ReductionTM2

open Computability Turing TM2CompositionPoly TM2ProductMap

abbrev FlaggedBody := Bool × Sequence
def flaggedBodyEncoding := pairEncoding finEncodingBoolBool sequenceEncoding
def assemblyRecordEncoding := pairEncoding unaryFinEncodingNat flaggedBodyEncoding
def flaggedAssemblyEncoding := pairEncoding unaryFinEncodingNat (TM2ListMap.listEncoding flaggedBodyEncoding)

def gapCount (L : ℕ) (same : Bool) : ℕ := L + (if same then 1 else 0) - 2
def emitFlaggedBody (x : ℕ × FlaggedBody) : Sequence :=
  List.replicate (gapCount x.1 x.2.1) .P ++ capWord x.2.2
def assembleFlagged (x : ℕ × List FlaggedBody) : Sequence :=
  [.H, .P] ++ x.2.flatMap (fun r => emitFlaggedBody (x.1, r))

noncomputable def boolUnaryComputable :
    TM2ComputableInPolyTime finEncodingBoolBool unaryFinEncodingNat (fun b => if b then 1 else 0) :=
  TM2Conditional.iteComputable (idComputableInPolyTime finEncodingBoolBool)
    (natConstant _ 1) (natConstant _ 0)

noncomputable def assemblyLengthComputable :
    TM2ComputableInPolyTime assemblyRecordEncoding unaryFinEncodingNat Prod.fst :=
  TM2PairProjections.fstComputable _ _
noncomputable def assemblyRecordComputable :
    TM2ComputableInPolyTime assemblyRecordEncoding flaggedBodyEncoding Prod.snd :=
  TM2PairProjections.sndComputable _ _
noncomputable def assemblyFlagComputable :
    TM2ComputableInPolyTime assemblyRecordEncoding finEncodingBoolBool (fun x : ℕ × FlaggedBody => x.2.1) :=
  compose assemblyRecordComputable (TM2PairProjections.fstComputable _ _)
noncomputable def assemblyBodyComputable :
    TM2ComputableInPolyTime assemblyRecordEncoding sequenceEncoding (fun x : ℕ × FlaggedBody => x.2.2) :=
  compose assemblyRecordComputable (TM2PairProjections.sndComputable _ _)

/-- Emit one exact P-linker prefix and both body caps, including the
one-site correction for same-sublattice endpoint caps. -/
noncomputable def emitFlaggedBodyComputable :
    TM2ComputableInPolyTime assemblyRecordEncoding sequenceEncoding emitFlaggedBody :=
  concat (compose (g := fun n => List.replicate n Residue.P) (sub (add assemblyLengthComputable
    (compose (g := fun b => if b then 1 else 0) assemblyFlagComputable boolUnaryComputable)) (natConstant _ 2)) (residuePower .P))
    (compose (g := capWord) assemblyBodyComputable capComputable)

/-- The actual list-map TM2 emits the entire word in its prescribed order.
The record list already contains the corresponding cap-parity flags. -/
noncomputable def assembleFlaggedComputable :
    TM2ComputableInPolyTime flaggedAssemblyEncoding sequenceEncoding assembleFlagged :=
  concat (wordConstant _ [.H, .P]) (TM2ListMap.flatMapComputable emitFlaggedBodyComputable)

def flagBodiesAt (flags : List Bool) : ℕ → List Sequence → List FlaggedBody
  | _, [] => []
  | i, u :: us => (flags[i]?.getD false, u) :: flagBodiesAt flags (i + 1) us

theorem flagBodiesAt_length (flags : List Bool) (i : ℕ) (us : List Sequence) :
    (flagBodiesAt flags i us).length = us.length := by
  induction us generalizing i <;> simp [flagBodiesAt, *]

theorem flatMap_flagBodiesAt (L : ℕ) (flags : List Bool) (i : ℕ) (us : List Sequence) :
    (flagBodiesAt flags i us).flatMap (fun r => emitFlaggedBody (L, r)) =
      assembleCappedBodies (fun j => gapCount L (flags[j]?.getD false)) i us := by
  induction us generalizing i with
  | nil => rfl
  | cons u us ih =>
    simpa only [flagBodiesAt, List.flatMap_cons, emitFlaggedBody, assembleCappedBodies,
      List.append_assoc] using congrArg (fun x => List.replicate (gapCount L (flags[i]?.getD false)) .P ++ (capWord u ++ x)) (ih (i + 1))

theorem assembleFlagged_eq (L : ℕ) (flags : List Bool) (us : List Sequence) :
    assembleFlagged (L, flagBodiesAt flags 0 us) =
      assembleReductionWord (fun j => gapCount L (flags[j]?.getD false)) us := by
  unfold assembleFlagged assembleReductionWord
  rw [flatMap_flagBodiesAt]

/-- Exact agreement with the frozen literal word and its corrected linker
convention. The only remaining assembly input is the finite parity zipper;
no assertion of its runtime is hidden in this semantic identity. -/
theorem assembleFlagged_prescribed (p : ConstructionParameters) (items bulkLengths : List ℕ) (flags : List Bool) :
    assembleFlagged (p.baseLinkerLength (p.reductionWireCount items bulkLengths),
      flagBodiesAt flags 0 (p.reductionUnitBodies items bulkLengths)) =
      p.prescribedReductionWord items bulkLengths flags := by
  rw [assembleFlagged_eq]
  rfl

end ProteinFolding.Tetrahedral.ReductionTM2

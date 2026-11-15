import ProteinFolding.Tetrahedral.ReductionTM2BulkPredicate
import ProteinFolding.Tetrahedral.ReductionTM2Walk
import ProteinFolding.Tetrahedral.ReductionTM2ListFlatMap
import ProteinFolding.Common.TM2UnaryRange

/-! The explicit canonical bulk serialization algorithm.
Scan the whole fixed grid in increasing index order. From each degree-one
vertex, follow the actual bulk graph for the grid bound. Emit the component
length and its two endpoint colours exactly when the start index is smaller
than the final endpoint. The proof that this covers each component once is
separate from this unconditional finite-machine runtime construction. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

open Computability Turing TM2CompositionPoly TM2ProductMap

abbrev Input := ℕ × ℕ
abbrev Record := ℕ × (Bool × Bool)
def inputEncoding := Division.inputEncoding
def recordEncoding : FinEncoding Record := pairEncoding unaryFinEncodingNat
  (pairEncoding finEncodingBoolBool finEncodingBoolBool)
def recordsEncoding := TM2ListMap.listEncoding recordEncoding

def startState (x : Input) : BoundedWalk.State ℕ := BoundedWalk.initial x.1 (Grid.count x.1) x.2

noncomputable def walk (x : Input) : BoundedWalk.State ℕ :=
  (BoundedWalk.step BulkPredicate.predicate)^[Grid.count x.1] (startState x)

noncomputable def record (x : Input) : Record :=
  ((walk x).2.2.1, (BulkPredicate.colour (x.1, (x.2, 0)),
    BulkPredicate.colour (x.1, ((walk x).2.1.2, 0))))

noncomputable def canonical (x : Input) : Bool :=
  BulkPredicate.endpoint (x.1, (x.2, 0)) && decide (x.2 < (walk x).2.1.2)

noncomputable def emit (x : Input) : List Record := if canonical x then [record x] else []

noncomputable def records (m : ℕ) : List Record := (List.range (Grid.count m)).flatMap (fun i => emit (m, i))

noncomputable def mComputable : TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => x.1) :=
  TM2PairProjections.fstComputable unaryFinEncodingNat unaryFinEncodingNat
noncomputable def startComputable : TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => x.2) :=
  TM2PairProjections.sndComputable unaryFinEncodingNat unaryFinEncodingNat
noncomputable def boundComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => Grid.count x.1) :=
  compose (g := Grid.count) mComputable Grid.countComputable

set_option maxHeartbeats 1200000 in
noncomputable def startStateComputable :
    TM2ComputableInPolyTime inputEncoding (BoundedWalk.stateEncoding unaryFinEncodingNat) startState :=
  pairComputable (pairComputable mComputable boundComputable)
    (pairComputable (pairComputable boundComputable startComputable)
      (pairComputable (natConstant _ 1) (TM2Constants.constantComputable _ finEncodingBoolBool false)))

set_option maxHeartbeats 1200000 in
noncomputable def walkComputable :
    TM2ComputableInPolyTime inputEncoding (BoundedWalk.stateEncoding unaryFinEncodingNat) walk :=
  compose (pairComputable startStateComputable boundComputable)
    (BoundedWalk.computable unaryFinEncodingNat BulkPredicate.computable)

noncomputable def lengthComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => (walk x).2.2.1) := by
  let h := compose walkComputable (BoundedWalk.lengthComputable unaryFinEncodingNat)
  exact changeFunction h (fun x => rfl)

noncomputable def endComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => (walk x).2.1.2) := by
  let h := compose walkComputable (BoundedWalk.currentComputable unaryFinEncodingNat)
  exact changeFunction h (fun x => rfl)

noncomputable def startQueryComputable :
    TM2ComputableInPolyTime inputEncoding BulkPredicate.inputEncoding (fun x : Input => (x.1, (x.2, 0))) :=
  pairComputable mComputable (pairComputable startComputable (natConstant _ 0))

noncomputable def endQueryComputable :
    TM2ComputableInPolyTime inputEncoding BulkPredicate.inputEncoding
      (fun x : Input => (x.1, ((walk x).2.1.2, 0))) :=
  pairComputable mComputable (pairComputable endComputable (natConstant _ 0))

set_option maxHeartbeats 1200000 in
noncomputable def recordComputable : TM2ComputableInPolyTime inputEncoding recordEncoding record :=
  pairComputable lengthComputable (pairComputable
    (compose startQueryComputable BulkPredicate.colourComputable)
    (compose endQueryComputable BulkPredicate.colourComputable))

set_option maxHeartbeats 1200000 in
noncomputable def canonicalComputable : TM2ComputableInPolyTime inputEncoding finEncodingBoolBool canonical :=
  compose (pairComputable (compose startQueryComputable BulkPredicate.endpointComputable)
    (compose (pairComputable startComputable endComputable) TM2UnaryComparison.ltComputable))
      TM2Boolean.andComputable

set_option maxHeartbeats 1200000 in
noncomputable def emitComputable : TM2ComputableInPolyTime inputEncoding recordsEncoding emit :=
  TM2Conditional.iteComputable canonicalComputable
    (compose recordComputable (singletonComputable recordEncoding))
    (TM2Constants.constantComputable _ recordsEncoding [])

set_option maxHeartbeats 1200000 in
noncomputable def recordsComputable : TM2ComputableInPolyTime unaryFinEncodingNat recordsEncoding records := by
  let h := compose (pairComputable (idComputableInPolyTime unaryFinEncodingNat)
    (compose Grid.countComputable TM2UnaryRange.rangeComputable))
      (listFlatMapComputable recordEncoding emitComputable)
  exact changeFunction h (fun m => rfl)

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

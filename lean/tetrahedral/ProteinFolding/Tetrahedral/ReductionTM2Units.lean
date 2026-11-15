import ProteinFolding.Tetrahedral.ReductionTM2Lists
import ProteinFolding.Tetrahedral.ReductionWord

namespace ProteinFolding.Tetrahedral.ReductionTM2

open Computability Turing TM2CompositionPoly TM2ProductMap

abbrev PreparedInput := Parameters × (List ℕ × List ℕ)
def naturalListEncoding := TM2ListMap.listEncoding unaryFinEncodingNat
def bodyListEncoding := TM2ListMap.listEncoding sequenceEncoding
def preparedEncoding : FinEncoding PreparedInput :=
  pairEncoding parameterEncoding (pairEncoding naturalListEncoding naturalListEncoding)

def unitBodies (x : PreparedInput) : List Sequence :=
  [[.H], [.H], [.H], Raw.frameBody x.1] ++ Raw.separatorBodies x.1 ++
    [dimerChain (Raw.leftFiller x.1)] ++ x.2.1.map (Raw.itemBody x.1) ++
    [dimerChain (Raw.rightFiller x.1)] ++ List.replicate 3 (Raw.ringBody x.1) ++
    x.2.2.map (fun n => List.replicate n .H)

@[simp] theorem unitBodies_parameters (p : ConstructionParameters) (items bulkLengths : List ℕ) :
    unitBodies ((p.bins, p.capacity), (items, bulkLengths)) = p.reductionUnitBodies items bulkLengths := rfl

noncomputable def preparedParametersComputable : TM2ComputableInPolyTime preparedEncoding parameterEncoding Prod.fst :=
  TM2PairProjections.fstComputable _ _
noncomputable def preparedListsComputable :
    TM2ComputableInPolyTime preparedEncoding (pairEncoding naturalListEncoding naturalListEncoding) Prod.snd :=
  TM2PairProjections.sndComputable _ _
noncomputable def preparedItemsComputable : TM2ComputableInPolyTime preparedEncoding naturalListEncoding (fun p : PreparedInput => p.2.1) :=
  compose preparedListsComputable (TM2PairProjections.fstComputable _ _)
noncomputable def preparedBulkComputable : TM2ComputableInPolyTime preparedEncoding naturalListEncoding (fun p : PreparedInput => p.2.2) :=
  compose preparedListsComputable (TM2PairProjections.sndComputable _ _)

noncomputable def unitBodiesComputable : TM2ComputableInPolyTime preparedEncoding bodyListEncoding unitBodies := by
  let terminal := TM2Constants.constantComputable preparedEncoding bodyListEncoding [[.H], [.H], [.H]]
  let frame := compose (g := fun w : Sequence => [w])
    (compose (g := Raw.frameBody) preparedParametersComputable frameBodyComputable) (singletonComputable sequenceEncoding)
  let separators := compose (g := Raw.separatorBodies) preparedParametersComputable separatorBodiesComputable
  let left := compose (g := fun w : Sequence => [w])
    (compose (g := fun p => dimerChain (Raw.leftFiller p)) preparedParametersComputable leftFillerBodyComputable) (singletonComputable sequenceEncoding)
  let items := compose (pairComputable preparedParametersComputable preparedItemsComputable) itemBodiesComputable
  let right := compose (g := fun w : Sequence => [w])
    (compose (g := fun p => dimerChain (Raw.rightFiller p)) preparedParametersComputable rightFillerBodyComputable) (singletonComputable sequenceEncoding)
  let ring := compose (g := fun w : Sequence => [w])
    (compose (g := Raw.ringBody) preparedParametersComputable ringBodyComputable) (singletonComputable sequenceEncoding)
  let rings := listConcat (listConcat ring ring) ring
  let bulk := compose (pairComputable preparedParametersComputable preparedBulkComputable)
    (TM2ListMap.mapComputable sequenceEncoding (compose (g := fun n => List.replicate n Residue.H) indexComputable (residuePower .H)))
  let h := listConcat (listConcat (listConcat (listConcat (listConcat (listConcat
    (listConcat terminal frame) separators) left) items) right) rings) bulk
  exact changeFunction h (fun x => by simp only [Function.comp_def, id_eq, unitBodies, List.append_assoc,
    List.cons_append, List.nil_append, List.replicate_succ, List.replicate_zero])

abbrev SourceBulkInput := Packing.Instance × List ℕ
def sourceBulkEncoding : FinEncoding SourceBulkInput := pairEncoding Packing.instanceEncoding naturalListEncoding

noncomputable def sourceBulkPreparedComputable :
    TM2ComputableInPolyTime sourceBulkEncoding preparedEncoding
      (fun x : SourceBulkInput => ((x.1.bins, x.1.capacity), (x.1.sizes, x.2))) :=
  let hsource := TM2PairProjections.fstComputable Packing.instanceEncoding naturalListEncoding
  pairComputable (compose hsource sourceParametersComputable)
    (pairComputable (compose hsource sourceItemsComputable) (TM2PairProjections.sndComputable _ _))

/-- Actual polynomial-time generation of the entire literal unit-body list
from the encoded packing source and a prepared bulk-length list. Bulk list
generation and the parity-aware linker assembly remain separate stages. -/
noncomputable def sourceBulkUnitsComputable :
    TM2ComputableInPolyTime sourceBulkEncoding bodyListEncoding
      (fun x : SourceBulkInput => unitBodies ((x.1.bins, x.1.capacity), (x.1.sizes, x.2))) :=
  compose (g := unitBodies) sourceBulkPreparedComputable unitBodiesComputable

end ProteinFolding.Tetrahedral.ReductionTM2

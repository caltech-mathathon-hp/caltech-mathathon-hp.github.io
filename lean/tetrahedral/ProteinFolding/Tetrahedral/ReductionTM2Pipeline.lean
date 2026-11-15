import ProteinFolding.Tetrahedral.ReductionTM2BulkOutput
import ProteinFolding.Tetrahedral.ReductionTM2ColourFlags
import ProteinFolding.Tetrahedral.ReductionTM2Guard

/-! Complete actual HP output generation from the source and its nonbulk
endpoint-colour list. Bulk lengths, bulk colours and all incoming parity bits
are computed internally. Only the short geometric prefix-colour specification
remains an explicit input to this stage. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Pipeline

open Computability Turing TM2CompositionPoly TM2ProductMap

abbrev Input := Packing.Instance × List ColourFlags.Colours
def inputEncoding := pairEncoding Packing.instanceEncoding (TM2ListMap.listEncoding ColourFlags.coloursEncoding)

noncomputable def sourceComputable :
    TM2ComputableInPolyTime inputEncoding Packing.instanceEncoding (fun x : Input => x.1) :=
  TM2PairProjections.fstComputable Packing.instanceEncoding (TM2ListMap.listEncoding ColourFlags.coloursEncoding)

noncomputable def prefixComputable :
    TM2ComputableInPolyTime inputEncoding (TM2ListMap.listEncoding ColourFlags.coloursEncoding) (fun x : Input => x.2) :=
  TM2PairProjections.sndComputable Packing.instanceEncoding (TM2ListMap.listEncoding ColourFlags.coloursEncoding)

noncomputable def sideComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : Input => Raw.side (x.1.bins, x.1.capacity)) :=
  compose (g := fun I : Packing.Instance => Raw.side (I.bins, I.capacity)) sourceComputable BulkScan.sourceSideComputable

noncomputable def lengthsComputable :
    TM2ComputableInPolyTime inputEncoding naturalListEncoding
      (fun x : Input => BulkScan.lengths (Raw.side (x.1.bins, x.1.capacity))) :=
  compose (g := BulkScan.lengths) sideComputable BulkScan.lengthsComputable

noncomputable def bulkColoursComputable :
    TM2ComputableInPolyTime inputEncoding (TM2ListMap.listEncoding ColourFlags.coloursEncoding)
      (fun x : Input => BulkScan.colours (Raw.side (x.1.bins, x.1.capacity))) :=
  compose (g := BulkScan.colours) sideComputable BulkScan.coloursComputable

noncomputable def allColoursComputable :
    TM2ComputableInPolyTime inputEncoding (TM2ListMap.listEncoding ColourFlags.coloursEncoding)
      (fun x : Input => x.2 ++ BulkScan.colours (Raw.side (x.1.bins, x.1.capacity))) :=
  listConcat prefixComputable bulkColoursComputable

set_option maxHeartbeats 1200000 in
noncomputable def flagsComputable :
    TM2ComputableInPolyTime inputEncoding (wordEncoding Bool)
      (fun x : Input => ColourFlags.flags (false, x.2 ++ BulkScan.colours (Raw.side (x.1.bins, x.1.capacity)))) :=
  compose (g := ColourFlags.flags) (pairComputable (TM2Constants.constantComputable _ finEncodingBoolBool false) allColoursComputable)
    ColourFlags.computable

noncomputable def preparedData (x : Input) : WordInput :=
  ((x.1, BulkScan.lengths (Raw.side (x.1.bins, x.1.capacity))),
    ColourFlags.flags (false, x.2 ++ BulkScan.colours (Raw.side (x.1.bins, x.1.capacity))))

set_option maxHeartbeats 1200000 in
noncomputable def preparedDataComputable : TM2ComputableInPolyTime inputEncoding wordInputEncoding preparedData :=
  pairComputable (pairComputable sourceComputable lengthsComputable) flagsComputable

noncomputable def output (x : Input) : HPInstance := guardedPreparedInstance (preparedData x)

set_option maxHeartbeats 1200000 in
noncomputable def computable : TM2ComputableInPolyTime inputEncoding hpEncoding output :=
  compose (g := guardedPreparedInstance) preparedDataComputable guardedPreparedInstanceComputable

theorem rejects_invalid (x : Input) (h : Guard.sourceGuard x.1 = false) : ¬ (output x).Accepts :=
  guardedPreparedInstance_rejects (preparedData x) h

end ProteinFolding.Tetrahedral.ReductionTM2.Pipeline

import ProteinFolding.Tetrahedral.ReductionTM2BulkScan
import ProteinFolding.Tetrahedral.ReductionTM2Units

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

open Computability Turing TM2CompositionPoly TM2ProductMap

def coloursEncoding := pairEncoding finEncodingBoolBool finEncodingBoolBool

noncomputable def lengths (m : ℕ) : List ℕ := (records m).map Prod.fst
noncomputable def colours (m : ℕ) : List (Bool × Bool) := (records m).map Prod.snd

noncomputable def recordLengthComputable :
    TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat recordEncoding) unaryFinEncodingNat
      (fun x : ℕ × Record => x.2.1) :=
  compose (TM2PairProjections.sndComputable unaryFinEncodingNat recordEncoding)
    (TM2PairProjections.fstComputable unaryFinEncodingNat coloursEncoding)

noncomputable def recordColoursComputable :
    TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat recordEncoding) coloursEncoding
      (fun x : ℕ × Record => x.2.2) :=
  compose (TM2PairProjections.sndComputable unaryFinEncodingNat recordEncoding)
    (TM2PairProjections.sndComputable unaryFinEncodingNat coloursEncoding)

set_option maxHeartbeats 1200000 in
noncomputable def lengthsComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat naturalListEncoding lengths := by
  let h := compose (pairComputable (idComputableInPolyTime unaryFinEncodingNat) recordsComputable)
    (TM2ListMap.mapComputable unaryFinEncodingNat recordLengthComputable)
  exact changeFunction h (fun m => rfl)

set_option maxHeartbeats 1200000 in
noncomputable def coloursComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat (TM2ListMap.listEncoding coloursEncoding) colours := by
  let h := compose (pairComputable (idComputableInPolyTime unaryFinEncodingNat) recordsComputable)
    (TM2ListMap.mapComputable coloursEncoding recordColoursComputable)
  exact changeFunction h (fun m => rfl)

noncomputable def sourceSideComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding unaryFinEncodingNat
      (fun I : Packing.Instance => Raw.side (I.bins, I.capacity)) :=
  compose (g := Raw.side) sourceParametersComputable sideComputable

noncomputable def sourceData (I : Packing.Instance) : SourceBulkInput :=
  (I, lengths (Raw.side (I.bins, I.capacity)))

set_option maxHeartbeats 1200000 in
noncomputable def sourceDataComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding sourceBulkEncoding sourceData := by
  let h := pairComputable (idComputableInPolyTime Packing.instanceEncoding)
    (compose sourceSideComputable lengthsComputable)
  exact changeFunction h (fun I => rfl)

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

import ProteinFolding.Tetrahedral.ReductionTM2Prepared
import ProteinFolding.Tetrahedral.ReductionTM2Threshold
import ProteinFolding.Tetrahedral.Encodings

/-! The full encoded HP output, including the exact signed-binary threshold.
The remaining reduction stage is generation of its canonical bulk/parity data. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2

open Computability Turing TM2CompositionPoly TM2ProductMap

def preparedInstance (x : WordInput) : HPInstance :=
  ⟨preparedWord x, Raw.threshold (Raw.side (x.1.1.bins, x.1.1.capacity))⟩

noncomputable def wordSourceComputable :
    TM2ComputableInPolyTime wordInputEncoding Packing.instanceEncoding (fun x : WordInput => x.1.1) :=
  compose (TM2PairProjections.fstComputable sourceBulkEncoding (wordEncoding Bool))
    (TM2PairProjections.fstComputable Packing.instanceEncoding naturalListEncoding)

set_option maxHeartbeats 1200000 in
noncomputable def wordThresholdComputable :
    TM2ComputableInPolyTime wordInputEncoding signedEncoding
      (fun x : WordInput => Raw.threshold (Raw.side (x.1.1.bins, x.1.1.capacity))) :=
  compose (compose wordSourceComputable sourceParametersComputable) sideThresholdComputable

set_option maxHeartbeats 1200000 in
noncomputable def preparedInstanceComputable :
    TM2ComputableInPolyTime wordInputEncoding hpEncoding preparedInstance := by
  let h := pairComputable preparedWordComputable wordThresholdComputable
  exact {
    toTM2ComputableAux := h.toTM2ComputableAux
    time := h.time
    outputsFun := h.outputsFun }

theorem preparedInstance_sequence (I : PackingSource.Instance) (hw : Packing.WellFormed I)
    (bulkLengths : List ℕ) (flags : List Bool) :
    (preparedInstance ((I, bulkLengths), flags)).sequence =
      (PackingSource.parameters I hw).prescribedReductionWord I.sizes bulkLengths flags :=
  preparedWord_eq_prescribed I hw bulkLengths flags

theorem preparedInstance_threshold (I : PackingSource.Instance) (hw : Packing.WellFormed I)
    (bulkLengths : List ℕ) (flags : List Bool) :
    (preparedInstance ((I, bulkLengths), flags)).minBonds =
      2 * (octahedralNumber (PackingSource.parameters I hw).side : ℤ) -
        2 * ((PackingSource.parameters I hw).side ^ 2 : ℕ) := rfl

end ProteinFolding.Tetrahedral.ReductionTM2

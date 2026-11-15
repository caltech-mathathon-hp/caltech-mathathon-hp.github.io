import ProteinFolding.Cubic.Encodings
import ProteinFolding.Cubic.Proofs.VerifierRecordDecoder
import ProteinFolding.Common.TM2ProductMap
import ProteinFolding.Common.TM2WordEquality
import ProteinFolding.Common.TM2Boolean
import ProteinFolding.Common.TM2ArithmeticSignedUnary

/-! Closed polynomial-time components of the cubic HP certificate verifier:
input field projections, decoding the redundant labels, and checking that
those labels agree with the original sequence. -/

namespace ProteinFolding.CubicHPVerifier

open Computability Turing CubicVerifier CubicRecordDecoder

abbrev Input := HPInstance × List Bool
def inputEncoding : FinEncoding Input := pairEncoding hpEncoding (wordEncoding Bool)

noncomputable def sequenceComputable :
    TM2ComputableInPolyTime hpEncoding sequenceEncoding HPInstance.sequence := by
  let h := TM2PairProjections.fstComputable sequenceEncoding signedEncoding
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => h.outputsFun (I.sequence, I.minBonds) }

noncomputable def minBondsComputable :
    TM2ComputableInPolyTime hpEncoding signedEncoding HPInstance.minBonds := by
  let h := TM2PairProjections.sndComputable sequenceEncoding signedEncoding
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun I => h.outputsFun (I.sequence, I.minBonds) }

def decodedLabels (w : List Bool) : Sequence :=
  (stream w).filterMap (fun r => r.map Prod.fst)

noncomputable def decodedLabelsComputable :
    TM2ComputableInPolyTime (wordEncoding Bool) sequenceEncoding decodedLabels :=
  TM2CompositionPoly.compose decoderComputable
    (TM2PairProjections.filterMapComputable (Option Record) Residue (fun r => r.map Prod.fst))

noncomputable def instanceComputable :
    TM2ComputableInPolyTime inputEncoding hpEncoding Prod.fst :=
  TM2PairProjections.fstComputable hpEncoding (wordEncoding Bool)

noncomputable def certificateComputable :
    TM2ComputableInPolyTime inputEncoding (wordEncoding Bool) Prod.snd :=
  TM2PairProjections.sndComputable hpEncoding (wordEncoding Bool)

noncomputable def inputSequenceComputable :
    TM2ComputableInPolyTime inputEncoding sequenceEncoding (fun x : Input => x.1.sequence) :=
  TM2CompositionPoly.compose instanceComputable sequenceComputable

noncomputable def inputMinBondsComputable :
    TM2ComputableInPolyTime inputEncoding signedEncoding (fun x : Input => x.1.minBonds) :=
  TM2CompositionPoly.compose instanceComputable minBondsComputable

noncomputable def inputDecodedLabelsComputable :
    TM2ComputableInPolyTime inputEncoding sequenceEncoding (fun x : Input => decodedLabels x.2) :=
  TM2CompositionPoly.compose (f := fun x : Input => x.2) (g := decodedLabels)
    certificateComputable decodedLabelsComputable

def labelCheck (x : Input) : Bool := decide (x.1.sequence = decodedLabels x.2)

noncomputable def labelCheckComputable :
    TM2ComputableInPolyTime inputEncoding finEncodingBoolBool labelCheck :=
  TM2CompositionPoly.compose
    (TM2ProductMap.pairComputable inputSequenceComputable inputDecodedLabelsComputable)
    (TM2WordEquality.wordEqualityComputable Residue)

theorem labelCheck_correct (x : Input) :
    labelCheck x = true ↔ x.1.sequence = decodedLabels x.2 := by simp [labelCheck]

theorem decodedLabels_encodeRecords (rs : List Record) :
    decodedLabels (encodeRecords rs) = rs.map Prod.fst := by
  simp [decodedLabels, stream_encodeRecords, List.filterMap_map, Function.comp_def]

theorem recordsAccept_labels (I : HPInstance) (rs : List Record) (h : RecordsAccept (I, rs)) :
    rs.map Prod.fst = I.sequence := by
  have hv : ValidRecords I.sequence rs := by
    by_contra hn
    simp [RecordsAccept, recordFold, hn] at h
  exact hv.1

theorem labelCheck_encodeRecords (I : HPInstance) (rs : List Record)
    (h : RecordsAccept (I, rs)) : labelCheck (I, encodeRecords rs) = true := by
  rw [labelCheck_correct, decodedLabels_encodeRecords]
  exact (recordsAccept_labels I rs h).symm

end ProteinFolding.CubicHPVerifier

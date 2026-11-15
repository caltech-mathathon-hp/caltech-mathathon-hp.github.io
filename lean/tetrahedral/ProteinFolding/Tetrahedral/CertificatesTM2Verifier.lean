import ProteinFolding.Tetrahedral.CertificatesTM2PairComputable
import ProteinFolding.Tetrahedral.CertificatesTM2ZipSemantics
import ProteinFolding.Common.TM2ProductMap
import ProteinFolding.Common.TM2Boolean
import ProteinFolding.Common.TM2ArithmeticSignedUnary

/-! Actual polynomial-time assembly on the frozen HP/direction input. The
machine compares the signed binary threshold directly with a unary bond
count; it never expands the binary threshold into unary. -/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Verifier

open Computability Turing

abbrev Input := HPInstance × DirectionWord

def inputEncoding : FinEncoding Input := pairEncoding hpEncoding directionEncoding

noncomputable def sequenceComputable :
    TM2ComputableInPolyTime hpEncoding sequenceEncoding HPInstance.sequence := by
  let h := TM2PairProjections.fstComputable sequenceEncoding signedEncoding
  exact { toTM2ComputableAux := h.toTM2ComputableAux
          time := h.time
          outputsFun := fun I => h.outputsFun (I.sequence, I.minBonds) }

noncomputable def minBondsComputable :
    TM2ComputableInPolyTime hpEncoding signedEncoding HPInstance.minBonds := by
  let h := TM2PairProjections.sndComputable sequenceEncoding signedEncoding
  exact { toTM2ComputableAux := h.toTM2ComputableAux
          time := h.time
          outputsFun := fun I => h.outputsFun (I.sequence, I.minBonds) }

noncomputable def instanceComputable :
    TM2ComputableInPolyTime inputEncoding hpEncoding Prod.fst :=
  TM2PairProjections.fstComputable hpEncoding directionEncoding

noncomputable def certificateComputable :
    TM2ComputableInPolyTime inputEncoding directionEncoding Prod.snd :=
  TM2PairProjections.sndComputable hpEncoding directionEncoding

noncomputable def inputSequenceComputable :
    TM2ComputableInPolyTime inputEncoding sequenceEncoding (fun x : Input => x.1.sequence) :=
  TM2CompositionPoly.compose instanceComputable sequenceComputable

noncomputable def inputMinBondsComputable :
    TM2ComputableInPolyTime inputEncoding signedEncoding (fun x : Input => x.1.minBonds) :=
  TM2CompositionPoly.compose instanceComputable minBondsComputable

def records (x : Input) : List CertificatesTM2Zip.Letter :=
  CertificatesTM2Zip.zipRecords 0 x.1.sequence x.2

noncomputable def recordsComputable :
    TM2ComputableInPolyTime inputEncoding (wordEncoding CertificatesTM2Zip.Letter) records :=
  TM2CompositionPoly.compose
    (TM2ProductMap.pairComputable inputSequenceComputable certificateComputable)
    CertificatesTM2Zip.zipComputable

def verify (x : Input) : Bool :=
  CertificatesTM2Pairs.geometryValid (records x) &&
    decide (x.1.minBonds ≤ (CertificatesTM2Pairs.bondCountRecords (records x) : ℤ))

noncomputable def verifyComputable :
    TM2ComputableInPolyTime inputEncoding finEncodingBoolBool verify := by
  let hgeo := TM2CompositionPoly.compose recordsComputable
    CertificatesTM2Pairs.GeometryMachine.geometryComputable
  let hvalid := TM2CompositionPoly.compose hgeo
    (TM2PairProjections.fstComputable finEncodingBoolBool unaryFinEncodingNat)
  let hscore := TM2CompositionPoly.compose hgeo
    (TM2PairProjections.sndComputable finEncodingBoolBool unaryFinEncodingNat)
  let hthreshold := TM2CompositionPoly.compose
    (TM2ProductMap.pairComputable inputMinBondsComputable hscore)
    TM2Arithmetic.Comparator.signedUnaryComputable
  exact TM2CompositionPoly.compose (TM2ProductMap.pairComputable hvalid hthreshold)
    TM2Boolean.andComputable

theorem verifier_polyTimeDecidable :
    PolyTimeDecidable inputEncoding (fun x => verify x = true) :=
  ⟨verify, ⟨verifyComputable⟩, fun _ => Iff.rfl⟩

end ProteinFolding.Tetrahedral.CertificatesTM2Verifier

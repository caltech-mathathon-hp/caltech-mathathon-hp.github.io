import ProteinFolding.Cubic.Proofs.ThresholdCertificateUnarySide
import ProteinFolding.Cubic.Proofs.VerifierPerfectPred
import ProteinFolding.Cubic.Proofs.VerifierPerfectEquality
import ProteinFolding.Common.TM2ProductMap
import ProteinFolding.Common.TM2Constants

/-! Actual polynomial-time unary arithmetic for the perfect verifier. The
unary argument is an explicit portion of the candidate certificate, so its
square and cube have polynomial output size in the verifier's total input. -/

namespace ProteinFolding.PerfectVerifierArithmetic

open Computability Turing TM2CompositionPoly TM2ProductMap
open PerfectUnaryMultiplication PerfectUnaryPredecessor PerfectUnaryEquality CubicCertificates

noncomputable def unaryCubeComputable : TM2ComputableInPolyTime
    unaryFinEncodingNat unaryFinEncodingNat (fun n : ℕ => n ^ 3) := by
  let h := compose (pairComputable unarySquareComputable (idComputableInPolyTime unaryFinEncodingNat))
    unaryMulComputable
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun n => by
        simpa only [Function.comp_apply, pow_succ, pow_zero, Nat.one_mul] using h.outputsFun n }

noncomputable def unaryThresholdComputable : TM2ComputableInPolyTime
    unaryFinEncodingNat unaryFinEncodingNat (fun n : ℕ => 3 * n ^ 2 * (n - 1)) := by
  let core := compose (pairComputable unarySquareComputable predecessorComputable) unaryMulComputable
  let three := TM2Constants.constantComputable unaryFinEncodingNat unaryFinEncodingNat 3
  let h := compose (pairComputable three core) unaryMulComputable
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun n => by
        simpa only [Function.comp_apply, Nat.mul_assoc] using h.outputsFun n }

noncomputable def unaryAddComputable : TM2ComputableInPolyTime
    (pairEncoding unaryFinEncodingNat unaryFinEncodingNat) unaryFinEncodingNat
      (fun p : ℕ × ℕ => p.1 + p.2) := by
  let h := TM2PairProjections.concatComputable Bool
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun p => by
        have hout := h.outputsFun (unaryEncodeNat p.1, unaryEncodeNat p.2)
        simpa only [wordEncoding, pairEncoding, unaryFinEncodingNat, ← unary_append] using hout }

/-- Compare the cube of the explicit unary side witness to the H counter. -/
noncomputable def cubeCountComputable : TM2ComputableInPolyTime
    (pairEncoding unaryFinEncodingNat unaryFinEncodingNat) finEncodingBoolBool
      (fun p : ℕ × ℕ => decide (p.1 ^ 3 = p.2)) :=
  compose (productMapComputable unaryCubeComputable (idComputableInPolyTime unaryFinEncodingNat))
    unaryEqualityComputable

/-- Exact score equality is sufficient for perfect packing once the H counter
equals the cube volume, by the already proved geometric theorem. -/
noncomputable def thresholdScoreComputable : TM2ComputableInPolyTime
    (pairEncoding unaryFinEncodingNat unaryFinEncodingNat) finEncodingBoolBool
      (fun p : ℕ × ℕ => decide (3 * p.1 ^ 2 * (p.1 - 1) = p.2)) :=
  compose (productMapComputable unaryThresholdComputable (idComputableInPolyTime unaryFinEncodingNat))
    unaryEqualityComputable

end ProteinFolding.PerfectVerifierArithmetic

import ProteinFolding.Cubic.Proofs.VerifierPerfectUnary
import ProteinFolding.Common.TM2WordEquality

/-! Exact unary-counter equality using the proved finite-word equality machine. -/

namespace ProteinFolding.PerfectUnaryEquality

open Computability Turing

theorem unaryEncodeNat_inj (a b : ℕ) : unaryEncodeNat a = unaryEncodeNat b ↔ a = b := by
  constructor
  · intro h
    exact unaryFinEncodingNat.toEncoding.encode_injective h
  · intro h
    exact congrArg unaryEncodeNat h

noncomputable def unaryEqualityComputable :
    TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)
      finEncodingBoolBool (fun ab : ℕ × ℕ => decide (ab.1 = ab.2)) := by
  let h := TM2WordEquality.wordEqualityComputable Bool
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun ab => by
        have hout := h.outputsFun (unaryEncodeNat ab.1, unaryEncodeNat ab.2)
        simpa only [wordEncoding, pairEncoding, unaryFinEncodingNat, unaryEncodeNat_inj] using hout }

theorem unaryEquality_polyTimeDecidable :
    PolyTimeDecidable (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)
      (fun ab : ℕ × ℕ => ab.1 = ab.2) :=
  ⟨fun ab => decide (ab.1 = ab.2), ⟨unaryEqualityComputable⟩, fun _ => by simp⟩

end ProteinFolding.PerfectUnaryEquality

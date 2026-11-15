import ProteinFolding.Common.TM2UnarySubtraction
import ProteinFolding.Common.TM2WordFold
import ProteinFolding.Common.TM2PairSwap
import ProteinFolding.Common.TM2Boolean

/-! Actual unary comparisons, obtained from finite-state nonemptiness and
the proved truncated-subtraction machine. All bounds use encoding lengths. -/

namespace ProteinFolding.TM2UnaryComparison

open Computability Turing TM2CompositionPoly

theorem unary_nonempty (n : ℕ) (seen : Bool) :
    (unaryEncodeNat n).foldl (fun _ _ => true) seen = (seen || decide (0 < n)) := by
  induction n generalizing seen with
  | zero => simp [unaryEncodeNat]
  | succ n ih => simp [unaryEncodeNat, ih]

noncomputable def positiveComputable : TM2ComputableInPolyTime unaryFinEncodingNat finEncodingBoolBool
    (fun n => decide (0 < n)) := by
  let h := TM2WordFold.computable Bool Bool (fun _ _ => true) id false
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun n => by
        simpa only [wordEncoding, unaryFinEncodingNat, unary_nonempty, Bool.false_or, id_eq] using
          h.outputsFun (unaryEncodeNat n) }

noncomputable def lessBoundComputable :
    TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat unaryFinEncodingNat) finEncodingBoolBool
      (fun p : ℕ × ℕ => decide (p.2 < p.1)) := by
  let h := compose TM2UnarySubtraction.subtractionComputable positiveComputable
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun p => by simpa only [Function.comp_def, Nat.sub_pos_iff_lt] using h.outputsFun p }

noncomputable def ltComputable :
    TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat unaryFinEncodingNat) finEncodingBoolBool
      (fun p : ℕ × ℕ => decide (p.1 < p.2)) :=
  compose (TM2PairSwap.swapComputable unaryFinEncodingNat unaryFinEncodingNat) lessBoundComputable

noncomputable def leComputable :
    TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat unaryFinEncodingNat) finEncodingBoolBool
      (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
  let h := compose lessBoundComputable TM2Boolean.notComputable
  have he : (fun p : ℕ × ℕ => !(decide (p.2 < p.1))) =
      (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
    funext p
    by_cases hp : p.2 < p.1 <;> simp_all
  change TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat unaryFinEncodingNat)
    finEncodingBoolBool (fun p : ℕ × ℕ => !(decide (p.2 < p.1))) at h
  rw [he] at h
  exact h

end ProteinFolding.TM2UnaryComparison

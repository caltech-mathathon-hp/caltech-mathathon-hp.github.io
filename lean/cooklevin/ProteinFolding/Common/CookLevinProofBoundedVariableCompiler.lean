import ProteinFolding.Common.CookLevinProofSourceQueryCompiler
import ProteinFolding.Common.TM2BoundedSearch
import ProteinFolding.Common.TM2UnaryToBinary

/-! Safe bounded conversion of a queried binary variable identifier to unary.
An actual bounded-search machine tests canonical binary codes and never
expands an identifier beyond the supplied unary bound. -/

namespace ProteinFolding.SAT.CookLevinBoundedVariableCompiler

open Computability Turing TM2CompositionPoly TM2ProductMap TM2BoundedSearch
open CookLevinSourceQueryCompiler

def variableTest (p : QueryInput × ℕ) : Bool := decide (variableCodeAt p.1 = encodeNat p.2)

def boundedVariable (p : QueryInput × ℕ) : ℕ := boundedSearch variableTest p

theorem encodeNat_eq_iff (a b : ℕ) : encodeNat a = encodeNat b ↔ a = b := by
  constructor
  · intro he
    have hd := congrArg decodeNat he
    simpa only [decode_encodeNat] using hd
  · exact congrArg encodeNat

theorem boundedVariable_le (p : QueryInput × ℕ) : boundedVariable p ≤ p.2 :=
  (boundedSearch_spec variableTest p.1 p.2).1

theorem boundedVariable_correct (φ : CNF) (i j V : ℕ) (hi : i < φ.length)
    (hj : j < φ[i].length) (hv : φ[i][j].var < V) :
    boundedVariable (((φ, i), j), V) = φ[i][j].var := by
  let v := φ[i][j].var
  let r := boundedVariable (((φ, i), j), V)
  have ht (n : ℕ) : variableTest (((φ, i), j), n) = decide (v = n) := by
    simp only [variableTest, variableCodeAt_correct φ i j hi hj, encodeNat_eq_iff]
    rfl
  have hs := boundedSearch_spec variableTest ((φ, i), j) V
  change r ≤ V ∧ (r < V → variableTest (((φ, i), j), r) = true) ∧
    ∀ n < r, variableTest (((φ, i), j), n) = false at hs
  change r = v
  by_cases hr : r < v
  · have hh := hs.2.1 (hr.trans hv)
    rw [ht, decide_eq_true_eq] at hh
    omega
  · by_cases hh : v < r
    · have hb := hs.2.2 v hh
      simp only [ht, decide_true] at hb
      contradiction
    · omega

noncomputable def unaryBinaryWordCompiler :
    TM2ComputableInPolyTime unaryFinEncodingNat (wordEncoding Bool) encodeNat :=
  compose (f := (id : ℕ → ℕ)) (g := encodeNat)
    TM2UnaryToBinary.unaryToBinaryComputable (TM2EncodingWords.encodeComputable finEncodingNatBool)

noncomputable def variableTestCompiler :
    TM2ComputableInPolyTime (pairEncoding queryEncoding unaryFinEncodingNat) finEncodingBoolBool variableTest :=
  compose (pairComputable
    (compose (TM2PairProjections.fstComputable queryEncoding unaryFinEncodingNat) variableCodeCompiler)
    (compose (TM2PairProjections.sndComputable queryEncoding unaryFinEncodingNat) unaryBinaryWordCompiler))
      (TM2WordEquality.wordEqualityComputable Bool)

noncomputable def boundedVariableCompiler :
    TM2ComputableInPolyTime (pairEncoding queryEncoding unaryFinEncodingNat) unaryFinEncodingNat boundedVariable :=
  boundedSearchComputable variableTestCompiler

end ProteinFolding.SAT.CookLevinBoundedVariableCompiler

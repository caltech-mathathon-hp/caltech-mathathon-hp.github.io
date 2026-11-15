import ProteinFolding.Tetrahedral.ReductionTM2Basics
import ProteinFolding.Common.TM2BoundedSearch
import ProteinFolding.Common.TM2Conditional
import ProteinFolding.Common.TM2UnaryComparison

/-! Actual unary quotient and remainder machines for deterministic grid
indexing. Division is a bounded least-index search implemented by a finite
TM2; zero divisors use the ordinary total natural-number convention. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Division

open Computability Turing TM2CompositionPoly TM2ProductMap

def inputEncoding : FinEncoding (ℕ × ℕ) := pairEncoding unaryFinEncodingNat unaryFinEncodingNat

def test (xq : (ℕ × ℕ) × ℕ) : Bool := decide (xq.1.1 < (xq.2 + 1) * xq.1.2)

def rawQuotient (x : ℕ × ℕ) : ℕ :=
  TM2BoundedSearch.boundedSearch test (x, x.1 + 1)

theorem rawQuotient_eq (x : ℕ × ℕ) (hb : 0 < x.2) : rawQuotient x = x.1 / x.2 := by
  have hs := TM2BoundedSearch.boundedSearch_spec test x (x.1 + 1)
  have ht : test (x, x.1 / x.2) = true := by
    simp only [test, decide_eq_true_eq]
    exact (Nat.div_lt_iff_lt_mul hb).1 (Nat.lt_succ_self _)
  have hle : rawQuotient x ≤ x.1 / x.2 := by
    by_contra h
    have hf := hs.2.2 (x.1 / x.2) (by change _ < rawQuotient x; omega)
    rw [ht] at hf
    contradiction
  have hge : x.1 / x.2 ≤ rawQuotient x := by
    by_cases hr : rawQuotient x < x.1 + 1
    · have hsuccess := hs.2.1 hr
      simp only [test, decide_eq_true_eq] at hsuccess
      have hq := (Nat.div_lt_iff_lt_mul hb).2 hsuccess
      change x.1 / x.2 < rawQuotient x + 1 at hq
      omega
    · have hn := Nat.div_le_self x.1 x.2
      omega
  omega

set_option maxHeartbeats 1200000 in
noncomputable def testComputable :
    TM2ComputableInPolyTime (pairEncoding inputEncoding unaryFinEncodingNat) finEncodingBoolBool test := by
  let hx := TM2PairProjections.fstComputable inputEncoding unaryFinEncodingNat
  let hq := TM2PairProjections.sndComputable inputEncoding unaryFinEncodingNat
  let hn := compose hx (TM2PairProjections.fstComputable unaryFinEncodingNat unaryFinEncodingNat)
  let hb := compose hx (TM2PairProjections.sndComputable unaryFinEncodingNat unaryFinEncodingNat)
  exact compose (pairComputable hn (mul (add hq (natConstant _ 1)) hb))
    TM2UnaryComparison.ltComputable

set_option maxHeartbeats 1200000 in
noncomputable def rawQuotientComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat rawQuotient :=
  compose (pairComputable (idComputableInPolyTime inputEncoding)
    (add (TM2PairProjections.fstComputable unaryFinEncodingNat unaryFinEncodingNat)
      (natConstant _ 1))) (TM2BoundedSearch.boundedSearchComputable testComputable)

set_option maxHeartbeats 1200000 in
noncomputable def quotientComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : ℕ × ℕ => x.1 / x.2) := by
  let hpos := compose (TM2PairProjections.sndComputable unaryFinEncodingNat unaryFinEncodingNat)
    TM2UnaryComparison.positiveComputable
  let h := TM2Conditional.iteComputable hpos rawQuotientComputable (natConstant _ 0)
  refine changeFunction h ?_
  intro x
  simp only [Function.comp_def, decide_eq_true_eq]
  split
  · exact rawQuotient_eq x (by assumption)
  · have hb : x.2 = 0 := by omega
    simp [hb]

set_option maxHeartbeats 1200000 in
noncomputable def remainderComputable :
    TM2ComputableInPolyTime inputEncoding unaryFinEncodingNat (fun x : ℕ × ℕ => x.1 % x.2) :=
  changeFunction (sub (TM2PairProjections.fstComputable unaryFinEncodingNat unaryFinEncodingNat)
    (mul (TM2PairProjections.sndComputable unaryFinEncodingNat unaryFinEncodingNat) quotientComputable))
      (fun x => Nat.mod_eq_sub_mul_div.symm)

end ProteinFolding.Tetrahedral.ReductionTM2.Division

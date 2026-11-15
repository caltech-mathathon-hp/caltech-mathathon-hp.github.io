import ProteinFolding.Tetrahedral.ReductionTM2Parameters
import ProteinFolding.Tetrahedral.ReductionTM2Third
import ProteinFolding.Common.TM2UnarySigned

/-! The exact octahedral contact threshold is computed by actual unary
arithmetic and then converted to the frozen signed-binary encoding. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2

open Computability Turing TM2CompositionPoly TM2ProductMap

namespace Raw

def octahedralCount (m : ℕ) : ℕ := m * (4 * (m * m) - 1) / 3
def thresholdNat (m : ℕ) : ℕ := 2 * octahedralCount m - 2 * (m * m)
def threshold (m : ℕ) : ℤ := 2 * (octahedralNumber m : ℤ) - 2 * (m ^ 2 : ℕ)

theorem octahedralCount_eq (m : ℕ) : octahedralCount m = octahedralNumber m := by
  simpa only [octahedralCount, pow_two] using (octahedralNumber_formula m).symm

theorem thresholdNat_cast (m : ℕ) : (thresholdNat m : ℤ) = threshold m := by
  have hN : m ^ 2 ≤ octahedralNumber m := by unfold octahedralNumber; omega
  unfold thresholdNat threshold
  rw [octahedralCount_eq, ← pow_two]
  rw [Nat.cast_sub (Nat.mul_le_mul_left 2 hN)]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

end Raw

noncomputable def octahedralCountComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat Raw.octahedralCount := by
  let hid := idComputableInPolyTime unaryFinEncodingNat
  exact compose (mul hid (sub (mul (natConstant _ 4) (mul hid hid)) (natConstant _ 1))) Third.computable

noncomputable def thresholdNatComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat unaryFinEncodingNat Raw.thresholdNat :=
  sub (mul (natConstant _ 2) octahedralCountComputable)
    (mul (natConstant _ 2) (mul (idComputableInPolyTime unaryFinEncodingNat) (idComputableInPolyTime unaryFinEncodingNat)))

noncomputable def thresholdComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat signedEncoding Raw.threshold :=
  changeFunction (compose thresholdNatComputable TM2UnarySigned.nonnegativeComputable) Raw.thresholdNat_cast

set_option maxHeartbeats 1200000 in
noncomputable def sideThresholdComputable :
    TM2ComputableInPolyTime parameterEncoding signedEncoding (fun p => Raw.threshold (Raw.side p)) :=
  compose sideComputable thresholdComputable

end ProteinFolding.Tetrahedral.ReductionTM2

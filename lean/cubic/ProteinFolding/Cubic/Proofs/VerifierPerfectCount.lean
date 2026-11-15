import ProteinFolding.Cubic.Proofs.ThresholdCertificate
import ProteinFolding.Common.TM2PairProjections
import Mathlib.Algebra.BigOperators.Fin

/-! An actual linear-time machine for extracting the number of H residues.
The output counter is unary and has at most one symbol per input residue;
no binary side length is expanded by this stage. -/

namespace ProteinFolding.CubicCertificates

open Computability Turing
open scoped BigOperators

theorem hydrophobicCount_eq_sum (S : Sequence) :
    hydrophobicCount S = ∑ i : Fin S.length, if S.get i = Residue.H then 1 else 0 := by
  simp only [hydrophobicCount, hydrophobicIndices, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem hydrophobicCount_cons (r : Residue) (S : Sequence) :
    hydrophobicCount (r :: S) = (if r = Residue.H then 1 else 0) + hydrophobicCount S := by
  rw [hydrophobicCount_eq_sum, hydrophobicCount_eq_sum]
  change (∑ i : Fin (S.length + 1), if (r :: S).get i = Residue.H then 1 else 0) = _
  rw [Fin.sum_univ_succ]
  rfl

def retainH : Residue → Option Bool
  | .H => some true
  | .P => none

theorem retainH_word (S : Sequence) :
    S.filterMap retainH = unaryEncodeNat (hydrophobicCount S) := by
  induction S with
  | nil => simp [hydrophobicCount, hydrophobicIndices, unaryEncodeNat]
  | cons r S ih =>
    rw [hydrophobicCount_cons]
    cases r with
    | H =>
      change true :: S.filterMap retainH = unaryEncodeNat (1 + hydrophobicCount S)
      rw [ih, Nat.add_comm 1 (hydrophobicCount S)]
      rfl
    | P =>
      change S.filterMap retainH = unaryEncodeNat (0 + hydrophobicCount S)
      simpa using ih

/-- The machine scans/filter-maps the residue word and restores order through
its buffer. Its polynomial time is exactly `2*X+3`. -/
noncomputable def hydrophobicCountComputable :
    TM2ComputableInPolyTime sequenceEncoding unaryFinEncodingNat hydrophobicCount := by
  let h := TM2PairProjections.filterMapComputable Residue Bool retainH
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun S => by
        have hout := h.outputsFun S
        simpa only [wordEncoding, sequenceEncoding, unaryFinEncodingNat, retainH_word] using hout }

theorem hydrophobicCountComputable_time :
    hydrophobicCountComputable.time = Polynomial.C 2 * Polynomial.X + Polynomial.C 3 := rfl

end ProteinFolding.CubicCertificates

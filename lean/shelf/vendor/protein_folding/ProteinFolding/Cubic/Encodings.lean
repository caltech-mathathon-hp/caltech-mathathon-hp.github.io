import ProteinFolding.Common.Encodings
import ProteinFolding.Cubic.Statement

/-! Encodings for the cubic-lattice inputs of Berger--Leighton. -/

namespace ProteinFolding

open Computability

/-- Section 2's HP STRING-FOLD instance with the graph fixed to Z³.
Format: tagged residues, separator, sign bit, binary magnitude of m.
Length = |S| + 2 + bitlength(|m|); no padding and no unary integer field. -/
def hpEncoding : FinEncoding HPInstance :=
  let e := pairEncoding sequenceEncoding signedEncoding
  { Γ := e.Γ
    ΓFin := e.ΓFin
    encode := fun I => e.encode (I.sequence, I.minBonds)
    decode := fun w => (e.decode w).map (fun sm => ⟨sm.1, sm.2⟩)
    decode_encode := by
      intro I
      rw [e.decode_encode]
      cases I
      rfl }

/-- Raw inputs avoid the proof field of `PerfectInstance`. Wrong H counts are
no-instances, via the already defined `PerfectHPStringFold`. -/
abbrev PerfectInput := Sequence × ℕ

/-- Section 2's perfect-fold input: tagged residues, separator, binary n.
Length = |S| + 1 + bitlength(n). Binary is economical even for malformed inputs;
on valid inputs with n>0, the explicit sequence already has at least n³ symbols. -/
def perfectEncoding : FinEncoding PerfectInput :=
  pairEncoding sequenceEncoding finEncodingNatBool

end ProteinFolding

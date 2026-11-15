import ProteinFolding.Common.Encodings
import ProteinFolding.Tetrahedral.Statement

/-!
# Encoding tetrahedral HP instances

Reuse the existing finite alphabet, tagged pair encoding and signed-binary
integer encoding. The word is explicit, and the threshold is binary, with
no coordinate, folding certificate or unary padding in the input.
-/

namespace ProteinFolding.Tetrahedral

open Computability

/-- Encoding length is |S| + 2 + bitlength(|minBonds|).
The alphabet and decoding conventions are shared with the existing projects. -/
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

end ProteinFolding.Tetrahedral

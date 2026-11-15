import ProteinFolding.Common.Encodings
import ProteinFolding.Square.Statement

/-! Both square-lattice input formats use the shared five-symbol alphabet:
H/P word, separator, sign, little-endian binary threshold magnitude.
Encoding length is |S| + 2 + bitlength(|threshold|), with bitlength(0) = 0.
No graph, fold, bound on coordinates, or unary padding is encoded. -/

namespace ProteinFolding.Square

open Computability

def hpEncoding : FinEncoding HPInstance :=
  let e := pairEncoding sequenceEncoding signedEncoding
  { Γ := e.Γ
    ΓFin := e.ΓFin
    encode := fun I => e.encode (I.sequence, I.minContacts)
    decode := fun w => (e.decode w).map (fun sm => ⟨sm.1, sm.2⟩)
    decode_encode := by
      intro I
      rw [e.decode_encode]
      cases I
      rfl }

def lossEncoding : FinEncoding LossInstance :=
  let e := pairEncoding sequenceEncoding signedEncoding
  { Γ := e.Γ
    ΓFin := e.ΓFin
    encode := fun I => e.encode (I.sequence, I.maxLosses)
    decode := fun w => (e.decode w).map (fun sm => ⟨sm.1, sm.2⟩)
    decode_encode := by
      intro I
      rw [e.decode_encode]
      cases I
      rfl }

end ProteinFolding.Square

import ProteinFolding.Common.TM2UnaryToBinary
import ProteinFolding.Common.TM2EncodingWords
import ProteinFolding.Common.TM2Constants
import ProteinFolding.Common.TM2ProductMap

/-! Actual conversion of an explicit unary natural to its nonnegative signed
binary integer encoding. The sign is one fixed false bit; the magnitude uses
the proved canonical unary-to-binary TM2, with no padding. -/

namespace ProteinFolding.TM2UnarySigned

open Computability Turing TM2CompositionPoly TM2ProductMap TM2PairProjections

noncomputable def nonnegativeComputable :
    TM2ComputableInPolyTime unaryFinEncodingNat signedEncoding (fun n : ℕ => (n : ℤ)) := by
  let hbits := compose TM2UnaryToBinary.unaryToBinaryComputable
    (TM2EncodingWords.encodeComputable finEncodingNatBool)
  let hsign := TM2Constants.constantComputable unaryFinEncodingNat (wordEncoding Bool) [false]
  let h := compose (pairComputable hsign hbits) (concatComputable Bool)
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun n => by
        simpa only [Function.comp_def, wordEncoding, signedEncoding, encodeSigned,
          finEncodingNatBool, List.singleton_append] using h.outputsFun n }

end ProteinFolding.TM2UnarySigned

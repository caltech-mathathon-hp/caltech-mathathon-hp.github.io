import ProteinFolding.Common.TM2PairProjections

/-! Viewing a typed encoded value as its word requires no new computation.
The machine is mathlib's actual identity machine on the original alphabet. -/

namespace ProteinFolding.TM2EncodingWords

open Computability Turing

noncomputable def encodeComputable {A : Type} (ea : FinEncoding A) :
    TM2ComputableInPolyTime ea (@wordEncoding ea.Γ ea.ΓFin) ea.encode := by
  let h := idComputableInPolyTime ea
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun x => by
        simpa only [wordEncoding, id_eq] using h.outputsFun x }

end ProteinFolding.TM2EncodingWords

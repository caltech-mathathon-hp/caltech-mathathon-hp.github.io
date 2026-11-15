import ProteinFolding.Tetrahedral.ReductionTM2PipelineFacts

/-! The fixed source-only reduction algorithm.
Its H-body endpoint data are the literal construction's terminal B, singleton
vertices/frame/separators/left filler/items AA, right filler AB, and three BB
ring units. Bulk records and every linker parity bit are computed internally.
Geometric correctness of these placements and the bulk scan is proved apart
from the unconditional finite-machine runtime witness. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Canonical

open Computability Turing

def frameColours : ColourFlags.Colours := (true, true)
def ringColours : List ColourFlags.Colours := List.replicate 3 (false, false)

noncomputable def reduction : Packing.Instance → HPInstance :=
  PrefixColours.reduction frameColours ringColours

/-- A closed actual polynomial-time TM2 from the unary source to HP inputs.
No bulk list, parity list, graph predicate or runtime premise is supplied. -/
noncomputable def computable : TM2ComputableInPolyTime Packing.instanceEncoding hpEncoding reduction :=
  PrefixColours.reductionComputable frameColours ringColours

noncomputable def flags (I : Packing.Instance) : List Bool :=
  ColourFlags.flags (false, PrefixColours.nonbulk frameColours ringColours I ++
    BulkScan.colours (Raw.side (I.bins, I.capacity)))

/-- The terminal B to first singleton A linker has the opposite-colour bit. -/
theorem flags_head (I : Packing.Instance) : (flags I)[0]? = some false := by
  change (ColourFlags.flags (false, (true, true) :: _))[0]? = some false
  rw [ColourFlags.flags_cons]
  rfl

theorem rejects_invalid (I : Packing.Instance) (h : Guard.sourceGuard I = false) :
    ¬ (reduction I).Accepts := Pipeline.rejects_invalid (I, PrefixColours.nonbulk frameColours ringColours I) h

theorem sequence_eq (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity) :
    (reduction I).sequence = (PackingSource.parameters I hw).prescribedReductionWord I.sizes
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))) (flags I) :=
  PrefixColours.reduction_sequence frameColours ringColours I hw ht

theorem threshold_eq (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity) :
    (reduction I).minBonds = 2 * (octahedralNumber (PackingSource.parameters I hw).side : ℤ) -
      2 * ((PackingSource.parameters I hw).side ^ 2 : ℕ) :=
  PrefixColours.reduction_threshold frameColours ringColours I hw ht

theorem flags_length (I : Packing.Instance) :
    (flags I).length = I.bins + I.sizes.length +
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))).length + 10 :=
  PrefixColours.flags_length frameColours ringColours (by simp [ringColours]) I

end ProteinFolding.Tetrahedral.ReductionTM2.Canonical

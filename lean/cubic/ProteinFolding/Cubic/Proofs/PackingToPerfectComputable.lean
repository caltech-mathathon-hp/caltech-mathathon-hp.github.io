import ProteinFolding.Cubic.Proofs.PackingWordComputableSource
import ProteinFolding.Cubic.Proofs.PackingGuardComputable
import ProteinFolding.Cubic.MainTheorem
import ProteinFolding.Common.TM2Conditional
import ProteinFolding.Common.ComplexityComposition

/-! The entire guarded packing-to-folding map as an actual polynomial-time
machine, including source checks, every frame/item word, and binary side output.

The geometric equivalence remains an explicit hypothesis in the interim Karp
and hardness transfer lemmas below. These are not proofs of the final theorem
from Cook--Levin alone. -/

namespace ProteinFolding.CubicPacking

open Computability Turing

/-- Actual runtime proof for the total reduction candidate. Invalid source
instances are sent to the original fixed no-instance `([],1)`. -/
noncomputable def packingToPerfectComputable :
    TM2ComputableInPolyTime Packing.instanceEncoding perfectEncoding packingToPerfect := by
  simpa only [packingToPerfect] using
    TM2Conditional.iteComputable Guard.sourceGuardComputable WordGenerator.unguardedInputComputable
      (TM2Constants.constantComputable Packing.instanceEncoding perfectEncoding ([], 1))

/-- Once geometric correctness is proved, the implemented map is a Karp
reduction. The hypothesis exposes exactly the remaining mathematical claim. -/
theorem packingToPerfect_karpReduces
    (hgeometry : ∀ I : Packing.Instance, Packing.ModifiedAccepts I ↔
      PerfectHPStringFold (packingToPerfect I).1 (packingToPerfect I).2) :
    KarpReduces Packing.instanceEncoding perfectEncoding Packing.ModifiedAccepts
      (fun I : PerfectInput => PerfectHPStringFold I.1 I.2) :=
  ⟨packingToPerfect, ⟨packingToPerfectComputable⟩, hgeometry⟩

theorem perfectHPStringFold_NPHard_of_modified_packing
    (hpacking : Packing.ModifiedBinPackingUnaryNPHard)
    (hgeometry : ∀ I : Packing.Instance, Packing.ModifiedAccepts I ↔
      PerfectHPStringFold (packingToPerfect I).1 (packingToPerfect I).2) :
    PerfectHPStringFoldNPHard :=
  npHard_of_karpReduces hpacking (packingToPerfect_karpReduces hgeometry)

end ProteinFolding.CubicPacking

import ProteinFolding.Cubic.Proofs.PackingFrameCompleteness
import ProteinFolding.Cubic.Proofs.PackingReductionSoundness
import ProteinFolding.Cubic.Proofs.PackingToPerfectComputable

/-! Correctness and the actual Karp reduction for every raw unary modified
packing input. The constructive and forcing geometric directions are both
proved; no geometric correctness hypothesis remains. -/

namespace ProteinFolding.CubicPacking

theorem packingToPerfect_complete (I : Packing.Instance) (hI : Packing.ModifiedAccepts I) :
    PerfectHPStringFold (packingToPerfect I).1 (packingToPerfect I).2 := by
  obtain ⟨hg, parts, hp⟩ := (modified_iff_guard_normalized I).mp hI
  obtain ⟨hw, _, _⟩ := (sourceGuard_spec I).mp hg
  rw [packingToPerfect_of_guard I hg]
  exact frameWord_complete (sourceBins I) (sourceQ I) (sourceWidths I)
    (sourceBins_two_le I hw) (sourceQ_gt_bins I hw) (sourceWidths_positive I hw)
    (sourceWidths_even I) parts hp

/-- The implemented total map preserves both yes- and no-instances. -/
theorem packingToPerfect_correct (I : Packing.Instance) :
    Packing.ModifiedAccepts I ↔
      PerfectHPStringFold (packingToPerfect I).1 (packingToPerfect I).2 :=
  ⟨packingToPerfect_complete I, packingToPerfect_sound I⟩

/-- The actual polynomial-time many-one reduction, with both semantic
directions proved on all raw inputs and no additional assumptions. -/
theorem packingToPerfect_karp :
    KarpReduces Packing.instanceEncoding perfectEncoding Packing.ModifiedAccepts
      (fun I : PerfectInput => PerfectHPStringFold I.1 I.2) :=
  packingToPerfect_karpReduces packingToPerfect_correct

end ProteinFolding.CubicPacking

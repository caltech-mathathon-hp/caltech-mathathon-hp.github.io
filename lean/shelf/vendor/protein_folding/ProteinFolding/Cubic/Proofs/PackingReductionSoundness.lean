import ProteinFolding.Cubic.Proofs.PackingFrameSoundness
import ProteinFolding.Cubic.Proofs.PackingWordSource

/-! Soundness of the actual total unary-packing reduction. The guard retains
all modified-packing side conditions; invalid raw source inputs are rejected. -/

namespace ProteinFolding.CubicPacking

/-- Every accepted output of the total candidate reduction comes from an
accepted MODIFIED BIN PACKING input. No promise on the raw source is needed. -/
theorem packingToPerfect_sound (I : Packing.Instance) :
    PerfectHPStringFold (packingToPerfect I).1 (packingToPerfect I).2 →
      Packing.ModifiedAccepts I := by
  intro hfold
  cases hg : sourceGuard I with
  | false => exact False.elim (packingToPerfect_rejects_invalid I hg hfold)
  | true =>
    obtain ⟨hw, _, ht⟩ := (sourceGuard_spec I).mp hg
    apply (modified_iff_guard_normalized I).mpr
    refine ⟨hg, ?_⟩
    have hsource : PerfectHPStringFold (sourceWord I) (sourceSide I) := by
      simpa only [packingToPerfect_of_guard I hg] using hfold
    exact CubicPackingGeometry.frameWord_sound (sourceBins I) (sourceQ I) (sourceWidths I)
      (sourceBins_two_le I hw) (sourceQ_gt_bins I hw) (sourceWidths_positive I hw)
      (sourceWidths_sum I ht) hsource

end ProteinFolding.CubicPacking

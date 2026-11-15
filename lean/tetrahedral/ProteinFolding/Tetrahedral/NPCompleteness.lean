import ProteinFolding.Tetrahedral.NearFieldCanonicalCompleteness
import ProteinFolding.Tetrahedral.ReductionTM2CanonicalBackward
import ProteinFolding.Tetrahedral.ReductionNPComposition

/-! Final composition of the concrete reduction's two directions for the
frozen NP-completeness target. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Canonical

theorem reduction_complete (I : Packing.Instance) (hI : PackingSource.Accepts I) :
    (reduction I).Accepts :=
  NearField.canonical_accepts_of_packing I hI (source_bulk_acyclic I hI.1)

theorem reduction_correct (I : Packing.Instance) :
    (reduction I).Accepts ↔ PackingSource.Accepts I :=
  ⟨reduction_sound I, reduction_complete I⟩

end ProteinFolding.Tetrahedral.ReductionTM2.Canonical

namespace ProteinFolding.Tetrahedral

theorem tetrahedral_hp_npComplete : HPStringFoldNPComplete :=
  ReductionTM2.Canonical.npComplete_of_reduction_correct ReductionTM2.Canonical.reduction_correct

#print axioms tetrahedral_hp_npComplete

end ProteinFolding.Tetrahedral

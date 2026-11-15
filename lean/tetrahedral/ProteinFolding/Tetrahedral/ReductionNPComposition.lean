import ProteinFolding.Tetrahedral.MainTheorem
import ProteinFolding.Tetrahedral.PackingSource
import ProteinFolding.Tetrahedral.ReductionTM2Canonical
import ProteinFolding.Tetrahedral.CertificatesTM2Correctness
import ProteinFolding.Common.ComplexityComposition

/-! The final complexity composition, with correctness of the actual fixed
reduction explicit. This helper does not supply the remaining geometric
correctness proof or prove the unconditional target. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Canonical

theorem reduction_karp_of_correct
    (hcorrect : ∀ I : Packing.Instance, (reduction I).Accepts ↔ PackingSource.Accepts I) :
    KarpReduces PackingSource.instanceEncoding hpEncoding PackingSource.Accepts HPInstance.Accepts :=
  ⟨reduction, ⟨computable⟩, fun I => (hcorrect I).symm⟩

theorem npComplete_of_reduction_correct
    (hcorrect : ∀ I : Packing.Instance, (reduction I).Accepts ↔ PackingSource.Accepts I) :
    HPStringFoldNPComplete := by
  change NPComplete hpEncoding HPInstance.Accepts
  exact ⟨hp_inNP, npHard_of_karpReduces PackingSource.unary_exact_capacity_npHard
    (reduction_karp_of_correct hcorrect)⟩

end ProteinFolding.Tetrahedral.ReductionTM2.Canonical

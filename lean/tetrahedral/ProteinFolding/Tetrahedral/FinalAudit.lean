import ProteinFolding.Tetrahedral.NPCompleteness

/-! Final kernel gate for the unchanged problem statement. This module must
be compiled after its concrete dependencies; its presence is not a proof
receipt. VerifyFinal.ps1 checks the resulting artifacts and audit log. -/

namespace ProteinFolding.Tetrahedral

example : HPStringFoldNPComplete := tetrahedral_hp_npComplete

#check tetrahedral_hp_npComplete
#print axioms tetrahedral_hp_npComplete
#print axioms ReductionTM2.Canonical.reduction_correct
#print axioms ReductionTM2.Canonical.source_bulk_acyclic
#print axioms bulkFiniteGraph_acyclic

end ProteinFolding.Tetrahedral

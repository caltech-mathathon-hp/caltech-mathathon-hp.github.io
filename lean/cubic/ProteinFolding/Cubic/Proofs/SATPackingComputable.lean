import ProteinFolding.Common.SAT.CNFMatchingReduction
import ProteinFolding.Cubic.Proofs.MatchingPackingComputable

/-! Strong unary source hardness with actual polynomial-time machines.

The direct CNF occurrence gadget uses block-labelled Boolean vertices, and the
numerical packing map emits dummy items in vertex order. Both alternative
witnesses have proved semantics, and preserve all earlier problem and reduction
definitions. The only hypothesis of the hardness theorem is the explicit
frozen Cook--Levin statement. No geometric folding claim is assumed here. -/

namespace ProteinFolding.SATPacking

open Computability Turing SAT ThreeDimensionalMatching SourceQueries

/-- The implemented source transformation, distinct from the earlier
mathematical witness whose item and vertex orders remain unchanged. -/
def cnfToSortedModified (φ : CNF) : Packing.Instance :=
  MatchingPacking.sortedToModified (cnfToBlockMatching φ)

/-- Actual polynomial-time composition of the finite occurrence-gadget and
bounded numerical-item generators, measured in their stated encodings. -/
noncomputable def cnfToSortedModifiedComputable :
    TM2ComputableInPolyTime cnfEncoding Packing.instanceEncoding cnfToSortedModified :=
  TM2CompositionPoly.compose (g := MatchingPacking.sortedToModified)
    cnfToBlockMatchingComputable MatchingPacking.sortedToModifiedComputable

theorem cnfToSortedModified_correct (φ : CNF) :
    Packing.ModifiedAccepts (cnfToSortedModified φ) ↔ Satisfiable φ :=
  (MatchingPacking.sortedToModified_correct (cnfToBlockMatching φ)).symm.trans
    (cnfToBlockMatching_correct φ)

/-- A complete Karp reduction from the unchanged binary-variable CNF language
to positive-even, exact, unary modified packing. -/
theorem cnfToSortedModified_karp :
    KarpReduces cnfEncoding Packing.instanceEncoding Satisfiable Packing.ModifiedAccepts :=
  ⟨cnfToSortedModified, ⟨cnfToSortedModifiedComputable⟩,
    fun φ => (cnfToSortedModified_correct φ).symm⟩

/-- The strong unary packing source is NP-hard assuming only Cook--Levin.
Every reduction and runtime witness used after that source assumption is
proved, rather than supplied as an additional hypothesis. -/
theorem modifiedBinPackingUnary_NPHard (hCL : CookLevin) :
    Packing.ModifiedBinPackingUnaryNPHard :=
  npHard_of_cookLevin_reduction hCL cnfToSortedModified_karp

end ProteinFolding.SATPacking

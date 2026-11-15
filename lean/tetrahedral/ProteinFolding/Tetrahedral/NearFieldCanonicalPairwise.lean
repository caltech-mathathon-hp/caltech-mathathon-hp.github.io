import ProteinFolding.Tetrahedral.NearFieldCanonicalFamilyCross
import ProteinFolding.Tetrahedral.NearFieldCanonicalRemainingCrossProof

/-! The complete actual unit family is disjoint. The local cross-family
relations are supplied by geometric theorems, not caller certificates. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem canonicalUnitPieces_pairwise (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic) :
    (canonicalUnitPieces p items d ha).Pairwise WordsDisjoint :=
  canonicalUnitPieces_pairwise_of_remaining p items d ha (canonicalRemainingCross p)

theorem canonicalUnitAt_disjoint (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (i j : Fin ((p.reductionUnitBodies items (ReductionTM2.BulkScan.lengths p.side)).length + 1))
    (hne : i ≠ j) : WordsDisjoint (canonicalUnitAt p items d ha i) (canonicalUnitAt p items d ha j) :=
  canonicalUnitAt_disjoint_of_pairwise p items d ha (canonicalUnitPieces_pairwise p items d ha) i j hne

end ProteinFolding.Tetrahedral.NearField

import ProteinFolding.Tetrahedral.BulkCanonicalCover
import ProteinFolding.Tetrahedral.ReductionTM2CanonicalCounts
import ProteinFolding.Tetrahedral.ReductionTM2BulkRuntimeFamily
import ProteinFolding.Tetrahedral.ReductionTM2BulkCappedFamily
import ProteinFolding.Tetrahedral.ReductionTM2BulkEndpointFacts

/-! Source-only word facts after discharging the canonical graph's actual
acyclicity theorem. No graph certificate is an input to this API. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Canonical

set_option maxHeartbeats 2000000

theorem source_bulk_acyclic (I : Packing.Instance) (hw : Packing.WellFormed I) :
    (bulkFiniteGraph (PackingSource.parameters I hw).side).IsAcyclic :=
  bulkFiniteGraph_acyclic _ (by have h := (PackingSource.parameters I hw).side_ge; omega)

theorem source_bulk_lengths_ge_three (I : Packing.Instance) (hw : Packing.WellFormed I)
    (n : ℕ) (hn : n ∈ BulkScan.lengths (Raw.side (I.bins, I.capacity))) : 3 ≤ n :=
  bulk_lengths_ge_three I hw (source_bulk_acyclic I hw) n hn

theorem source_bulk_mass (I : Packing.Instance) (hw : Packing.WellFormed I) :
    24 * (PackingSource.parameters I hw).side + (BulkScan.lengths (Raw.side (I.bins, I.capacity))).sum =
      octahedralNumber (PackingSource.parameters I hw).side + 42 :=
  bulk_mass I hw (source_bulk_acyclic I hw)

theorem source_hydrophobicCount_eq (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity) :
    hydrophobicCount (reduction I).sequence = octahedralNumber (PackingSource.parameters I hw).side :=
  hydrophobicCount_eq I hw ht (source_bulk_acyclic I hw)

theorem source_phpIndices_card (I : Packing.Instance) (hw : Packing.WellFormed I)
    (ht : I.sizes.sum = I.bins * I.capacity) : (phpIndices (reduction I).sequence).card = 6 :=
  phpIndices_card I hw ht (source_bulk_acyclic I hw)

noncomputable def source_bulkFold (I : Packing.Instance) (hw : Packing.WellFormed I)
    (j : Fin (BulkScan.lengths (Raw.side (I.bins, I.capacity))).length) :
    Fold tetrahedralLattice ((BulkScan.lengths (Raw.side (I.bins, I.capacity))).get j) :=
  BulkScan.runtimeFold (PackingSource.parameters I hw).side
    (by have h := (PackingSource.parameters I hw).side_ge; omega) (source_bulk_acyclic I hw) j

noncomputable def source_cappedBulkPieces (I : Packing.Instance) (hw : Packing.WellFormed I) :
    List NearField.PositionedWord :=
  BulkScan.cappedRuntimePieces (PackingSource.parameters I hw).side
    (by have h := (PackingSource.parameters I hw).side_ge; omega) (source_bulk_acyclic I hw)

theorem source_cappedBulkPieces_words (I : Packing.Instance) (hw : Packing.WellFormed I) :
    (source_cappedBulkPieces I hw).map NearField.PositionedWord.word =
      (BulkScan.lengths (Raw.side (I.bins, I.capacity))).map (fun n => capWord (List.replicate n Residue.H)) :=
  BulkScan.cappedRuntimePieces_words (PackingSource.parameters I hw).side
    (by have h := (PackingSource.parameters I hw).side_ge; omega) (source_bulk_acyclic I hw)

theorem source_cappedBulkPieces_pairwise (I : Packing.Instance) (hw : Packing.WellFormed I) :
    (source_cappedBulkPieces I hw).Pairwise (fun a b => Disjoint (foldSites a.fold) (foldSites b.fold)) :=
  BulkScan.cappedRuntimePieces_pairwise (PackingSource.parameters I hw).side
    (by have h := (PackingSource.parameters I hw).side_ge; omega) (source_bulk_acyclic I hw)

theorem source_cappedBulkPieces_hSupport (I : Packing.Instance) (hw : Packing.WellFormed I) :
    NearField.pieceHsupport (source_cappedBulkPieces I hw) = bulkInterior (PackingSource.parameters I hw).side :=
  BulkScan.cappedRuntimePieces_hSupport (PackingSource.parameters I hw).side
    (by have h := (PackingSource.parameters I hw).side_ge; omega) (source_bulk_acyclic I hw)

noncomputable def source_bulkColumns (I : Packing.Instance) (hw : Packing.WellFormed I)
    (j : Fin (BulkScan.lengths (Raw.side (I.bins, I.capacity))).length) (e : Bool) :
    DanglingColumn (PackingSource.parameters I hw).side :=
  BulkScan.runtimeColumns (PackingSource.parameters I hw).side
    (by have h := (PackingSource.parameters I hw).side_ge; omega) (source_bulk_acyclic I hw) j e

theorem source_bulkColumns_data (I : Packing.Instance) (hw : Packing.WellFormed I)
    (j : Fin (BulkScan.lengths (Raw.side (I.bins, I.capacity))).length) (e : Bool) :
    (source_bulkColumns I hw j e).owner ∈ bulkInterior (PackingSource.parameters I hw).side ∧
      (bulkCoverNeighbours (PackingSource.parameters I hw).side (source_bulkColumns I hw j e).owner).card = 1 :=
  BulkScan.runtimeColumns_data (PackingSource.parameters I hw).side
    (by have h := (PackingSource.parameters I hw).side_ge; omega) (source_bulk_acyclic I hw) j e

end ProteinFolding.Tetrahedral.ReductionTM2.Canonical
